open Ast
open LibCore
module Loc = LibCore.Loc

let tf location x = Ty.Fixed.fix x location

module Make(B:Ident.Bindings)(BTyVar:Ident.Bindings)(BTyNamed:Ident.Bindings)(BT:Ident.FreshableBindings)(F:Ident.Fields) :
sig
  type 'a ty = ('a, F.t, BT.t, BTyNamed.t) Ty.Fixed.t

  type acc
  val passe : (acc,
               (Loc.t, Loc.t,
                BTyVar.t, BTyNamed.t,
                F.t, B.t) Ast.TopLvl.decl,
               (Loc.t * Loc.t ty, Loc.t,
                BT.t, BTyNamed.t,
                F.t, B.t) Ast.TopLvl.decl,
               'passfinal, 'passfinal) LibCore.Passes.t
  val debug : Format.formatter -> (Loc.t * Loc.t ty, Loc.t,
                BT.t, BTyNamed.t,
                F.t, B.t) Ast.TopLvl.decl -> unit

  val ppenv : Format.formatter -> acc -> unit

end = struct
  open Expr
  type 'a ty = ('a, F.t, BT.t, BTyNamed.t) Ty.Fixed.t

  type scheme = {
      vars : BT.t list;
      body : Loc.t ty;
    }
  type env = {
      fresh : BT.t;
      bindings : scheme B.Map.t;
      tybindings : Loc.t ty BT.Map.t;
      ty_named : (BT.t list * Loc.t ty) BTyNamed.Map.t;
      fieldmap : BTyNamed.t F.Map.t
    }
  type acc = env

  let ppty f ty = Ty.Fixed.pp F.pp BT.pp BTyNamed.pp f ty

  let ftv_ty ty = Ty.Fixed.Deep.foldfg Aux.passacc (BT.Set.add) Aux.passacc ty BT.Set.empty

  (* Applique la substitution [tybindings] récursivement : une chaîne
     'b := 'a, 'a := int doit donner int pour 'b, pas 'a. *)
  let rec resolve env ty =
    Ty.Fixed.Deep.map
      (function
       | Ty.Var binding as v ->
          begin match BT.Map.find_opt binding env.tybindings with
          | None -> v
          | Some s -> Ty.Fixed.unfix (resolve env s)
          end
       | x -> x)
      ty

  (* Variables libres de l'environnement : celles des corps de schémas (une fois la
     substitution appliquée), moins les variables quantifiées. *)
  let ftv_env env =
    B.Map.fold (fun _binding scheme acc ->
        BT.Set.union acc (BT.Set.diff (ftv_ty (resolve env scheme.body)) (BT.Set.of_list scheme.vars)))
      env.bindings BT.Set.empty

  let generalize env ty =
    let ty = resolve env ty in
    let vars = BT.Set.diff (ftv_ty ty) (ftv_env env) in
    {vars=BT.Set.to_list vars; body=ty}

  let pp_scheme f scheme = Format.fprintf f "@[∀ %a . %a@]"
                         (Pp.list (Pp.sep " ") BT.pp) scheme.vars
                         ppty scheme.body

  let ppenv f env =
    Format.fprintf f "@[{fresh:%a;@\nbindings:%a;@\ntybindings:@[%a@]@\n}@]"
    BT.pp env.fresh
    (Pp.assoc B.pp pp_scheme) (B.Map.to_list env.bindings)
    (Pp.assoc BT.pp ppty) (BT.Map.to_list env.tybindings)

  let empty = { fresh = BT.init; bindings = B.Map.empty; tybindings = BT.Map.empty; ty_named=BTyNamed.Map.empty; fieldmap = F.Map.empty; }
  let fresh location env v =
    let typevar =  Ty.Var env.fresh |> tf location in
    {env with
      fresh=BT.next env.fresh;
      bindings = B.Map.add v {vars= []; body=typevar } env.bindings}, typevar
  let fresh'var env =
    {env with fresh=BT.next env.fresh}, env.fresh
  let fresh' location env =
    let env, tv = fresh'var env in
    let typevar =  Ty.Var tv |> tf location in
    env, typevar

  let instantiate (env:env) tyvars (ty : Loc.t ty) =
    let (env, assocvars), nvars = List.fold_left_map (fun (env, assocvars) var ->
                             let env, var' = fresh'var env in
                             (env, BT.Map.add var var' assocvars), var') (env, BT.Map.empty) tyvars in
    env, nvars, Ty.Fixed.Deep.mapfg Fun.id (fun var -> Option.value (BT.Map.find_opt var assocvars) ~default:var) Fun.id ty

  let insert_mono env binding ty =
    { env with bindings = B.Map.add binding {vars=[]; body=ty} env.bindings}

  let insert_poly env binding ty =
    (* la liaison elle-même (monomorphe pendant un let rec) ne doit pas bloquer la généralisation *)
    let scheme = generalize { env with bindings = B.Map.remove binding env.bindings } ty in
    { env with bindings = B.Map.add binding scheme env.bindings}

  let find_binding env binding =
    let sch = B.Map.find binding env.bindings in
    let env, _nvars, ty = instantiate env sch.vars sch.body in
    env, ty

  let sort_sum li = List.sort (fun (a, _) (b, _) -> F.compare a b) li

  let occurs_check tyvar ty =
    Ty.Fixed.Deep.exists (function
        | Ty.Var v when BT.compare v tyvar == 0 -> true
        | _ -> false) ty
  let occurs_check v t location =
    let t = Ty.Fixed.fix t location in
    if occurs_check v t then Pp.failwith "type rec : %a occurs in %a" BT.pp v ppty t

  (* TODO utiliser le zip *)
  let rec unify location env t1 t2 =
    (* Format.printf "env:%a@\nunify @[<v>-%a@\n-%a@]@\n" ppenv env ppty (tf location t1) ppty (tf location t2); *)
    match t1, t2 with
    | Ty.Named (li1, d1), Ty.Named (li2, d2) when BTyNamed.equal d1 d2 -> (* TODO instancier sauf si c'est pas type somme *)
       let env, li = match Aux.zip_opt li1 li2 with
           | None -> Pp.failwith "%a vs %a" ppty (tf location t1) ppty (tf location t2)
           | Some li -> List.fold_left_map (fun env (t1, t2) -> unify location env (Ty.Fixed.unfix t1) (Ty.Fixed.unfix t2)) env li in
       let li = List.map (tf location) li
       in env, Ty.Named(li, d1)
    | Ty.Var v1, Ty.Var v2 when BT.equal v1 v2 ->
       env, t1
    | Ty.Var v, t | t, Ty.Var v ->
       begin match BT.Map.find_opt v env.tybindings with
       | Some tv -> unify location env (Ty.Fixed.unfix tv) t
       | None ->
          let t = Ty.Fixed.unfix (resolve env (tf location t)) in
          match t with
          | Ty.Var w when BT.equal v w -> env, t
          | _ ->
             occurs_check v t location;
             let env = {env with tybindings = BT.Map.add v (tf location t) env.tybindings } in
             env, t
       end
    | Ty.Integer, Ty.Integer -> env, Ty.Integer
    | Ty.Char, Ty.Char -> env, Ty.Char
    | Ty.Bool, Ty.Bool -> env, Ty.Bool
    | Ty.Sum li1, Ty.Sum li2 ->
       let li1 = sort_sum li1 in
       let li2 = sort_sum li2 in
       let rec merge env acc li1 li2 = match li1, li2 with
         | [], li | li, [] -> env, List.append (List.rev acc) li
         | ((name1, ty1)::tl1), ((name2, ty2)::tl2) ->
            match F.compare name1 name2 with
              | -1 -> merge env ((name1, ty1)::acc) li2 tl1
              | 1 -> merge env ((name2, ty2)::acc) li1 tl2
              | 0 -> let env, ty = unify location env (Ty.Fixed.unfix ty1) (Ty.Fixed.unfix ty2) in
                     merge env ((name1, (tf location ty))::acc) tl1 tl2
              | _ -> assert false
       in let env, li = merge env [] li1 li2
          in env, Ty.Sum li
    | Ty.Tuple li1, Ty.Tuple li2 ->
       begin match Aux.zip_opt li1 li2 with
       | None -> assert false (* TODO erreur de type *)
       | Some li ->
          let env, li = List.fold_left_map (fun env (t1, t2) -> unify location env (Ty.Fixed.unfix t1) (Ty.Fixed.unfix t2)) env li in
          env, Ty.Tuple (List.map (tf location) li)
       end
    | Ty.Arrow (f1, t1), Ty.Arrow (f2, t2) ->
       let env, f1 = unify location env (Ty.Fixed.unfix f1) (Ty.Fixed.unfix f2) in
       let env, t1 = unify location env (Ty.Fixed.unfix t1) (Ty.Fixed.unfix t2) in
       env, Ty.Arrow(tf location f1, tf location t1)
    | _ ->
       Pp.failwith "@\nCannot unify @[<v>%a@\nvs :@\n%a@]@\n(location %a)@\n"
         ppty (tf location t1) ppty (tf location t2)
         Loc.pp location

  let canonique_pattern location env t =
    Ty.Fixed.Deep.foldmap (fun env ty ->
        match ty with
        | Ty.Sum (((name, _)::_) as li) ->
           begin match F.Map.find_opt name env.fieldmap with
           | None -> Pp.failwith "unknown constructor %a" F.pp name
           | Some tyname ->
              let (tyvars, def) = BTyNamed.Map.find tyname env.ty_named in
              let env, tyvars, def = instantiate env tyvars def in
              let tyvars = List.map (fun v -> tf location (Ty.Var v)) tyvars in
              let def_assoc = match Ty.Fixed.unfix def with
                | Ty.Sum li2 -> li2
                | _ -> assert false
              in
              let env = List.fold_left (fun env (name, ty) ->
                            let ty2 = List.assoc name def_assoc in
                            let env, _ = unify location env  (Ty.Fixed.unfix ty) (Ty.Fixed.unfix ty2) in
                            env
                          ) env li in
              env, Ty.Named(tyvars, tyname)
           end
        | _ -> env, ty
      ) t env

  let merge_patterns location env t1 t2 = unify location env t1 t2 (* TODO *)

  let merge_patterns location env = function
    | hd::tl -> List.fold_left (fun (env, t1) t2 -> merge_patterns location env t1 t2) (env, hd) tl
    | [] -> assert false

  let merge_patterns location env li =
    let env, t = merge_patterns location env (List.map Ty.Fixed.unfix li) in
    let t = tf location t in
    let env, t = canonique_pattern location env t in
    env, t

  let unify location env ta tb =
    let env, t = unify location env (Ty.Fixed.unfix ta) (Ty.Fixed.unfix tb)
    in env, tf location t

  let ty_of_pat pat = snd (Fixed.decoration_u pat)
  let ty_of_expr e = snd (Fixed.decoration e)
  let location_of_expr e = fst (Fixed.decoration e)

  let ty_pattern location pat env =
    match pat with
    | Pattern.Var v -> let env, ty = fresh location env v in env, (location, ty)
    | Pattern.Tuple li -> let types = List.map ty_of_pat li
                          in env, (location, Ty.Tuple types |> tf location)
    | Pattern.Construct (a, p) ->
       env, (location, Ty.Sum [a, ty_of_pat p] |> tf location)

  let ty_pattern pat env = Fixed.Deep.decorate_foldmap_u ty_pattern pat env

  let apply_ty = resolve

  let ty_expr location tra expr env =
    let ef x = location, tf location x in
    match expr with
    | Fixable.Integer i -> env, Ty.Integer |> ef, Fixable.Integer i
    | Fixable.Char c -> env, Ty.Char |> ef, Fixable.Char c
    | Fixable.Bool b -> env, Ty.Bool |> ef, Fixable.Bool b
    | Fixable.Tuple li ->
       let env, li = List.fold_left_map tra env li in
       let types = List.map ty_of_expr li in
       env, Ty.Tuple types |> ef, Fixable.Tuple li
    | Fixable.Construct (a, e) ->
       let env, e = tra env e in
       let te = ty_of_expr e in
       begin match F.Map.find_opt a env.fieldmap with
       | None -> Pp.failwith "unknown constructor %a" F.pp a
       | Some s -> let tyvars, ty = BTyNamed.Map.find s env.ty_named in
                   let env, nvars, tout' = instantiate env tyvars ty in
                   let te' = match Ty.Fixed.unfix tout' with
                     | Ty.Sum li -> List.assoc a li
                     | _ -> assert false
                   in
                   let env, _te' = unify location env te te' in
                   let nvars = List.map (fun v ->
                                   match BT.Map.find_opt v env.tybindings with
                                   | Some s -> s
                                   | None -> tf location (Ty.Var v)) nvars in
                   env, ef (Ty.Named(nvars, s)), Fixable.Construct (a, e)
       end
    | Fixable.Lambda (c, a) ->
       let outer = env.bindings in
       let env, tc = fresh location env c in
       let env, a = tra env a in
       let ta = ty_of_expr a in
       let env = { env with bindings = outer } in (* c sort de la portée *)
       env, Ty.Arrow (tc, ta)|> ef, Fixable.Lambda (c, a)
    | Fixable.BinOp (a, op, b) ->
       let t0, t_out = match op with
         | Add | Sub | Mul | Div -> Some(tf location Ty.Integer), Ty.Integer (* int -> int -> int *)
         | Lt | Le | Gt | Ge ->  Some(tf location Ty.Integer), Ty.Bool (* int -> int -> bool *)
         | And | Or -> Some (tf location Ty.Bool), Ty.Bool (* bool -> bool -> bool *)
         | Eq | Neq -> None, Ty.Bool (* 'a -> 'a -> bool *)
       in
       let env, a = tra env a in
       let env, b = tra env b in
       let ta = ty_of_expr a in
       let tb = ty_of_expr b in
       let env, t = unify location env ta tb in
       let env, _t = match t0 with
         | None -> env, t
         | Some t0 -> unify location env t0 t in
       env, (location, tf location  t_out), Fixable.BinOp (a, op, b)
    | Fixable.UnOp (op, a) ->
       let t = match op with
         | Neg -> Ty.Integer
         | Not -> Ty.Bool in
       let env, a = tra env a in
       let ta = ty_of_expr a in
       let env, t = unify location env ta (tf location t) in
       env, (location, t), Fixable.UnOp(op, a)
    | Fixable.Apply (a, b) ->
       let env, a = tra env a in
       let ta = ty_of_expr a in
       let env, b = tra env b in
       let tb = ty_of_expr b in
       let env, tout = fresh' location env in
       let t = Ty.Arrow (tb, tout)|> tf location in
       let env, _t = unify location env t ta in
       env, (location, tout), Fixable.Apply (a, b)
    | Fixable.Record li ->
       let env, li = List.fold_left_map (fun env (a, b) ->
                         let env, b = tra env b in
                         env, (a, b)) env li in
       let t = Ty.Record (List.map (fun (a, b) -> a, ty_of_expr b) li) in
       env, ef t, Record (li)
    | Fixable.PatternMatch (a, li) ->
       let env, a = tra env a in
       let ta = ty_of_expr a in
       let env, li = List.fold_left_map (fun env (pat, e) ->
                         let outer = env.bindings in
                         let env, p = ty_pattern pat env in
                         let env, e = tra env e in
                         { env with bindings = outer }, (p, e)) env li in
       let patterns, expressions = List.split li in
       let env, ty_sum = merge_patterns location env (List.map ty_of_pat patterns) in
       let env, tout = match expressions with
         | [] -> assert false
         | hd::tl ->
            let tout = ty_of_expr hd in
            List.fold_left (fun (env, tout) e -> unify location env tout (ty_of_expr e)) (env, tout) tl in
       let env, _ty_sum = unify location env ty_sum ta in
       env, (location, tout), Fixable.PatternMatch (a, li)
    | Fixable.AccessRecord (e, b) ->
       let env, e = tra env e in
       let te = ty_of_expr e in
       let env, tfield = fresh' location env in
       let t = Ty.Record [b, tfield] |> tf location in
       let env, _t = unify location env t te in
       env, (location, tfield), Fixable.AccessRecord (e, b)
    | Fixable.IfThenElse (a, b, c) ->
       let env, a = tra env a in
       let env, b = tra env b in
       let env, c = tra env c in
       let ta = ty_of_expr a in
       let tb = ty_of_expr b in
       let tc = ty_of_expr c in
       let env, tb = unify location env tb tc in
       let env, _ta = unify location env ta (tf location Ty.Bool) in
       env, (location, tb), Fixable.IfThenElse(a, b, c)
    | Fixable.LetIn (c, a, b) ->
       let outer = env.bindings in
       let env, a = tra env a in
       let ta = ty_of_expr a in
       let env = insert_poly env c ta in
       let env, b = tra env b in
       let tb = ty_of_expr b in
       let env = { env with bindings = outer } in
       env, (location, tb), Fixable.LetIn(c, a, b)
    | Fixable.LetRecIn(c, a, b) ->
       let outer = env.bindings in
       let env, tc = fresh' location env in
       let env = insert_mono env c tc in
       let env, a = tra env a in
       let ta = ty_of_expr a in
       let env, _ta = unify location env ta tc in
       let env = insert_poly env c tc in (* c est polymorphe dans le corps *)
       let env, b = tra env b in
       let tb = ty_of_expr b in
       let env = { env with bindings = outer } in
       env, (location, tb), Fixable.LetRecIn(c, a, b)
    | Fixable.Var c ->
       let env, tc = find_binding env c in
       env, (location, tc), Fixable.Var c

  let ty_expr fin _gin _tra (env:env) location e = ty_expr location (fun a b -> fin b a) e env

  let process e env =
    let env, e = Expr.Fixed.Traverse.decorate_foldmap ty_expr (fun _ -> assert false)
                   Aux.didacc Aux.didacc e env in
    (* Format.printf "env=%a@\n" ppenv env; *)
    let app (loc, ty) _ =
      let ty = apply_ty env ty in
      loc, ty in
    env, Expr.Fixed.Deep.decorate app app e

  let process env toplvl =
    let open Ast.TopLvl in
    match toplvl with
    | TypeDecl (tylist, binding, ty) -> (* TODO checker la forme du type, lui interdire des typesum pas au premier niveau *)
       let env = Ty.Fixed.Deep.foldfg (fun field env ->
                     {env with fieldmap = F.Map.add field binding env.fieldmap}
                   ) Aux.passacc Aux.passacc ty env in
       let (map, _), tylist' = List.fold_left_map (fun (map, fresh) ty ->
                                   let map = BTyVar.Map.add ty fresh map in
                                   (map, BT.next fresh), fresh
                            ) (BTyVar.Map.empty, BT.init) tylist in
       let ty = Ty.Fixed.Deep.mapfg Fun.id (fun v -> BTyVar.Map.find v map) Fun.id ty in (* TODO erreur sur les types non bindés *)
       let env = { env with ty_named = BTyNamed.Map.add binding (tylist', ty) env.ty_named }
       in env, TypeDecl (tylist', binding, ty)
    | Let (binding, expr) ->
       let env, expr = process expr env in
       let env = insert_poly env binding (ty_of_expr expr) in
       env, Let(binding, expr)
    | LetRec (binding, expr) ->
       let location = Expr.Fixed.decoration expr in
       let env, tc = fresh' location env in
       let env = insert_mono env binding tc in
       let env, expr = process expr env in
       let loc = location_of_expr expr in
       let env, _tc = unify loc env tc (ty_of_expr expr) in
       let tc = apply_ty env tc in
       let expr = Expr.Fixed.fix (Expr.Fixed.unfix expr) (loc, tc) in
       let env = insert_poly env binding (ty_of_expr expr) in
       env, LetRec(binding, expr)
    | External (binding, ty, s) ->
       let map = BTyVar.Map.empty in (* TODO peut-être un forall ? *)
       let ty = Ty.Fixed.Deep.mapfg Fun.id (fun v -> BTyVar.Map.find v map) Fun.id ty in
       let env = insert_poly env binding ty in
       env, External (binding, ty, s)
  let passe = { LibCore.Passes.init = empty; process = process ; final = LibCore.Passes.nofinal;}
  let debug f = function
    | Ast.TopLvl.Let (binding, expr)
    | Ast.TopLvl.LetRec (binding, expr) ->
       let _, ty = Expr.Fixed.decoration expr in
       Format.fprintf f "val %a : @[<v>%a@]@\n"
       B.pp binding ppty ty
    | _ -> ()
end
