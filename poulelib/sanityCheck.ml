(* Bonne formation (notes de conception d'origine, implémentées ci-dessous)
À vérifier :

pas de doublons de noms globaux
arité correcte des types paramétrés
constructeurs référencent des types existants
signatures de fonctions bien formées
signatures de prédicats bien formées
chaque variable de type utilisée est bien liée
pas de constructeur déclaré deux fois dans le même type
5. Vérification de bonne formation des types

Entrée : Ty.t
Sortie : Ty.t validé, ou version annotée

À vérifier :

TyVar bien liée
TyNamed(name, args) a la bonne arité
TyArrow(args, ret) contient des types valides partout

Cette passe peut être appelée par d’autres :

vérification des déclarations
vérification des formules
vérification des preuves
6. Vérification de bonne formation des termes

Entrée : Term.t
Sortie : terme bien formé, idéalement annoté par son type

À vérifier :

variable liée ou globale autorisée selon le contexte
Constr(c, args) : constructeur connu, bon nombre d’arguments
App(f, args) : fonction connue, bon nombre d’arguments
types des arguments compatibles

Sortie utile :

soit simple validation
soit term * ty

Cette passe est centrale si tes formules contiennent des termes.

7. Vérification de bonne formation des formules

Entrée : Formula.t
Sortie : formule bien formée

À vérifier :

Pred(p, li) : prédicat déclaré, bonne arité, arguments bien typés
Eq(t1, t2) : les deux termes ont le même type
connecteurs logiques bien formés
Forall(v, ty, f) : type valide, variable liée dans f
Exists(v, ty, f) : idem

But :

garantir que les énoncés sont sensés avant de regarder les preuves
*)

open Logic
module Pp = LibCore.Pp
module SM = Map.Make (String)

type signature = {
    tyvars : string list;   (* variables de type génériques de la signature *)
    args : ty list;
    ret : ty;
  }

type env = {
    types : int SM.t;             (* nom de type -> arité *)
    ctors : signature SM.t;
    funs : signature SM.t;
    preds : signature SM.t;       (* ret inutilisé *)
    hyps : formula SM.t;          (* axiomes et théorèmes déjà prouvés *)
  }

let empty = { types = SM.empty; ctors = SM.empty; funs = SM.empty; preds = SM.empty; hyps = SM.empty }

(* ------------------------------------------------------------------------- *)
(* Types                                                                     *)
(* ------------------------------------------------------------------------- *)

let rec tyvars_of acc = function
  | TVar v -> if List.mem v acc then acc else acc @ [v]
  | TNamed (_, li) -> List.fold_left tyvars_of acc li
  | TArrow (li, r) -> tyvars_of (List.fold_left tyvars_of acc li) r

(* [bound] : None = variables de type libres autorisées, Some l = seulement celles de l *)
let rec check_ty env loc ?bound t = match t with
  | TVar v ->
     begin match bound with
     | Some l when not (List.mem v l) -> fail loc "unbound type variable %s" v
     | _ -> ()
     end
  | TNamed (n, li) ->
     begin match SM.find_opt n env.types with
     | None -> fail loc "unknown type %s" n
     | Some arity when arity <> List.length li ->
        fail loc "type %s expects %d argument(s), got %d" n arity (List.length li)
     | Some _ -> List.iter (check_ty env loc ?bound) li
     end
  | TArrow (li, r) -> List.iter (check_ty env loc ?bound) li; check_ty env loc ?bound r

(* ------------------------------------------------------------------------- *)
(* Termes : inférence avec unification du premier ordre                      *)
(* Les métavariables sont des TVar dont le nom commence par '?' ; les        *)
(* variables de type écrites par l'utilisateur ('a) sont rigides.            *)
(* ------------------------------------------------------------------------- *)

let is_meta v = String.length v > 0 && v.[0] = '?'
let meta_counter = ref 0
let fresh_meta () = incr meta_counter; TVar (Printf.sprintf "?%d" !meta_counter)

let instantiate sg =
  let sub = List.map (fun v -> v, fresh_meta ()) sg.tyvars in
  let rec go = function
    | TVar v -> (match List.assoc_opt v sub with Some m -> m | None -> TVar v)
    | TNamed (n, li) -> TNamed (n, List.map go li)
    | TArrow (li, r) -> TArrow (List.map go li, go r)
  in List.map go sg.args, go sg.ret

let rec resolve s = function
  | TVar v when is_meta v && Hashtbl.mem s v -> resolve s (Hashtbl.find s v)
  | TNamed (n, li) -> TNamed (n, List.map (resolve s) li)
  | TArrow (li, r) -> TArrow (List.map (resolve s) li, resolve s r)
  | t -> t

let rec occurs v = function
  | TVar w -> v = w
  | TNamed (_, li) -> List.exists (occurs v) li
  | TArrow (li, r) -> List.exists (occurs v) li || occurs v r

let rec unify s loc a b =
  let a = resolve s a and b = resolve s b in
  let mismatch () = fail loc "type mismatch: %a vs %a" pp_ty a pp_ty b in
  match a, b with
  | TVar x, TVar y when x = y -> ()
  | TVar x, t when is_meta x -> if occurs x t then mismatch () else Hashtbl.replace s x t
  | t, TVar x when is_meta x -> if occurs x t then mismatch () else Hashtbl.replace s x t
  | TNamed (n, l1), TNamed (m, l2) when n = m && List.length l1 = List.length l2 ->
     List.iter2 (unify s loc) l1 l2
  | TArrow (l1, r1), TArrow (l2, r2) when List.length l1 = List.length l2 ->
     List.iter2 (unify s loc) l1 l2; unify s loc r1 r2
  | _ -> mismatch ()

let apply_sig s env gamma loc what name sg args infer =
  let targs, tret = instantiate sg in
  if List.length targs <> List.length args then
    fail loc "%s %s expects %d argument(s), got %d" what name (List.length targs) (List.length args);
  List.iter2 (fun ta arg -> unify s arg.tloc ta (infer s env gamma arg)) targs args;
  tret

(* gamma : variables de terme liées (par forall, exists, gen, unpack) avec leur type *)
let rec infer_term s env gamma tm = match tm.t with
  | Var v ->
     begin match List.assoc_opt v gamma with
     | Some t -> t
     | None ->
        (* une constante déclarée par fundecl c : () -> T peut s'écrire c *)
        begin match SM.find_opt v env.funs with
        | Some sg when sg.args = [] -> snd (instantiate sg)
        | _ -> fail tm.tloc "unbound term variable %s" v
        end
     end
  | Constr (c, args) ->
     begin match SM.find_opt c env.ctors with
     | None -> fail tm.tloc "unknown constructor %s" c
     | Some sg -> apply_sig s env gamma tm.tloc "constructor" c sg args infer_term
     end
  | App (fn, args) ->
     begin match SM.find_opt fn env.funs with
     | None -> fail tm.tloc "unknown function %s" fn
     | Some sg -> apply_sig s env gamma tm.tloc "function" fn sg args infer_term
     end

let check_term env gamma tm expected =
  let s = Hashtbl.create 8 in
  unify s tm.tloc expected (infer_term s env gamma tm)

(* ------------------------------------------------------------------------- *)
(* Formules                                                                  *)
(* ------------------------------------------------------------------------- *)

let rec check_formula env gamma fm = match fm.f with
  | Top | Bottom -> ()
  | Pred (p, args) ->
     begin match SM.find_opt p env.preds with
     | None -> fail fm.floc "unknown predicate %s" p
     | Some sg ->
        let s = Hashtbl.create 8 in
        ignore (apply_sig s env gamma fm.floc "predicate" p sg args infer_term)
     end
  | Eq (a, b) ->
     let s = Hashtbl.create 8 in
     unify s fm.floc (infer_term s env gamma a) (infer_term s env gamma b)
  | And (a, b) | Or (a, b) | Impl (a, b) -> check_formula env gamma a; check_formula env gamma b
  | Forall (v, t, a) | Exists (v, t, a) ->
     check_ty env fm.floc t; check_formula env ((v, t) :: gamma) a

(* ------------------------------------------------------------------------- *)
(* Déclarations                                                              *)
(* ------------------------------------------------------------------------- *)

let dummy_loc = Loc.loc Lexing.dummy_pos Lexing.dummy_pos

let declare loc what map name v =
  if SM.mem name map then begin
    if loc == dummy_loc then Pp.failwith "%s %s is declared twice" what name
    else fail loc "%s %s is declared twice" what name
  end;
  SM.add name v map

(* Les déclarations n'ont pas de position dans l'AST : on prend celle du
   premier type rencontré quand il y en a une. *)
let loc_of_tys = function
  | [] -> dummy_loc
  | t :: _ -> PouleAst.Ty.Fixed.decoration t

let type_decl env name params constructors =
  let loc = loc_of_tys (List.concat_map snd constructors) in
  let types = declare loc "type" env.types name (List.length params) in
  let env = { env with types } in
  let ret = TNamed (name, List.map (fun v -> TVar v) params) in
  List.fold_left (fun env (c, tys) ->
      let args = List.map ty_of tys in
      List.iter (check_ty env loc ~bound:params) args;
      { env with ctors = declare loc "constructor" env.ctors c { tyvars = params; args; ret } })
    env constructors

let fun_decl env name args ret =
  let loc = loc_of_tys (ret :: args) in
  let args = List.map ty_of args and ret = ty_of ret in
  List.iter (check_ty env loc) (ret :: args);
  let tyvars = List.fold_left tyvars_of [] (args @ [ret]) in
  { env with funs = declare loc "function" env.funs name { tyvars; args; ret } }

let pred_decl env name args =
  let loc = loc_of_tys args in
  let args = List.map ty_of args in
  List.iter (check_ty env loc) args;
  let tyvars = List.fold_left tyvars_of [] args in
  { env with preds = declare loc "predicate" env.preds name { tyvars; args; ret = TNamed ("Prop", []) } }

let closed_formula env fm =
  check_formula env [] fm

let add_hyp env name fm =
  { env with hyps = declare fm.floc "axiom/theorem" env.hyps name fm }



