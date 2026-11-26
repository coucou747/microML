open LibCore.Passes
module Pp = LibCore.Pp

(* Vérification des preuves (notes de conception d'origine, implémentées ci-dessous)

9. Vérification des toplevels

Entrée : programme complet
Sortie : programme validé

Par déclaration :

TypeDecl : vérifier la déclaration
FunDecl : vérifier la signature
PredDecl : vérifier la signature
Axiom : vérifier la formule
Theorem :
vérifier la formule
vérifier la preuve contre cette formule
Check :
vérifier la formule
vérifier la preuve contre cette formule




. Vérification des preuves
Entrée : proof, formula attendue
Sortie : preuve validée, ou preuve annotée

Jugement central :

￼
Γ ⊢ p : F
Règles typiques :

Var v : chercher v dans le contexte de preuve

Triv : prouve Top

Abort(p, F) : si p : Bottom, alors résultat F

Pair(p1,p2) : prouve A ∧ B

Fst p / Snd p : éliminent A ∧ B

Left / Right : introduisent A ∨ B

Case : élimine A ∨ B

Lam(v, A, p) : introduit A -> B

App(p,q) : élimine A -> B

Gen(v, ty, p) : introduit forall

Inst(p, t) : élimine forall

Pack(ty, t, p) : introduit exists

Unpack(...) : élimine exists

C’est la passe principale de Poule.
*)

open Logic
module SC = SanityCheck

(* Γ : variables de terme liées ; Δ : hypothèses locales (fun, match, unpack). *)
type ctx = {
    env : SC.env;
    gamma : (string * ty) list;
    delta : (string * formula) list;
  }

let mk loc f = { f; floc = loc }

let lookup ctx h =
  match List.assoc_opt h ctx.delta with
  | Some f -> Some f
  | None -> SC.SM.find_opt h ctx.env.hyps

let add_hyp ctx h f = { ctx with delta = (h, f) :: ctx.delta }
let add_var ctx x t = { ctx with gamma = (x, t) :: ctx.gamma }

let wf ctx fm = SC.check_formula ctx.env ctx.gamma fm
let wf_ty ctx loc t = SC.check_ty ctx.env loc t

(* Condition sur la variable propre de gen / unpack : elle ne doit apparaître
   libre ni dans une hypothèse locale ni dans le but. *)
let eigen ctx loc x goal =
  List.iter (fun (h, f) ->
      if S.mem x (fv_formula f) then
        fail loc "variable %s is not fresh: it occurs free in hypothesis %s : %a" x h pp_formula f)
    ctx.delta;
  match goal with
  | Some g when S.mem x (fv_formula g) ->
     fail loc "variable %s is not fresh: it occurs free in the goal %a" x pp_formula g
  | _ -> ()

let shape loc what expected got =
  fail loc "%s expects a proof of %s, but this proves@\n  %a" what expected pp_formula got

(* unpack (h, x, h', p) : h doit nommer une hypothèse qui prouve exists (y : T). A *)
let exists_hyp ctx tm =
  match tm.t with
  | Var h ->
     begin match lookup ctx h with
     | Some { f = Exists (y, t, a); _ } -> y, t, a
     | Some f -> shape tm.tloc "unpack" "exists (x : T). A" f
     | None -> fail tm.tloc "unknown hypothesis %s" h
     end
  | _ -> fail tm.tloc "unpack expects the name of a hypothesis proving an exists, got %a" pp_term tm

(* Arbre de dérivation construit pendant la vérification (affiché par --trace). *)
type deriv = {
    rule : string;
    concl : formula;
    dloc : Loc.t;
    intro : string list;     (* hypothèses / variables entrées dans la portée à ce nœud :
                                le contexte d'un nœud = union des intro de la racine à lui *)
    children : deriv list;
  }

let node rule concl dloc children = { rule; concl; dloc; intro = []; children }
let hyp_intro h f = Format.asprintf "%s : %a" h pp_formula f
let var_intro x t = Format.asprintf "%s : %a" x pp_ty t
let scoped intro d = { d with intro = intro @ d.intro }

let rec infer ctx pr : formula * deriv =
  let loc = pr.ploc in
  let leaf rule f = f, node rule f loc [] in
  match pr.p with
  | PVar h ->
     begin match lookup ctx h with
     | Some f -> leaf ("hyp " ^ h) f
     | None -> fail loc "unknown hypothesis %s" h
     end
  | Triv -> leaf "Top-I" (mk loc Top)
  | Abort (q, f) -> wf ctx f; let d = check ctx q (mk loc Bottom) in f, node "Bottom-E" f loc [d]
  | Pair (a, b) ->
     let fa, da = infer ctx a and fb, db = infer ctx b in
     let f = mk loc (And (fa, fb)) in f, node "And-I" f loc [da; db]
  | Fst q ->
     begin match infer ctx q with
     | { f = And (a, _); _ }, d -> a, node "And-E1" a loc [d]
     | f, _ -> shape loc "fst" "A /\\ B" f
     end
  | Snd q ->
     begin match infer ctx q with
     | { f = And (_, b); _ }, d -> b, node "And-E2" b loc [d]
     | f, _ -> shape loc "snd" "A /\\ B" f
     end
  | Left (q, b) ->
     wf ctx b; let a, d = infer ctx q in let f = mk loc (Or (a, b)) in f, node "Or-I1" f loc [d]
  | Right (a, q) ->
     wf ctx a; let b, d = infer ctx q in let f = mk loc (Or (a, b)) in f, node "Or-I2" f loc [d]
  | Case (q, (h1, p1), (h2, p2)) ->
     begin match infer ctx q with
     | { f = Or (a, b); _ }, d ->
        let c, d1 = infer (add_hyp ctx h1 a) p1 in
        let d2 = check (add_hyp ctx h2 b) p2 c in
        c, node "Or-E" c loc [d; scoped [hyp_intro h1 a] d1; scoped [hyp_intro h2 b] d2]
     | f, _ -> shape loc "match" "A \\/ B" f
     end
  | Lam (h, a, q) ->
     wf ctx a;
     let b, d = infer (add_hyp ctx h a) q in
     let f = mk loc (Impl (a, b)) in
     f, node "Impl-I" f loc [scoped [hyp_intro h a] d]
  | PApp (q, r) ->
     begin match infer ctx q with
     | { f = Impl (a, b); _ }, d -> let dr = check ctx r a in b, node "Impl-E" b loc [d; dr]
     | f, _ -> shape loc "application" "A -> B" f
     end
  | Gen (x, t, q) ->
     wf_ty ctx loc t;
     eigen ctx loc x None;
     let a, d = infer (add_var ctx x t) q in
     let f = mk loc (Forall (x, t, a)) in
     f, node "Forall-I" f loc [scoped [var_intro x t] d]
  | Inst (q, tm) ->
     begin match infer ctx q with
     | { f = Forall (x, t, a); _ }, d ->
        SC.check_term ctx.env ctx.gamma tm t;
        let f = subst x tm a in f, node (Format.asprintf "Forall-E [%a]" pp_term tm) f loc [d]
     | f, _ -> shape loc "instantiation [t]" "forall (x : T). A" f
     end
  | Pack _ ->
     fail loc "cannot infer what pack proves: use it where the exists formula is the expected goal"
  | Unpack (tm, x, h, q) ->
     let y, t, a = exists_hyp ctx tm in
     eigen ctx loc x None;
     let ax = subst y { t = Var x; tloc = loc } a in
     let c, d = infer (add_hyp (add_var ctx x t) h ax) q in
     if S.mem x (fv_formula c) then
       fail loc "the witness %s escapes: it occurs in the conclusion %a" x pp_formula c;
     c, node (Format.asprintf "Exists-E [%a]" pp_term tm) c loc [scoped [var_intro x t; hyp_intro h ax] d]

and check ctx pr goal : deriv =
  let loc = pr.ploc in
  let mismatch_ann what ann expected =
    fail loc "%s: the annotation@\n  %a@\ndoes not match the goal's@\n  %a" what pp_formula ann pp_formula expected
  in
  match pr.p, goal.f with
  | Triv, Top -> node "Top-I" goal loc []
  | Pair (a, b), And (ga, gb) -> node "And-I" goal loc [check ctx a ga; check ctx b gb]
  | Left (q, b), Or (ga, gb) ->
     if not (alpha_equal b gb) then mismatch_ann "left" b gb;
     node "Or-I1" goal loc [check ctx q ga]
  | Right (a, q), Or (ga, gb) ->
     if not (alpha_equal a ga) then mismatch_ann "right" a ga;
     node "Or-I2" goal loc [check ctx q gb]
  | Case (q, (h1, p1), (h2, p2)), _ ->
     begin match infer ctx q with
     | { f = Or (a, b); _ }, d ->
        let d1 = check (add_hyp ctx h1 a) p1 goal and d2 = check (add_hyp ctx h2 b) p2 goal in
        node "Or-E" goal loc [d; scoped [hyp_intro h1 a] d1; scoped [hyp_intro h2 b] d2]
     | f, _ -> shape loc "match" "A \\/ B" f
     end
  | Lam (h, a, q), Impl (ga, gb) ->
     wf ctx a;
     if not (alpha_equal a ga) then mismatch_ann "fun" a ga;
     node "Impl-I" goal loc [scoped [hyp_intro h a] (check (add_hyp ctx h a) q gb)]
  | Gen (x, t, q), Forall (y, gt, ga) ->
     if not (ty_equal t gt) then
       fail loc "gen: variable %s has type %a but the goal quantifies over %a" x pp_ty t pp_ty gt;
     eigen ctx loc x (Some goal);
     node "Forall-I" goal loc [scoped [var_intro x t] (check (add_var ctx x t) q (subst y { t = Var x; tloc = loc } ga))]
  | Pack (t, tm, q), Exists (y, gt, ga) ->
     if not (ty_equal t gt) then
       fail loc "pack: witness type %a but the goal is exists over %a" pp_ty t pp_ty gt;
     SC.check_term ctx.env ctx.gamma tm t;
     node (Format.asprintf "Exists-I [%a]" pp_term tm) goal loc [check ctx q (subst y tm ga)]
  | Unpack (tm, x, h, q), _ ->
     let y, t, a = exists_hyp ctx tm in
     eigen ctx loc x (Some goal);
     let ax = subst y { t = Var x; tloc = loc } a in
     node (Format.asprintf "Exists-E [%a]" pp_term tm) goal loc [scoped [var_intro x t; hyp_intro h ax] (check (add_hyp (add_var ctx x t) h ax) q goal)]
  | Abort (q, f), _ ->
     wf ctx f;
     if not (alpha_equal f goal) then mismatch_ann "abort" f goal;
     node "Bottom-E" goal loc [check ctx q (mk loc Bottom)]
  | _ ->
     let got, d = infer ctx pr in
     if not (alpha_equal got goal) then
       fail loc "this proof proves@\n  %a@\nbut the goal is@\n  %a" pp_formula got pp_formula goal;
     d

(* ------------------------------------------------------------------------- *)
(* Sortie JSON (--trace), une ligne par théorème                             *)
(* ------------------------------------------------------------------------- *)

let json_string s =
  let b = Buffer.create (String.length s + 2) in
  Buffer.add_char b '"';
  String.iter (function
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c) s;
  Buffer.add_char b '"';
  Buffer.contents b

let rec json_of_deriv d =
  Printf.sprintf "{\"rule\":%s,\"concl\":%s,\"loc\":%s,\"intro\":[%s],\"children\":[%s]}"
    (json_string d.rule)
    (json_string (Format.asprintf "%a" pp_formula d.concl))
    (json_string (Format.asprintf "%a" Loc.pp d.dloc))
    (String.concat "," (List.map json_string d.intro))
    (String.concat "," (List.map json_of_deriv d.children))

(* ------------------------------------------------------------------------- *)
(* Toplevel                                                                   *)
(* ------------------------------------------------------------------------- *)

type acc = {
    genv : SC.env;
    failures : int;
  }

let theorem_label = function
  | Some name -> "theorem " ^ name
  | None -> "check"

let process ~trace acc (item : (Types.ParsedProg.ty, Types.ParsedProg.term, Types.ParsedProg.formula, Types.ParsedProg.proof, string) PouleAst.TopLevel.t) =
  let open PouleAst.TopLevel in
  let acc = match item with
    | TypeDecl { name; params; constructors } -> { acc with genv = SC.type_decl acc.genv name params constructors }
    | FunDecl { name; args; ret } -> { acc with genv = SC.fun_decl acc.genv name args ret }
    | PredDecl { name; args } -> { acc with genv = SC.pred_decl acc.genv name args }
    | Axiom { name; formula } ->
       let fm = formula_of formula in
       SC.closed_formula acc.genv fm;
       { acc with genv = SC.add_hyp acc.genv name fm }
    | Theorem { name; formula; proof } ->
       let label = theorem_label name in
       begin try
           let fm = formula_of formula in
           SC.closed_formula acc.genv fm;
           let d = check { env = acc.genv; gamma = []; delta = [] } (proof_of proof) fm in
           Format.printf "%s : OK@." label;
           if trace then
             Format.printf "TRACE {\"theorem\":%s,\"ok\":true,\"formula\":%s,\"tree\":%s}@."
               (json_string label) (json_string (Format.asprintf "%a" pp_formula fm)) (json_of_deriv d);
           match name with
           | Some n -> { acc with genv = SC.add_hyp acc.genv n fm }
           | None -> acc
         with Failure msg ->
           Format.printf "%s : FAILED@\n%s@\n@." label msg;
           if trace then
             Format.printf "TRACE {\"theorem\":%s,\"ok\":false,\"message\":%s}@." (json_string label) (json_string msg);
           { acc with failures = acc.failures + 1 }
       end
  in
  acc, item

let final acc li =
  if acc.failures > 0 then Pp.failwith "%d proof(s) rejected" acc.failures;
  li

let passe ~trace = { init = { genv = SC.empty; failures = 0 }; process = process ~trace; final }
