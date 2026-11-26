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

let rec infer ctx pr : formula =
  let loc = pr.ploc in
  match pr.p with
  | PVar h ->
     begin match lookup ctx h with
     | Some f -> f
     | None -> fail loc "unknown hypothesis %s" h
     end
  | Triv -> mk loc Top
  | Abort (q, f) -> wf ctx f; check ctx q (mk loc Bottom); f
  | Pair (a, b) -> mk loc (And (infer ctx a, infer ctx b))
  | Fst q ->
     begin match infer ctx q with
     | { f = And (a, _); _ } -> a
     | f -> shape loc "fst" "A /\\ B" f
     end
  | Snd q ->
     begin match infer ctx q with
     | { f = And (_, b); _ } -> b
     | f -> shape loc "snd" "A /\\ B" f
     end
  | Left (q, b) -> wf ctx b; mk loc (Or (infer ctx q, b))
  | Right (a, q) -> wf ctx a; mk loc (Or (a, infer ctx q))
  | Case (q, (h1, p1), (h2, p2)) ->
     begin match infer ctx q with
     | { f = Or (a, b); _ } ->
        let c = infer (add_hyp ctx h1 a) p1 in
        check (add_hyp ctx h2 b) p2 c;
        c
     | f -> shape loc "match" "A \\/ B" f
     end
  | Lam (h, a, q) -> wf ctx a; mk loc (Impl (a, infer (add_hyp ctx h a) q))
  | PApp (q, r) ->
     begin match infer ctx q with
     | { f = Impl (a, b); _ } -> check ctx r a; b
     | f -> shape loc "application" "A -> B" f
     end
  | Gen (x, t, q) ->
     wf_ty ctx loc t;
     eigen ctx loc x None;
     mk loc (Forall (x, t, infer (add_var ctx x t) q))
  | Inst (q, tm) ->
     begin match infer ctx q with
     | { f = Forall (x, t, a); _ } -> SC.check_term ctx.env ctx.gamma tm t; subst x tm a
     | f -> shape loc "instantiation [t]" "forall (x : T). A" f
     end
  | Pack _ ->
     fail loc "cannot infer what pack proves: use it where the exists formula is the expected goal"
  | Unpack (tm, x, h, q) ->
     let y, t, a = exists_hyp ctx tm in
     eigen ctx loc x None;
     let c = infer (add_hyp (add_var ctx x t) h (subst y { t = Var x; tloc = loc } a)) q in
     if S.mem x (fv_formula c) then
       fail loc "the witness %s escapes: it occurs in the conclusion %a" x pp_formula c;
     c

and check ctx pr goal : unit =
  let loc = pr.ploc in
  let mismatch_ann what ann expected =
    fail loc "%s: the annotation@\n  %a@\ndoes not match the goal's@\n  %a" what pp_formula ann pp_formula expected
  in
  match pr.p, goal.f with
  | Triv, Top -> ()
  | Pair (a, b), And (ga, gb) -> check ctx a ga; check ctx b gb
  | Left (q, b), Or (ga, gb) ->
     if not (alpha_equal b gb) then mismatch_ann "left" b gb;
     check ctx q ga
  | Right (a, q), Or (ga, gb) ->
     if not (alpha_equal a ga) then mismatch_ann "right" a ga;
     check ctx q gb
  | Case (q, (h1, p1), (h2, p2)), _ ->
     begin match infer ctx q with
     | { f = Or (a, b); _ } -> check (add_hyp ctx h1 a) p1 goal; check (add_hyp ctx h2 b) p2 goal
     | f -> shape loc "match" "A \\/ B" f
     end
  | Lam (h, a, q), Impl (ga, gb) ->
     wf ctx a;
     if not (alpha_equal a ga) then mismatch_ann "fun" a ga;
     check (add_hyp ctx h a) q gb
  | Gen (x, t, q), Forall (y, gt, ga) ->
     if not (ty_equal t gt) then
       fail loc "gen: variable %s has type %a but the goal quantifies over %a" x pp_ty t pp_ty gt;
     eigen ctx loc x (Some goal);
     check (add_var ctx x t) q (subst y { t = Var x; tloc = loc } ga)
  | Pack (t, tm, q), Exists (y, gt, ga) ->
     if not (ty_equal t gt) then
       fail loc "pack: witness type %a but the goal is exists over %a" pp_ty t pp_ty gt;
     SC.check_term ctx.env ctx.gamma tm t;
     check ctx q (subst y tm ga)
  | Unpack (tm, x, h, q), _ ->
     let y, t, a = exists_hyp ctx tm in
     eigen ctx loc x (Some goal);
     check (add_hyp (add_var ctx x t) h (subst y { t = Var x; tloc = loc } a)) q goal
  | Abort (q, f), _ ->
     wf ctx f;
     if not (alpha_equal f goal) then mismatch_ann "abort" f goal;
     check ctx q (mk loc Bottom)
  | _ ->
     let got = infer ctx pr in
     if not (alpha_equal got goal) then
       fail loc "this proof proves@\n  %a@\nbut the goal is@\n  %a" pp_formula got pp_formula goal

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

let process acc (item : (Types.ParsedProg.ty, Types.ParsedProg.term, Types.ParsedProg.formula, Types.ParsedProg.proof, string) PouleAst.TopLevel.t) =
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
           check { env = acc.genv; gamma = []; delta = [] } (proof_of proof) fm;
           Format.printf "%s : OK@." label;
           match name with
           | Some n -> { acc with genv = SC.add_hyp acc.genv n fm }
           | None -> acc
         with Failure msg ->
           Format.printf "%s : FAILED@\n%s@\n@." label msg;
           { acc with failures = acc.failures + 1 }
       end
  in
  acc, item

let final acc li =
  if acc.failures > 0 then Pp.failwith "%d proof(s) rejected" acc.failures;
  li

let passe = { init = { genv = SC.empty; failures = 0 }; process; final }
