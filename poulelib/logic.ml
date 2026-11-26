(* Représentation de travail pour la vérification de Poule.

   L'AST issu du parser (PouleAst / Types.ParsedProg, en points fixes) est converti
   une fois en types OCaml simples, nommés par des chaînes et décorés par leur
   position : c'est sur eux que travaillent SanityCheck (bonne formation) et
   PassProof (vérification des preuves). *)

module Loc = LibCore.Loc
module P = Types.ParsedProg

(* ------------------------------------------------------------------------- *)
(* Types, termes, formules, preuves                                          *)
(* ------------------------------------------------------------------------- *)

type ty =
  | TVar of string                 (* variable de type ('a), rigide *)
  | TNamed of string * ty list     (* Nat, List('a) *)
  | TArrow of ty list * ty

type term = { t : term_node; tloc : Loc.t }
and term_node =
  | Var of string
  | Constr of string * term list
  | App of string * term list

type formula = { f : formula_node; floc : Loc.t }
and formula_node =
  | Top
  | Bottom
  | Pred of string * term list
  | Eq of term * term
  | And of formula * formula
  | Or of formula * formula
  | Impl of formula * formula
  | Forall of string * ty * formula
  | Exists of string * ty * formula

type proof = { p : proof_node; ploc : Loc.t }
and proof_node =
  | PVar of string
  | Triv
  | Abort of proof * formula
  | Pair of proof * proof
  | Fst of proof
  | Snd of proof
  | Left of proof * formula           (* left p : B   prouve A ∨ B si p : A *)
  | Right of formula * proof          (* right A p    prouve A ∨ B si p : B *)
  | Case of proof * (string * proof) * (string * proof)
  | Lam of string * formula * proof
  | PApp of proof * proof
  | Gen of string * ty * proof
  | Inst of proof * term
  | Pack of ty * term * proof
  | Unpack of term * string * string * proof

(* ------------------------------------------------------------------------- *)
(* Conversion depuis l'AST parsé                                             *)
(* ------------------------------------------------------------------------- *)

let rec ty_of (x : P.ty) : ty =
  match PouleAst.Ty.Fixed.unfix x with
  | Fixable.Ty.TyVar v -> TVar v
  | Fixable.Ty.TyNamed (n, li) -> TNamed (n, List.map ty_of li)
  | Fixable.Ty.TyArrow (li, r) -> TArrow (List.map ty_of li, ty_of r)

let rec term_of (x : P.term) : term =
  let tloc = PouleAst.Term.Fixed.decoration x in
  let t = match PouleAst.Term.Fixed.unfix x with
    | Fixable.Term.Var v -> Var v
    | Fixable.Term.Constr (c, li) -> Constr (c, List.map term_of li)
    | Fixable.Term.App (fn, li) -> App (fn, List.map term_of li)
  in { t; tloc }

let rec formula_of (x : P.formula) : formula =
  let floc = PouleAst.Formula.Fixed.decoration x in
  let f = match PouleAst.Formula.Fixed.unfix x with
    | Fixable.Formula.Top -> Top
    | Fixable.Formula.Bottom -> Bottom
    | Fixable.Formula.Pred (p, li) -> Pred (p, List.map term_of li)
    | Fixable.Formula.Eq (a, b) -> Eq (term_of a, term_of b)
    | Fixable.Formula.And (a, b) -> And (formula_of a, formula_of b)
    | Fixable.Formula.Or (a, b) -> Or (formula_of a, formula_of b)
    | Fixable.Formula.Impl (a, b) -> Impl (formula_of a, formula_of b)
    | Fixable.Formula.Forall (v, t, a) -> Forall (v, ty_of t, formula_of a)
    | Fixable.Formula.Exists (v, t, a) -> Exists (v, ty_of t, formula_of a)
  in { f; floc }

let rec proof_of (x : P.proof) : proof =
  let ploc = PouleAst.ProofTerm.Fixed.decoration x in
  let p = match PouleAst.ProofTerm.Fixed.unfix x with
    | Fixable.ProofTerm.Var v -> PVar v
    | Fixable.ProofTerm.Triv -> Triv
    | Fixable.ProofTerm.Abort (q, f) -> Abort (proof_of q, formula_of f)
    | Fixable.ProofTerm.Pair (a, b) -> Pair (proof_of a, proof_of b)
    | Fixable.ProofTerm.Fst q -> Fst (proof_of q)
    | Fixable.ProofTerm.Snd q -> Snd (proof_of q)
    | Fixable.ProofTerm.Left (q, f) -> Left (proof_of q, formula_of f)
    | Fixable.ProofTerm.Right (f, q) -> Right (formula_of f, proof_of q)
    | Fixable.ProofTerm.Case (q, (h1, q1), (h2, q2)) ->
       Case (proof_of q, (h1, proof_of q1), (h2, proof_of q2))
    | Fixable.ProofTerm.Lam (h, f, q) -> Lam (h, formula_of f, proof_of q)
    | Fixable.ProofTerm.App (a, b) -> PApp (proof_of a, proof_of b)
    | Fixable.ProofTerm.Gen (v, t, q) -> Gen (v, ty_of t, proof_of q)
    | Fixable.ProofTerm.Inst (q, t) -> Inst (proof_of q, term_of t)
    | Fixable.ProofTerm.Pack (t, tm, q) -> Pack (ty_of t, term_of tm, proof_of q)
    | Fixable.ProofTerm.Unpack (tm, x, h, q) -> Unpack (term_of tm, x, h, proof_of q)
  in { p; ploc }

(* ------------------------------------------------------------------------- *)
(* Affichage                                                                  *)
(* ------------------------------------------------------------------------- *)

let pp_list pp f li = LibCore.Pp.list (LibCore.Pp.sep ", ") pp f li

let rec pp_ty f = function
  | TVar v -> Format.pp_print_string f v
  | TNamed (n, []) -> Format.pp_print_string f n
  | TNamed (n, li) -> Format.fprintf f "%s(%a)" n (pp_list pp_ty) li
  | TArrow ([a], r) -> Format.fprintf f "(%a -> %a)" pp_ty a pp_ty r
  | TArrow (li, r) -> Format.fprintf f "((%a) -> %a)" (pp_list pp_ty) li pp_ty r

let rec pp_term f tm = match tm.t with
  | Var v -> Format.pp_print_string f v
  | Constr (c, []) -> Format.pp_print_string f c
  | Constr (c, li) | App (c, li) -> Format.fprintf f "%s(%a)" c (pp_list pp_term) li

(* précédences : 0 = ->, 1 = \/, 2 = /\, 3 = atome *)
let rec pp_formula_prec prec f fm =
  let paren p fmt = if prec > p then Format.fprintf f ("(" ^^ fmt ^^ ")") else Format.fprintf f fmt in
  match fm.f with
  | Top -> Format.pp_print_string f "Top"
  | Bottom -> Format.pp_print_string f "Bottom"
  | Pred (p, li) -> Format.fprintf f "%s(%a)" p (pp_list pp_term) li
  | Eq (a, b) -> paren 2 "%a = %a" pp_term a pp_term b
  | And (a, b) -> paren 2 "%a /\\ %a" (pp_formula_prec 2) a (pp_formula_prec 3) b
  | Or (a, b) -> paren 1 "%a \\/ %a" (pp_formula_prec 1) a (pp_formula_prec 2) b
  | Impl (a, b) -> paren 0 "%a -> %a" (pp_formula_prec 1) a (pp_formula_prec 0) b
  | Forall (v, t, a) -> paren 0 "forall (%s : %a). %a" v pp_ty t (pp_formula_prec 0) a
  | Exists (v, t, a) -> paren 0 "exists (%s : %a). %a" v pp_ty t (pp_formula_prec 0) a
let pp_formula f fm = pp_formula_prec 0 f fm

(* ------------------------------------------------------------------------- *)
(* Variables libres, substitution, α-équivalence                              *)
(* ------------------------------------------------------------------------- *)

module S = Set.Make (String)

let rec fv_term tm = match tm.t with
  | Var v -> S.singleton v
  | Constr (_, li) | App (_, li) -> List.fold_left (fun acc t -> S.union acc (fv_term t)) S.empty li

let rec fv_formula fm = match fm.f with
  | Top | Bottom -> S.empty
  | Pred (_, li) -> List.fold_left (fun acc t -> S.union acc (fv_term t)) S.empty li
  | Eq (a, b) -> S.union (fv_term a) (fv_term b)
  | And (a, b) | Or (a, b) | Impl (a, b) -> S.union (fv_formula a) (fv_formula b)
  | Forall (v, _, a) | Exists (v, _, a) -> S.remove v (fv_formula a)

let fresh_name avoid base =
  let rec go i =
    let n = Printf.sprintf "%s%d" base i in
    if S.mem n avoid then go (i + 1) else n
  in go 1

let rec subst_term x s tm = match tm.t with
  | Var v when v = x -> s
  | Var _ -> tm
  | Constr (c, li) -> { tm with t = Constr (c, List.map (subst_term x s) li) }
  | App (fn, li) -> { tm with t = App (fn, List.map (subst_term x s) li) }

(* fm[x := s], sans capture : un lieur qui capturerait une variable de s est renommé. *)
let rec subst x s fm =
  let fvs = fv_term s in
  let binder mk v t a =
    if v = x then fm
    else if S.mem v fvs then
      let v' = fresh_name (S.union fvs (S.union (fv_formula a) (S.singleton x))) v in
      let a' = subst v { t = Var v'; tloc = fm.floc } a in
      { fm with f = mk v' t (subst x s a') }
    else { fm with f = mk v t (subst x s a) }
  in
  match fm.f with
  | Top | Bottom -> fm
  | Pred (p, li) -> { fm with f = Pred (p, List.map (subst_term x s) li) }
  | Eq (a, b) -> { fm with f = Eq (subst_term x s a, subst_term x s b) }
  | And (a, b) -> { fm with f = And (subst x s a, subst x s b) }
  | Or (a, b) -> { fm with f = Or (subst x s a, subst x s b) }
  | Impl (a, b) -> { fm with f = Impl (subst x s a, subst x s b) }
  | Forall (v, t, a) -> binder (fun v t a -> Forall (v, t, a)) v t a
  | Exists (v, t, a) -> binder (fun v t a -> Exists (v, t, a)) v t a

let rec ty_equal a b = match a, b with
  | TVar x, TVar y -> x = y
  | TNamed (n, l1), TNamed (m, l2) -> n = m && List.length l1 = List.length l2 && List.for_all2 ty_equal l1 l2
  | TArrow (l1, r1), TArrow (l2, r2) ->
     List.length l1 = List.length l2 && List.for_all2 ty_equal l1 l2 && ty_equal r1 r2
  | _ -> false

(* env : liste d'associations (variable liée à gauche, variable liée à droite) *)
let rec term_alpha env a b = match a.t, b.t with
  | Var x, Var y ->
     (* le lieur le plus proche qui lie x à gauche ou y à droite doit lier les deux *)
     let rec lookup = function
       | [] -> x = y
       | (a, b) :: tl -> if a = x || b = y then a = x && b = y else lookup tl
     in lookup env
  | Constr (c, l1), Constr (d, l2) | App (c, l1), App (d, l2) ->
     c = d && List.length l1 = List.length l2 && List.for_all2 (term_alpha env) l1 l2
  | _ -> false

let rec alpha_env env a b = match a.f, b.f with
  | Top, Top | Bottom, Bottom -> true
  | Pred (p, l1), Pred (q, l2) ->
     p = q && List.length l1 = List.length l2 && List.for_all2 (term_alpha env) l1 l2
  | Eq (a1, b1), Eq (a2, b2) -> term_alpha env a1 a2 && term_alpha env b1 b2
  | And (a1, b1), And (a2, b2) | Or (a1, b1), Or (a2, b2) | Impl (a1, b1), Impl (a2, b2) ->
     alpha_env env a1 a2 && alpha_env env b1 b2
  | Forall (x, t1, a1), Forall (y, t2, a2) | Exists (x, t1, a1), Exists (y, t2, a2) ->
     ty_equal t1 t2 && alpha_env ((x, y) :: env) a1 a2
  | _ -> false

let alpha_equal a b = alpha_env [] a b

let fail loc fmt =
  Format.kasprintf (fun msg -> failwith (Format.asprintf "%s@\n(location %a)" msg Loc.pp loc)) fmt
