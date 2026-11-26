# MINI OCAML

Le projet permet de parser, typer, évaluer, compiler un micro-caml très simple. C'est inspiré du projet étudant d'un ami, mais son projet à lui restait très primitif. Je suis donc parti sur un micro-caml qui permet les fonctionnalités suivantes :
- un typer avec du polymorphisme
- des types sommes
- des tuples
- des clotures (applications partielles, déclarations de fonctions avec un environement)
- du pattern matching
- un backend en C, avec pour objectif ultime un backend llvm.
et quelques passes de compilations additionnelles :
- transformation des variables et champs en entiers
- && et || lazy
- de l'inline sur les variables du backend

# Dépendances
Pour ceux qui ne connaissent pas ocaml, il faut installer opam, le configurer, installer dune, menhir, et coté IDE, j'ai codé sous emacs avec merlin. Pour certains trucs, j'ai besoin d'ocaml-print-intf mais seulement pour de la doc.

# QUICK START
build runtime (normalement on a pas besoin de ça) :
```
dune build runtime/libruntime.a
```
tests :
```
dune runtest
```
test spécifique :
```
dune runtest test/main.t
```
Usage :
```
OCAMLRUNPARAM=b dune exec -- bin/main.exe test/t02.ml
```

Ajout de l'option --debug <nom de la passe> pour pouvoir afficher un AST intermédiaire (utile pour le debug. Les passes dispo sont dans le fichier lib/passes.ml)

# POULE
`poule` vérifie des preuves en déduction naturelle (logique du premier ordre typée) :
```
dune exec -- bin/poule.exe test/poule_logic.poule
```
Chaque `theorem` / `check` affiche `OK` ou `FAILED` avec la raison et la position ; le code de sortie est non nul si une preuve est rejetée. Un théorème prouvé s'utilise ensuite comme un axiome.

| preuve | prouve | à partir de |
|---|---|---|
| `h` | l'hypothèse `h` | axiome, théorème, `fun`, `match`, `unpack` |
| `triv` | `Top` | |
| `abort p : F` | `F` | `p : Bottom` |
| `(p, q)` / `fst p` / `snd p` | `A /\ B` / `A` / `B` | |
| `left p : B` / `right A p` | `A \/ B` | `p : A` / `p : B` |
| `match p with \| left h1 => p1 \| right h2 => p2` | `C` | `p : A \/ B`, `p1`, `p2 : C` |
| `fun (h : A) => p` / `p q` | `A -> B` / `B` | |
| `gen (x : T) => p` | `forall (x : T). A` | `p : A`, `x` frais |
| `p [t]` | `A[x := t]` | `p : forall (x : T). A`, `t : T` |
| `pack [T, t, p]` | `exists (x : T). A` | `p : A[x := t]` |
| `unpack (h, x, h', p)` | `C` | `h : exists (y : T). A`, `h' : A[y := x]`, `x` frais |
