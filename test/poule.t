POULE : vérification des preuves
  $ ../bin/poule.exe test01.poule
  theorem id_and : OK
  check : OK
  $ ../bin/poule.exe poule_logic.poule
  theorem and_comm : OK
  theorem or_comm : OK
  theorem trans : OK
  theorem curry : OK
  theorem top : OK
  theorem ex_falso : OK
  theorem reuse : OK
  theorem even_two : OK
  theorem even_four : OK
  theorem even_ss' : OK
  theorem some_even : OK
  theorem shift : OK
  theorem const : OK
  theorem poly : OK
  theorem no_capture : OK
  check : OK
une preuve fausse ou une formule mal formée est rejetée, avec sa position :
  $ ../bin/poule.exe poule_errors.poule 2>/dev/null
  theorem wrong : FAILED
  this proof proves
    even(Zero)
  but the goal is
    even(Zero) /\ even(Zero)
  (location <poule_errors.poule>15:43-15:45)
  
  theorem unknown : FAILED
  unknown hypothesis nothere
  (location <poule_errors.poule>18:24-18:31)
  
  theorem not_fresh : FAILED
  variable n is not fresh: it occurs free in hypothesis h : even(n)
  (location <poule_errors.poule>22:40-22:58)
  
  theorem ill_typed : FAILED
  type mismatch: Nat vs List(?1)
  (location <poule_errors.poule>25:25-25:28)
  
  theorem arity : FAILED
  predicate even expects 1 argument(s), got 2
  (location <poule_errors.poule>26:16-26:32)
  
  theorem unbound : FAILED
  unbound term variable x
  (location <poule_errors.poule>27:23-27:24)
  
  theorem bad_left : FAILED
  left: the annotation
    r()
  does not match the goal's
    q()
  (location <poule_errors.poule>30:32-30:45)
  
  theorem bad_fst : FAILED
  fst expects a proof of A /\ B, but this proves
    p()
  (location <poule_errors.poule>33:24-33:30)
  
  theorem capture : FAILED
  this proof proves
    exists (y1 : Nat). le(y, y1)
  but the goal is
    exists (z : Nat). le(z, z)
  (location <poule_errors.poule>38:77-38:82)
  
  theorem fine : OK
  9 proof(s) rejected
  
  [2]
--trace : l'arbre de dérivation de chaque théorème, en JSON :
  $ ../bin/poule.exe --trace test01.poule | grep -c '^TRACE {"theorem":"theorem id_and","ok":true'
  1
  $ ../bin/poule.exe --trace poule_errors.poule 2>/dev/null | grep -c '"ok":false'
  9
