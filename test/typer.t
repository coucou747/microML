  $ buildandrun(){
  > exe="${1%.*}.exe"
  > ../bin/main.exe --runtime ../runtime/libruntime.a "$1" -o "$exe" -I ../runtime/include > /dev/null 2>&1 || true
  > ./$exe
  > }
  $ evalme(){
  > ../bin/main.exe "$1" --eval
  > }
  $ nocompile(){
  > ../bin/main.exe --runtime ../runtime/libruntime.a "$1" -o "$exe" -I ../runtime/include > /dev/null 2>&1
  > echo $?
  > }
programmes mal typés :
  $ nocompile t_notype5.ml
  2
  $ nocompile t_notype6.ml
  2
  $ nocompile t_notype7.ml
  2
rejetés par le typer (et pas plus tard à l'exécution) :
  $ ../bin/main.exe --eval t_notype5.ml 2>&1 | grep -c "Cannot unify"
  2
  $ ../bin/main.exe --eval t_notype6.ml 2>&1 | grep -c "Cannot unify"
  2
  $ ../bin/main.exe --eval t_notype7.ml 2>&1 | grep -c "type rec"
  2
généralisation (let et let rec polymorphes, lambda monomorphe) :
  $ buildandrun t_generalize.ml
  118
  $ evalme t_generalize.ml
  118
deux appels récursifs sous + (le typer bouclait) :
  $ buildandrun t_fib.ml
  6765
  $ evalme t_fib.ml
  6765
