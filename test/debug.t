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
--debug affiche tous les éléments du toplevel (5 ici), chacun préfixé par sa passe :
  $ ../bin/main.exe --eval --debug parsing t_debug.ml | grep -c "^parsing"
  5
  $ ../bin/main.exe --eval --debug bindings t_debug.ml | grep -c "^bindings"
  5
  $ ../bin/main.exe --eval --debug typer t_debug.ml | grep -c "^typerval"
  4
