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
comparaisons dans le runtime C :
  $ buildandrun t_compare.ml
  10110101
  $ evalme t_compare.ml
  10110101
