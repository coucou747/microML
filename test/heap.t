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
le tas s'adapte à la mémoire disponible (ici 1 Gio de mémoire virtuelle) :
  $ ../bin/main.exe --runtime ../runtime/libruntime.a t01.ml -o t01_small.exe -I ../runtime/include > /dev/null 2>&1
  $ (ulimit -v 1048576; ./t01_small.exe)
  2
