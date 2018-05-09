#/bin/bash

FILE=$1

if [ "$1" = "" ]; then
    echo "$0 <module>"
    exit 1
fi

set -x

for f in src/$1.ml; do
  ocamlbuild -use-menhir "${f%.*}.inferred.mli";
done

echo "mli created, use:"
echo "cp _build/src/$FILE.inferred.mli src/$FILE.mli"

#for f in _build/src/$1.mli; do
#  name=`basename "${f%.*.*}.mli"`;
#  test -f $name || cp $f $name;
#done
