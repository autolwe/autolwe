#! /bin/sh

find src -name \*.ml | grep -v "Test" | while read FILE; do
  test -f ${FILE}i || echo $FILE
done