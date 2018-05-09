#! /bin/bash

SOME_FAIL=""

function ok_tests() {
  echo 
  echo "*******************************************************************"
  echo "Running examples and ok tests!"
  echo

  FAILED=""
  OK=""
  for file in \
              examples/ok/scheme-correct/*.zc \
              examples/ok/assumptions/*.zc \
              examples/ok/*.zc \
              test/ok/*.zc \
              ; do \
    printf "File $file: \n"
    before=$(date +%s)
    if ! ./autognp $file 2>&1 | \
         grep --colour=always -i \
           -e 'Finished Proof' -e 'EasyCrypt proof script.extracted'; then
      FAILED="$FAILED\n  $file"
    else
      OK="$OK\n  $file"
    fi
    after=$(date +%s)
    dt=$((after - before))
    printf  "  \e[1;32m$dt seconds\e[1;0m\n"
    done

  printf "\nFailed: $FAILED"
  printf "\nOK: $OK"
  SOME_FAIL="$SOME_FAIL$FAILED"
}

function fail_tests() {
  echo
  echo
  echo "*******************************************************************"
  echo "Running mustfail tests!"
  echo

  FAILED=""
  OK=""
  for file in test/fail/*.zc; do
    ERR=`grep ERROR $file | sed 's/ERROR: //'`
    printf "Testing $file, expecting error ''$ERR''\n"  
    if ! ./autognp $file 2>&1 | \
         grep -F "$ERR"; then
      FAILED="$FAILED\n  $file"
    else
      OK="$OK\n  $file"
    fi
  done
  printf "\nFailed:$FAILED"
  printf "\nOK:$OK\n"
  SOME_FAIL="$SOME_FAIL$FAILED"
}

ok_tests
fail_tests
if test -z "$SOME_FAIL"; then
  printf "\nAll tests executed successfully.\n";
else
  printf "\nSome tests failed: $SOME_FAIL\n"
fi
