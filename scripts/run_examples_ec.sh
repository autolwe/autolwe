#! /bin/sh

# set EC_CMD to override
if [ -z "${EC_CMD}" ]; then
  EC_CMD="$HOME/easycrypt/ec.native"
fi

# add required includes
EC_CMD="$EC_CMD -I ZooLib -I extraction"

FAILED_ZC=""
FAILED_EC=""
SUCCESS_ZC=""
SUCCESS_EC=""

for file in examples/ok/*.zc; do
  printf "File $file: \n"
  before=$(date +%s)
  if ! ./zoocrypt.native $file 2>&1 | grep --colour=always -i -e 'Finished Proof' -e 'EasyCrypt proof script.extracted'; then
    FAILED_ZC="$FAILED_ZC $file"
  else
    SUCCESS_ZC="$SUCCESS_ZC $file"
    name=`basename $file`
    ec_file=extraction/${name%.zc}.ec
    if ! $EC_CMD ${ec_file}; then
      FAILED_EC="$FAILED_EC $ec_file"
    else
      SUCCESS_EC="$SUCCESS_EC $ec_file"
    fi
  fi
  after=$(date +%s)
  dt=$((after - before))
  printf  "  \e[1;32m$dt seconds\e[1;0m\n"
done

test -n "$SUCCESS_ZC" && printf "\n\e[1;32mSucceed ZooCrypt: $SUCCESS_ZC\e[1;0m"
test -n "$FAILED_ZC" && printf  "\n\e[1;31mFailed ZooCrypt: $FAILED_ZC\e[1;0m"
test -n "$SUCCESS_EC" && printf "\n\e[1;32mSucceed EasyCrypt: $SUCCESS_EC\e[1;0m"
test -n "$FAILED_EC" && printf  "\n\e[1;31mFailed EasyCrypt: $FAILED_EC\e[1;0m"
echo ""
exit 0
