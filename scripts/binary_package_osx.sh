#!/bin/bash

set -x
set -e

ZOODIR=`pwd`
DEST=/var/chroot/zoocrypt

test -d $DEST && exit 1
mkdir $DEST
mkdir $DEST/bin
mkdir $DEST/etc
mkdir $DEST/myexamples
mkdir $DEST/extraction
mkdir $DEST/lib

cp wszoocrypt.native $DEST/bin
cp zoocrypt.native $DEST/bin
cp scripts/wszoocrypt $DEST
cp etc/log_bolt.config $DEST/etc
cp $ZOODIR/_build/c_src/libfactorystubs.so $DEST/lib
cp -a examples $DEST
cp -a test $DEST
cp -a web $DEST
cp -a ZooLib $DEST

cd $DEST
mkdir usr
cp -a /usr/lib usr

# copy over libraries

cp /usr/local/lib/libfactory-4.0.1.dylib \
   /usr/local/lib/libgmp.10.dylib \
   /usr/local/lib/libntl.5.dylib \
   /usr/local/lib/libmpfr.4.dylib \
   /usr/local/lib/libflint.dylib \
   /usr/local/opt/libffi/lib/libffi.6.dylib \
   lib

LIBDIR="@executable_path/../lib/"

# wszoocrypt
install_name_tool -change /usr/local/opt/libffi/lib/libffi.6.dylib $LIBDIR/libffi.6.dylib bin/wszoocrypt.native
install_name_tool -change /usr/local/lib/libgmp.10.dylib           $LIBDIR/libgmp.10.dylib bin/wszoocrypt.native
install_name_tool -change /usr/local/lib/libfactory-4.0.1.dylib    $LIBDIR/libfactory-4.0.1.dylib bin/wszoocrypt.native
install_name_tool -change _build/c_src/libfactorystubs.so          $LIBDIR/libfactorystubs.so bin/wszoocrypt.native

# zoocrypt
install_name_tool -change /usr/local/opt/libffi/lib/libffi.6.dylib $LIBDIR/libffi.6.dylib bin/zoocrypt.native
install_name_tool -change /usr/local/lib/libgmp.10.dylib           $LIBDIR/libgmp.10.dylib bin/zoocrypt.native
install_name_tool -change /usr/local/lib/libfactory-4.0.1.dylib    $LIBDIR/libfactory-4.0.1.dylib bin/zoocrypt.native
install_name_tool -change _build/c_src/libfactorystubs.so          $LIBDIR/libfactorystubs.so bin/zoocrypt.native

# libfactorystub
install_name_tool -change /usr/local/lib/libfactory-4.0.1.dylib $LIBDIR/libfactory-4.0.1.dylib lib/libfactorystubs.so

# libfactory
for L in libflint.dylib libmpfr.4.dylib libntl.5.dylib libgmp.10.dylib; do 
  for M in libfactory-4.0.1.dylib libflint.dylib libmpfr.4.dylib libntl.5.dylib libgmp.10.dylib; do
    install_name_tool -change /usr/local/lib/$L $LIBDIR/$L lib/$M
  done
done

# test that zoocrypt works
chroot . ./bin/zoocrypt.native examples/ok/cramer_shoup_crush.zc

# create tarball
rm -rf $DEST/usr
cd $DEST/..
DATE=`date "+%d-%m-%y"`
tar cfz /tmp/zoocrypt-mac-$DATE.tar.gz zoocrypt

