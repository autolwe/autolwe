# Installation

The current version of AutoG&P requires the C++ libraries `NTL` and
`libfactory`, the Ocaml compiler and various Ocaml libraries.
To use the interactive mode, Emacs and an extended version of
Proof General are required. To install all dependencies, proceed as follows.

## Ocaml compiler and C++ build dependencies

### OS X

We recommend using [homebrew](http://brew.sh) to install most of the dependencies.
The required commands are:

```
brew install opam
brew install libtool
brew install gmp
brew install libffi
brew link --force libffi
brew install pkg-config
```

### Linux

Most distributions should offer packages for `gmp` and `libffi`. Make sure to
install the development packages.
Please follow the instructions on
[https://opam.ocaml.org/doc/Install.html](https://opam.ocaml.org/doc/Install.html)
to install the opam package manager for Ocaml.

## C++ libraries

To get the required C++ libraries, follow these instructions.

1) download and install NTL from
http://www.shoup.net/ntl/ntl-9.7.1.tar.gz 

**On Linux:**
```
cd src
./configure NTL_GMP_LIP=on SHARED=on
make
sudo make install
```

**On OS X:**
```
cd src
./configure NTL_GMP_LIP=on SHARED=on LIBTOOL="glibtool --tag=CC"
make
sudo make install
```

2) download and install libfactory from
http://www.mathematik.uni-kl.de/ftp/pub/Math/Factory/factory-4.0.2.tar.gz

**On Linux and OS X:**
```
./configure --disable-streamio --without-Singular --disable-static
make
sudo make install
```

## Compiling AutoG&P

We recommend cloning the AutoG&P repository, compiling the tool, and
running it directly from the cloned directory. To achieve this, perform
the following steps:

Clone the repos
```
# clone the AutoG&P repo
git clone https://github.com/ZooCrypt/AutoGnP.git
# clone the extended Proof General mode
git clone https://github.com/ZooCrypt/PG.git PG-AutoGnP
```

Compile and test AutoG&P:
```
cd AutoGnP
# tell the opam package manager to use the cloned repo
opam pin add autognp . -n
# install all Ocaml dependencies
opam install autognp --deps-only
# compile autognp
make
# run test-suite
make test-examples
```

Compile Proof General:
```
cd PG-AutoGnP
make
# use make EMACS=/Applications/Emacs.app/Contents/MacOS/Emacs
# if make fails
```

## Configuring Proof General

Add the following lines to your `.emacs` with `GIT_DIR` replaced
by the directory containing the cloned repos.

```
(load "GIT_DIR/PG-AutoGnP/generic/proof-site.el")
(setq autognp-prog-name "GIT_DIR/AutoGnP/autognp -emacs")
```

Now, you can test everything by opening `examples/ok/bb1.zc` in
Emacs and executing regions of the file using `Ctrl-c Ctrl-enter`.

# Examples

The examples can be found in `examples/ok`.

# Status of current version

Currently, the extraction to EasyCrypt is disabled.
