# Guide for this example

Read files in the following order:
1. Fixed size arrays: [add4.jazz](add4.jazz)
1. Global `param`s and arrays: [addN.jazz](addN.jazz)
1. Optimizing one spill: [addNv2.jazz](addNv2.jazz)

Then take a look into the Makefile to see how to compile Jasmin code into assembly and extract Easycrypt.

After that, that a look at the following files:

1. Easycrypt extracted code of `add` function: [addN_s.ec](addN_s.ec)
1. Easycrypt model for constant-time verification: [addN_ct.ec](addN_ct.ec)
1. Constant-time proof of the `add` function: [addN_ct_proof.ec](addN_ct_proof.ec)
1. Making `add` non constant time: [addNv3.jazz](addNv3.jazz)
1. Fixing the proof (declare inputs as public): [addNv3_ct_proof.ec](addNv3_ct_proof.ec)

# Other examples

Other examples can be found in Jasmin GitHub repository (`glob_array3` branch supports global array variables):
* [Jasmin GitHub 1](https://github.com/jasmin-lang/jasmin/tree/glob_array3/compiler/examples)
* [Jasmin GitHub 2](https://github.com/jasmin-lang/jasmin/tree/master/compiler/tests/success)
* [libjc](https://github.com/tfaoliveira/libjc/tree/glob_array3/src) -- most example require the usage of a preprocessor (gpp is used in the makefiles)

# Installing Jasmin
To get the Jasmin compiler running you can read [Installation](https://github.com/jasmin-lang/jasmin/wiki/Installation-instructions).
I usually run the following set of commands: ('clean' Ubuntu, for instance):
```
curl https://nixos.org/nix/install | sh # reading the instructions in nix website before c&p is recommended
git clone git@github.com:jasmin-lang/jasmin.git -b glob_array3
cd jasmin/
nix-shell
cd compiler/
make CIL
make
exit
cd ../
sudo install -b -D `pwd`/compiler/jasminc /usr/local/bin/ # or something else that suits your needs
```

There is also a [VagrantFile](https://github.com/tfaoliveira/libjc/blob/glob_array3/env/Vagrantfile) in `libjc` repository (not sure if it still works) that contains some commands that were used at some point in time to install [EasyCrypt](https://github.com/EasyCrypt/easycrypt) and other dependencies. 
