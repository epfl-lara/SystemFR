# System FR [![Build Status][larabot-img]][larabot-ref]

### Description

This project aims to formalize in Coq part of the [Stainless project](https://github.com/epfl-lara/stainless). It describes a (standard) call-by-value lambda-calculus and defines a rich type system (based on computations) that describes behaviors of lambda-calculus terms. Supported types include: System F polymorphism, recursive types, infinite intersections, refinement and dependent types, equality types.

### Requirements

The proofs require Coq and Coq-Equations, which can be installed using `opam` with the `coq` and `coq-equations` packages. Some instructions are available [here](https://github.com/coq/coq/wiki/Installation-of-Coq-on-Linux) and [there](https://github.com/mattam82/Coq-Equations).

* Coq 8.10.2
* Coq-Equations 1.2+8.10

### Compiling the Proofs

After installing Coq, you can compile the proofs using:

```
./configure
make -j4     # takes around 27 minutes
```

### Overview of the proofs

All trees (for terms and for types) are defined in [Trees.v](https://github.com/epfl-lara/SystemFR/blob/master/Trees.v). The operational semantics is given in [SmallStep.v](https://github.com/epfl-lara/SystemFR/blob/master/SmallStep.v). The semantic definition of types is given in [ReducibilityDefinition.v](https://github.com/epfl-lara/SystemFR/blob/master/ReducibilityDefinition.v). The rules which are proven sound with respect to the definitions of the types are given in [Typing.v](https://github.com/epfl-lara/SystemFR/blob/master/Typing.v). The theorem showing that these rules are sound is given in [Reducibility.v](https://github.com/epfl-lara/SystemFR/blob/master/Reducibility.v).

The file [dependencies.pdf](https://github.com/epfl-lara/SystemFR/blob/master/dependencies.pdf) has an overview of the dependencies between all files.

[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/SystemFR/status/master
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/SystemFR/builds
