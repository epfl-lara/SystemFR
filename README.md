# System FR [![Build Status][larabot-img]][larabot-ref]

![System FR's logo](logo/small.png?raw=true)

### Description

This project aims to formalize in Coq part of the [Stainless project](https://github.com/epfl-lara/stainless). It describes a call-by-value lambda-calculus and defines a rich type system (based on computations) that describes behaviors of lambda-calculus terms. Supported types include: System F polymorphism, recursive types, infinite intersections, refinement and dependent types, equality types.

### Requirements

The proofs require Coq and Coq-Equations, which can be installed using `opam` with the `coq` and `coq-equations` packages. Some instructions are available [here](https://github.com/coq/coq/wiki/Installation-of-Coq-on-Linux) and [there](https://github.com/mattam82/Coq-Equations).

* Coq 8.12.2
* Coq-Equations 1.2.3+8.12

### Compiling the Proofs

After installing Coq, you can compile the proofs using:

```
./configure
make -j4     # should take around 25 minutes
```

### Overview of the proofs

All trees (for terms and for types) are defined in [Trees.v](https://github.com/epfl-lara/SystemFR/blob/master/Trees.v). The operational semantics is given in [SmallStep.v](https://github.com/epfl-lara/SystemFR/blob/master/SmallStep.v). The semantic definition of types is given in [ReducibilityDefinition.v](https://github.com/epfl-lara/SystemFR/blob/master/ReducibilityDefinition.v). We then prove soundness of inference rules for these types in the `Erased*.v` files (for erased terms) and in the `Annotated*.v` files (for annotated terms).

The file [dependencies.pdf](https://github.com/epfl-lara/SystemFR/blob/master/dependencies.pdf) has an overview of the dependencies between all files.


### Proofs for Scala Dependent Types project


Total: 5/26

#### Normalization Rules (3/9)

* NBase: `open_nbase1` and `open_nbase2` in NormalizationBase.v (OK)
* NExists2: `open_nexists_2` in NormalizationExists.v (OK)
* NPi: `open_npi` in NormalizationPi.v (OK)

* NSing: NormalizationSing.v (WIP)
* NExists1: `open_exists_1` in NormalizationExists.v (WIP)
* NCons: NormalizationCons.v (WIP)
* NMatch1: NormalizationMatch.v (WIP)
* NMatch2: NormalizationMatch.v (WIP)
* NMatch3: NormalizationMatch.v (WIP)


#### Inference Rules (2/7)

* TNil: `open_tnil` in ErasedList.v (OK)
* TCons: `open_tcons` in ErasedList.v (OK)

* TMatch: ErasedList.v (WIP)
* TAbs: (WIP)
* TFix: (WIP)
* TMatch: (WIP)
* TCheck: (WIP)


#### Subtyping Rules (0/9)

* SubTop: (WIP)
* SubRefl: (WIP)
* SubPi: (WIP)
* SubSing: (WIP)
* SubCons: (WIP)
* SubMatch: (WIP)
* SubExistsLeft: (WIP)
* SubExistsRight: (WIP)
* SubNorm: (WIP)



[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/SystemFR/status/master
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/SystemFR/builds
