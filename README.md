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


The typing algorithm maintains the following invariants, which are not proven in Coq:

* The terms and types appearing in goals/context satisfy some well-formedness conditions
* The types are appearing in goals/context are non-empty
* Inferred types are always syntactically singletons

We prove the following properties and the soundness of the rules used in our algorithm.

Properties: 0/3
Rules: 21/26
Total: 21/29

#### Required properties (0/3)

* `widen` gives a larger type `widen_open_subtype` in [InferApp.v](InferApp.v) (WIP)
* `delta_beta_reduction` gives observationally equivalent terms: `delta_beta_obs_equiv` in [NormalizationSing.v](NormalizationSing.v) (WIP)
* `\mathcal{N}` returns an equivalent type (WIP)


#### Normalization Rules (5/9)

* NBase: `open_nbase1` and `open_nbase2` in [NormalizationBase.v](NormalizationBase.v)
* NExists2: `open_nexists_2` in [NormalizationExists.v](NormalizationExists.v)
* NPi: `open_npi` in [NormalizationPi.v](NormalizationPi.v)
* NCons: `open_ncons` in [NormalizationList.v](NormalizationList.v)
* NSing: `open_nsing` in [NormalizationSing.v](NormalizationSing.v)

* NMatch1: NormalizationMatch.v (WIP)
* NMatch2: NormalizationMatch.v (WIP)
* NMatch3: NormalizationMatch.v (WIP)
* NExists1: `open_exists_1` in NormalizationExists.v (WIP)


#### Inference Rules (8/8)

* TVar: `open_tvar` in [InferMisc.v](InferMisc.v)
* TNil: `open_tnil` in [ErasedList.v](ErasedList.v)
* TCons: `open_tcons` in [ErasedList.v](ErasedList.v)
* TCheck: `open_subtype_reducible` in [ReducibilitySubtype.v](ReducibilitySubtype.v)
* TAbs: `open_tabs` in [InferMisc.v](InferMisc.v)
* TFix: `open_tfix` in [InferFix.v](InferFix.v)
* TMatch: `open_tmatch` in [InferMatch.v](InferMatch.v)
* TApp: `open_tapp` in [InferApp.v](InferApp.v)


#### Subtyping Rules (8/9)

* SubTop: `open_subtype` in [SubtypeMisc.v](SubtypeMisc.v)
* SubRefl: `open_subrefl` in [SubtypeMisc.v](SubtypeMisc.v)
* SubSing: `open_subsing` in [SubtypeMisc.v](SubtypeMisc.v)
* SubCons: `open_subcons` in [SubtypeList.v](SubtypeList.v)
* SubPi: `open_subpi` in [SubtypePi.v](SubtypePi.v)
* SubExistsLeft: `open_sub_exists_left` in [SubtypeExists](SubtypeExists.v)
* SubExistsRight: `open_sub_exists_right` in [SubtypeExists](SubtypeExists.v)
* SubMatch: `open_submatch` in [SubtypeMatch.v](SubtypeMatch.v)

* SubNorm: (WIP)



[larabot-img]: http://laraquad4.epfl.ch:9000/epfl-lara/SystemFR/status/master
[larabot-ref]: http://laraquad4.epfl.ch:9000/epfl-lara/SystemFR/builds
