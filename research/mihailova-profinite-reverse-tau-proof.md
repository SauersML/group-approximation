---
rg: 2
id: mihailova-profinite-reverse-tau-proof
kind: route
title: Extract a finitely generated dense subgroup inside N and apply arbitrary-modulus super-approximation
target: mihailova-kernel-has-profinite-reverse-tau-gap
requires:
  - sln-z-thin-codense-tau-pair
  - mihailova-coset-wreath-sofic-action-boundary
---

## 1. The whole kernel is profinitely dense

For every finite quotient `q:L->F`, profinite density of `E` gives
`q(E)=q(L)`.  Since `N normal E`, `q(N) normal q(E)`, and

```text
q(E)/q(N)
```

is a finite quotient of `Q=E/N`.  The hypothesis on `Q` makes it trivial.
Hence `q(N)=q(L)` for every `q`, so `N` is dense in `Lhat`.

## 2. A finite subset of N is already profinitely dense

First `N` is Zariski dense in `SL_3`.  Indeed `E` is Zariski dense, and the
Zariski closure of `N` is normalized by `E`, hence by `SL_3`.  Simplicity of
`SL_3` and nontriviality of the torsion-free kernel exclude a central closure.
Noetherianity therefore supplies a finite `S_0<N` for which
`Gamma_0=<S_0>` is Zariski dense.

Strong approximation for finitely generated Zariski-dense subgroups of the
simply connected group `SL_3`, together with the congruence subgroup property,
says that the closure `H_0` of `Gamma_0` in `Lhat` is open.  Let `C` be the
open normal core of `H_0`.  Since `N` is dense, its image in the finite group
`Lhat/C` is all of that group.  Choose finitely many `t_1,...,t_a in N` whose
images generate `Lhat/C`.  Then

```text
Gamma=<S_0,t_1,...,t_a> < N                            (PRP1)
```

is dense in `Lhat`: its closure contains `H_0`, hence `C`, and surjects onto
`Lhat/C`.  Let `S` be a finite symmetric generating set for `Gamma`.

## 3. Super-approximation gives the uniform reverse gap

Bourgain--Varju, *Expansion in SL_d(Z/qZ), q arbitrary*, Invent. Math. 188
(2012), 151--173 ([arXiv:1006.3365](https://arxiv.org/abs/1006.3365)), proves
that the Cayley graphs of the reductions of a fixed Zariski-dense subgroup
of `SL_d(Z)` form a uniform expander family over every modulus.  Here
profinite density in `(PRP1)` makes those reductions the full groups
`SL_3(Z/qZ)`.

Every finite-dimensional unitary representation of `L` has finite image by
Margulis superrigidity, and every finite quotient factors through a congruence
quotient by Bass--Milnor--Serre CSP.  The expander spectral gap passes to
quotients and to every nontrivial irreducible representation (each occurs in
the regular representation).  Decomposing `v=P_rho v+v_0` therefore gives
one `kappa>0`, independent of `rho`, with

```text
max_(s in S)||rho(s)v-v|| >= kappa ||v_0||,            (PRP2)
```

which is `(PRT2)`.

## 4. Excluding the coset coefficient

Suppose unit vectors `xi_j` in finite-image representations `rho_j` had
coefficients converging to `1_N`.  Since `S<N`,

```text
||rho_j(s)xi_j-xi_j||^2
 =2-2 Re <rho_j(s)xi_j,xi_j> ->0                       (PRP3)
```

for every `s in S`.  Equation `(PRT2)` makes `xi_j` converge in norm to its
`L`-invariant projection.  Consequently

```text
<rho_j(g)xi_j,xi_j> ->1                                (PRP4)
```

for every fixed `g in L`.  Taking any `g notin N` contradicts the required
limit `1_N(g)=0`.  This proves `(PRT3)`.

Finally, Peter--Weyl identifies finite-image representations of `L` with the
finite-dimensional continuous representations of `Lhat`.  The usual cyclic
weak-containment criterion identifies pointwise approximation of the
positive-definite coefficient `1_N` by their finite direct sums with
`(PRT4)`.  This proves the compact/profinite formulation as well.

