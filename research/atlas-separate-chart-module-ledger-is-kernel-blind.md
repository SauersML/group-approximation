---
rg: 2
id: atlas-separate-chart-module-ledger-is-kernel-blind
kind: claim
title: Separate-chart H6/H18 module ledgers are blind to the two augmented kernel strata
distinct_from:
  atlas-fixed-packet-arithmetic-has-no-hs-gap: that kills finite arithmetic refinements of a fixed multiplicity profile after amplification; this proves that even the complete modular isomorphism types of all separately restricted chart modules are constant on the relative-gauge space.
  atlas-a4-19243-type-relaxation-has-regular-zero: that treats complex regular type profiles and a collision S3 marginal; this treats the defining-characteristic repeated-natural-module gauge and both exact kernel strata.
  atlas-full-kernel-strata-rank-separation: that asks for a normalized-rank separation of two mixed word-zero strata; this excludes all invariants factoring through separate-chart subgroup modules and identifies the genuinely mixed data that remain available.
---

Let `V=F2^4` be the natural `A8=GL4(2)` module, let `M=F2^m`, and put
`E=V tensor M`.  Fix any finite list `L` of marked subgroups of one chart;
in particular `L` may contain all recorded copies of `H6`, `H18`, `A4`, and
`A8` used by the packet.  For a relative gauge `T in GL(E)`, compare the two
chart representations

```text
rho_m(g)=rho_V(g) tensor I_M,
rho_m^T(g)=T^-1 rho_m(g) T.                           (SML1)
```

For every `K in L`, independently of `T`,

```text
Res_K(rho_m^T) ~= Res_K(rho_m) ~= Res_K(V) tensor M.  (SML2)
```

Consequently all of the following data are constant on the entire packet
gauge space, and hence take identical values on its collision-zero and
q14-zero strata:

```text
the full F2[K]-module isomorphism type,
its composition-factor/K0 class,
dim Fix_K(E),
dim End_K(E),
and every invariant factoring through finitely many such data.             (SML3)
```

In particular, if `f_K=dim Fix_K(V)` and
`e_K=dim_F2 End_K(V)`, then

```text
dim Fix_K(E)=m f_K,
dim End_K(E)=m^2 e_K.                                 (SML4)
```

The statement includes extension data invisible to modular `K0`: the whole
restricted module, not merely its semisimplification, is fixed.  Thus no
additive charge assembled from the existing **separate-chart** H6/H18/A4/A8
fixed-space ledger can prove
`atlas-full-kernel-strata-rank-separation`.  Determinant, Dieudonne, parity,
or other finite residues do not help: over `F2` the ordinary determinant has
no nontrivial value, and in any finite residue target common amplification
kills the residue without changing normalized rank density.

There is a sharp boundary to this no-go.  A genuinely mixed coordinate such
as

```text
mu_(K,L)(T)=dim(Fix_K(E) intersect T^-1 Fix_L(E))      (SML5)
```

is not determined by `(SML2)`.  It is additive under direct sums and obeys

```text
|mu_(K,L)(T)-mu_(K,L)(T')| <= rank(T-T').             (SML6)
```

Hence mixed intersection dimensions have exactly the formal properties
needed for a rank-metric charge.  What is still missing is a kernel-sensitive
inequality forcing different normalized values on **every** collision-zero
and q14-zero packet gauge.  The multiplicity-two residual-rank spectrum does
not supply such an inequality, because it records only the two word ranks,
not the mixed intersection modules.

The surviving invariant search is therefore strictly narrower: it must use a
subgroup or module containing letters from both charts (equivalently, a
relative intersection/extension/holonomy datum).  No invariant of the
individual H6/H18 packet modules can separate the strata.
