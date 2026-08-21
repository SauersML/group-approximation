---
rg: 2
id: dimension-reported-julia-amplitude-return
kind: claim
title: A self-indexing matrix tape need only activate one Julia amplitude return
distinct_from:
  same-model-supercritical-clifford-trigger: that asks the detected matrix size to materialize a Clifford representation larger than the ambient model; this uses the detected size only to choose a deeper Fanizza heat filter and asks for two returned products.
  constant-hs-sound-self-detecting-tape-groupification: that asks for a general runtime-independent semantic compiler; this isolates a strictly smaller payload sufficient for the Fanizza route.
  julia-authenticated-high-spectrum-rank-selector: that asks directly for a finite-coordinate Hall matching into a spectral cutoff; this permits the dimension oracle to choose the cutoff depth endogenously and returns amplitude through cyclic trace instead of a rank matching theorem.
---

OPEN.  Fix the Fanizza instance and its accelerated contractions

```text
B_t=D_R p_t(H_m),             A_t=B_t^*B_t.
```

Construct one finite group-relation gadget with a fixed marked projection
`P` and the following normalized-HS behavior.  After exactifying a fixed
finite packet, let `M_k(C)` be the positive-density multiplicity block
containing `P`.  The Amitsur--Levitzki tape must detect its finite index `k`
and activate a depth `t(k)` with `t(k)->infinity`, together with matrices
`X_k,Y_k` decoded in the same finite model, such that

```text
||Y_k X_k-P||_2 <= omega(Def),
||X_k Y_k-A_(t(k))||_2 <= omega(Def),                (DJA1)
```

where `omega(epsilon)->0` is independent of `k`, `t(k)`, matrix dimension
and simulated runtime.  If the selected packet has density tending to zero,
the fixed mark must already have vanishing normalized HS norm.

This payload is enough.  Finite-dimensional cyclic trace and
`fanizza-heat-return-is-one-cyclic-amplitude-product` give

```text
tr(P)
 <= 2 omega(Def)+C_m/(4t(k)^2).                       (DJA2)
```

Along a canonical microstate sequence, a positive-density copy of a fixed
`r`-dimensional packet has multiplicity `k` tending to infinity with the
ambient dimension.  Hence `t(k)->infinity`, and `(DJA2)` collapses the mark.
The zero-density alternative collapses it directly.

HALT completeness is compatible with the *payload*: on the perfect quotient
`A_t=D_R` for every `t`, so `P=X=Y=D_R` solves every returned product after
countable amplification.  It is nevertheless a separate requirement on the
compiler.  The bare countable algebra `(ALO4)` does not supply a bounded
star-representation: nonvanishing of `p_n` on an infinite algebra does not
give uniformly bounded inverses.  Thus the finite presentation must arrange
the non-triggered infinite phase without imposing those formal inverse
relations or any fixed `(DJA1)` identity in the regular finite von Neumann
algebra.

## Why this is a smaller diagonal challenge

The previously isolated same-model trigger asks a detected `d`-dimensional
model to build a Clifford packet requiring dimension greater than `d`.
Here detection need only choose a scalar accuracy: for example
`t(k)=ceil(log_2(k+1))` already makes the heat remainder tend to zero.  The
terminal payload has two products and no growing all-pairs multiplication
table, no exponential divisibility conclusion and no estimate of the
ambient dimension from the selected corner.

The hard part has not disappeared: direct evaluation of the standard
polynomial and an ordinary Turing history have losses depending on `k` and
runtime, while branching robustly on a vanishing polynomial and preserving a
bounded infinite HALT model are both nontrivial.  The required advance is a
constant-sound local compiler which transports the triggered flag to the two
products in `(DJA1)`.  But its terminal semantic target is strictly weaker
than a supercritical Clifford trigger and is now matched exactly to the
smallest known Fanizza scalar endpoint.

## Attempts

- **Formal inverses are not a bounded trigger.**  Adjoining inverses to every
  `p_n` detects finite dimension algebraically, but gives no bounded
  star-representation for HALT completeness.
- **Direct polynomial evaluation is not robust.**  The degree and coefficient
  mass of `p_k` grow with the endogenous stopping index, so ordinary
  telescoping loses a `k`-dependent factor.
- **Ordinary machine transport is not robust.**  Simulating the instruction
  and heat polynomial step by step accumulates the runtime in the HS bound.
- **Live reduced target.**  PCP-localize only the stopping flag and the two
  product identities `(DJA1)`.  Unlike the Clifford route, the payload needs
  no growing multiplication table; the remaining question is whether this
  reduction also removes the runtime dependence while retaining a bounded
  infinite non-triggered model.
