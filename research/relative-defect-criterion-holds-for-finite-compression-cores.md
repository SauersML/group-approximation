---
rg: 2
id: relative-defect-criterion-holds-for-finite-compression-cores
kind: claim
title: The relative defect criterion holds for rigid pairs with a finite compression core, including the Kun--Thom Theorem E pairs
distinct_from:
  sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels: that is the open relative criterion for arbitrary rigid pairs; this proves it for pairs where some compressor has a finite compression core, which forces every admissible kernel to be finite.
  sofic-quotients-by-finite-normal-subgroups-are-sofic: that is quotient permanence for finite kernels; this combines it with the confinement of normal kernels to compression cores.
---

**ESTABLISHED.** Let `H` be a countable sofic group, `M` a normal subgroup of
`H`, and `Gamma <= G <= H` a rigid pair with `M <= Gamma`. For a compressor `t`
of `Gamma` put

```text
K_t(Gamma) = intersection over n >= 0 of t^n Gamma t^-n.
```

1. **Kernels sit in every compression core.** `M <= K_t(Gamma)` for every
   compressor `t`. Also `M` lies in every conjugate of `Gamma` by elements of
   `H`.
2. **A finite core forces the criterion.** If some `K_t(Gamma)` is finite, then
   `M` is finite. So for all `g` in `G`, `gamma` in `Gamma` and `z` in `H` with
   `[z, Gamma] <= M`, the commutator `[g z g^-1, gamma]` lies in `M`.
3. **Kun--Thom Theorem E pairs have finite cores.** Take
   `Gamma = EL_r(F_q[x_1..x_d])` inside
   `G = EL_r(F_q[x^(+-1)]) semidirect SL_d(Z)`, with `r, d >= 3`
   (`kun-thom-nonsofic-wreath`). The matrix `A = (min(i,j))` lies in `SL_d(Z)`,
   acts by the monomial substitution `x^v -> x^(Av)`, and compresses `Gamma`.
   Its core satisfies `K_A(Gamma) <= GL_r(F_q)`.

So a sofic group containing a Theorem E pair cannot refute
`sofic-groups-kill-rigid-defects-modulo-kazhdan-kernels` through that pair, with
any normal kernel. The congruence-type kernels `EL_r(R, I)` are not even
admissible: for a nonzero ideal `I` of the Laurent ring they contain root
elements with non-polynomial entries, so they do not lie in `Gamma`.

## What a counterexample needs

Suppose a sofic host `H`, a normal Kazhdan `M`, and a rigid pair containing `M`
violate the relative criterion. Then:

- `M` is infinite, and every compression core of the pair is infinite;
- `H/M` carries a rigid defect, so it is nonsofic, and `H` does not split over
  `M`;
- if `H` is residually finite, `M` is not closed in the profinite topology.
  Otherwise `H/M` is residually finite, hence sofic.

The Belegradek--Osin cover `hyperbolic-kazhdan-cover-of-leavitt-unit-group` has
all three features. No residually finite, linear or amenable-edge amalgam host
is known to have them. See also
`kazhdan-normal-subgroups-of-splittings-and-graph-products`.

Derivation: `relative-defect-finite-compression-core-proof`.
