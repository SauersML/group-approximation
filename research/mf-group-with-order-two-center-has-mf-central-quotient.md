---
rg: 2
id: mf-group-with-order-two-center-has-mf-central-quotient
kind: claim
title: A countable MF group whose center is a single involution has MF quotient by its center
distinct_from:
  central-extension-twisted-sector-criterion: that goes up, deciding MF of a central order-two extension from a twisted sector over the quotient; this goes down, from MF of the extension to MF of the quotient, by an explicit block construction with no twisted sector.
  central-quotients-of-residually-finite-groups-are-mf: that starts from a residually finite group and allows any central subgroup; this starts from an MF group and needs the central subgroup to be the whole center and of order two, which is exactly what the injectivity step uses.
  integral-jacobson-mf-radical-is-all-or-nothing: that is the restricted dichotomy for the integral Jacobson group; this is the general lemma that turns its whole-group form into the statement that the strong reading is equivalent to the non-MF alternative.
artifacts:
  - research/artifacts/jacobson-exact-torsion-radical-and-integral-dichotomy-2026-09-09.md
---

**ESTABLISHED.**  Let `Gamma` be a countable MF group with

```text
Z(Gamma) = <c>,      c^2 = 1,  c != 1.                               (CQ1)
```

Then `Gamma / <c>` is MF.

**Mechanism.**  From a faithful operator-norm asymptotic representation
`V_j` of `Gamma`, round `V_j(c)` to an exact self-adjoint unitary `J_j`,
average and take polar parts so that every `V_j(g)` becomes a unitary
`W_j(g)` commuting exactly with `J_j`, and then replace each sign block
`W_j^(+-)(g)` by `W_j^(+-)(g) (x) conj(W_j^(+-)(g))`.  The sign of `c`
disappears on each block, multiplicativity is preserved up to a factor
two, and an element killed by the new representation is asymptotically
scalar on both blocks, hence asymptotically commutes with every
`W_j(h)`, hence is central by faithfulness of the original
representation.  So the kernel of the new corona representation is
exactly `<c>`.  All estimates are dimension free; no compressor,
property (T), or change of matrix norm enters.

**What it says for the integral Jacobson group.**  `G = EL_4(Z<s,t | ts=1>)`
has `Z(G) = C_G(SL_fin(Z)) = {+-I}` with `-I = w_12^2 w_34^2` elementary
and not finitary.  So `G` is MF iff the centerless `P = G/{+-I}` is MF
(the reverse direction is `G -> P x T`, `T = G/SL_fin(Z)`, injective
since `{+-I} cap SL_fin(Z) = 1`), and an MF homomorphism of `G` that is
injective on `SL_fin(Z)` may have kernel exactly `{+-I}`.  The strong
reading "every MF homomorphism of `G` is injective or kills `SL_fin(Z)`"
is therefore equivalent to "`G` is not MF" and is not a reduction of
that question; see `integral-jacobson-mf-radical-is-all-or-nothing`.

**Extension not recorded as a claim.**  The same construction works for
any finite center once the restriction of the asymptotic representation
to the center is made exact (finite groups are operator-norm stable) and
the blocks are indexed by characters; only the order-two case is proved
on the route.

Derivation: `mf-group-with-order-two-center-has-mf-central-quotient-proof`.
