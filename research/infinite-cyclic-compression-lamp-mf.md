---
rg: 2
id: infinite-cyclic-compression-lamp-mf
kind: claim
title: Integer lamps over a compressed site space form an MF group
distinct_from:
  commuting-lamp-quotient-not-mf: That claim shows binary lamps over a compressed Kazhdan site space obstruct MF; this one shows infinite-cyclic lamps over the same kind of site space admit a faithful corona model, so the two lamp orders sit on opposite sides of an exact phase boundary.
  hs-invisibility-inflation-no-go: That claim inflates an existing faithful representation; this one constructs a faithful representation of a group with a nontrivial intrinsic compression defect from scratch.
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
---

Credit: external review session (2026-08-15, unrefereed); architecture and
all displayed estimates audited by this session.

Let `H` be countable residually finite, `L <= H` finitely generated,
`L_1 = t L t^{-1} < L`, and `X = H/L_1`.  Then the restricted wreath
product

```text
W_Z = Z^(X) semidirect H
```

is MF.  The root lamp `c` satisfies `[L_1, c] = 1`, its `L`-conjugates
commute pairwise, and `[g, c] != 1` for `g in L \ L_1` — a genuine
nontrivial intrinsic compression-centralizer defect surviving inside a
faithful MF group.

**Consequences.**  The statement "the intrinsic compression-centralizer
defect lies in the MF radical" is FALSE without a spectral or rigidity
detector: `z = t^{-1} c t` centralizes `L`, `t z t^{-1} = c`, and
`[c, g]` is literally an intrinsic-defect generator.  With `L` Kazhdan
this yields the strict radical gap `mf-vs-tracial-radical-strict-gap`.
The mechanism — slow phase ramps along compressed word length in finite
quotients, with spatially separated bumps for distinct sites — is the same
diffuse wall as `corona-commutant-growth-witness`, now realized by group
elements.
