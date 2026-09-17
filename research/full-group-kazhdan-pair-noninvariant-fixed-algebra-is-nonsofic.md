---
rg: 2
id: full-group-kazhdan-pair-noninvariant-fixed-algebra-is-nonsofic
kind: claim
title: A free action whose full group contains a Kazhdan infranormal pair with a non-invariant fixed algebra is not sofic, and mixing does not blind this test
distinct_from:
  groups-containing-kun-thom-pair-have-nonsofic-actions: that needs the pair inside the acting group; here the pair lives only in the full group of the orbit relation
  free-action-containing-nonsofic-group-relation-is-nonsofic: that needs a free action of a nonsofic group inside the relation; here the pair's group L is sofic and its action by full-group elements may be non-free
  kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions: that kills Theorem C for subgroups of a mixing group; full-group copies of Γ are not subgroups and need not act ergodically
---

**ESTABLISHED.** Let `G ↷ (X,μ)` be an essentially free p.m.p. action with orbit relation `R_G`. Let
`Γ <= L` be countable groups, both with property (T), with `Γ` infranormal in `L` and `L` sofic. Let
`ρ : L → [R_G]` be a homomorphism into the full group, so `L` acts on `X` possibly non-freely. If
`L^∞(X)^(ρ(Γ))` is not `ρ(L)`-invariant, then `G ↷ X` is not sofic (Păunescu Definition 1.4).

**Why this changes the invariant.** For a mixing `G ↷ X`, every infinite subgroup of `G` acts ergodically.
So Theorem C is blind on the action, on its factors and restrictions
(`kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions`), and on compact extensions
(`compact-extension-kazhdan-fixed-algebras-are-blind`). Elements of `[R_G]` are piecewise group elements.
A Kazhdan group acting through them can be non-ergodic even when `G` is mixing, so none of those
blindness theorems applies.

**Calibration.** The test never fires on a sofic free action, for example a Bernoulli shift of a sofic `G`.
Hence no such `ρ` exists in the full group of a Bernoulli relation of a sofic group. By the blindness
claim, any `ρ` that fires has `ρ(Γ)` non-ergodic and `ρ(L)` non-ergodic or with a non-invariant
`ρ(Γ)`-factor.

**Relation to containment.** If `ρ(L)` acts on a positive set `A` as a free Kun--Thom action and
trivially off `A`, this is the containment design. There `kun-thom-actions-have-no-host-without-p-torsion`
and `kun-thom-action-soe-class-is-rigid` apply. The claim here also admits non-free `ρ`, and a `ρ(L)` whose
orbits are not a copy of any free Kun--Thom relation. The no-go theorems above use freeness of the copy.

Proof: `full-group-kazhdan-pair-nonsofic-proof`.
