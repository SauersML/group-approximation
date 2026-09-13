---
rg: 2
id: km-246-completions-are-kazhdan-howe-moore-simple
kind: claim
title: The completions of a (2,4,6) Kac-Moody lattice over F_q with q >= 3 are simple Kazhdan Howe-Moore groups in which the lattice induces commensurated Kazhdan lattices
distinct_from:
  km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4: that is about the discrete group S_q itself (finite presentation, simplicity, (T), IRS rigidity); this is about the two locally compact completions L_+ and L_- and the lattices S_q induces in them.
  caprace-thom-v2-leaves-km-character-rigidity-open: that audits what Caprace--Thom v2 proves about characters of S_q; this imports the properties of the completions that their Section 5 uses.
---

**ESTABLISHED (literature import, unreviewed).** Let `Λ_q` be the minimal simply connected
split Kac--Moody group of type `(2,4,6)` over `F_q` (the generalized Cartan matrix `(KM2)` of
`simple-kazhdan-kac-moody-lattices-exist`), `Z` its finite centre and `S_q = Λ_q/Z`. Let
`X_+`, `X_-` be the two halves of its twin building and `L_±` the closure of the image of
`Λ_q` in `Aut(X_±)`. For every prime power `q >= 3`:

```text
(KHM1) L_+ and L_- are second countable, non-discrete, non-compact, topologically simple,
       totally disconnected locally compact groups acting strongly transitively on X_±.
(KHM2) L_+ and L_- have property (T) and the Howe--Moore property.
(KHM3) S_q is an irreducible lattice in L_+ x L_-, and both projections S_q -> L_+ and
       S_q -> L_- are injective with dense image.
(KHM4) If K_- is a compact open subgroup of L_-, then
       Lambda_+ = proj_{L_+}( S_q ∩ (L_+ x K_-) )
       is a lattice in L_+, it is commensurated by the image of S_q, and it has (T).
```

**Where each item comes from** (quotes in the citation route).
- (KHM1), the lattice statement in (KHM3), and (T) in (KHM2): Caprace--Thom, proof of
  Corollary 5.3, with Proposition 4.1(1).
- Howe--Moore in (KHM2): Caprace--Thom's Theorem A, run as in their proofs of Corollaries B
  and BB, with (T) of `L_±` supplied by Proposition 4.1(1). Their proof of Corollary 5.3
  asserts this for all these `q`. The introduction's uniform corollary asks for `q >= 11`
  unless `W` is 3-spherical, but at type `(2,4,6)` the proof of Corollary B needs thickness
  only to get (T) of the minimal non-spherical parabolic, which is the whole group.
- Injectivity in (KHM3): Creutz--Peterson, Lemma 5.2 of arXiv:1311.4513v3.
- (KHM4): the argument in the proof of Theorem 9.1 of Creutz--Peterson, arXiv:1303.3949.
  Property (T) holds because a lattice in a Kazhdan locally compact group is Kazhdan
  (Bekka--de la Harpe--Valette, Theorem 1.7.1, as imported in
  `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4-citation`).

Citation: `km-246-completions-kazhdan-howe-moore-citation`.
