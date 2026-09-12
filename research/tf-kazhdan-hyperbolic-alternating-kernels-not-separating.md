---
rg: 2
id: tf-kazhdan-hyperbolic-alternating-kernels-not-separating
kind: claim
title: A torsion-free hyperbolic Kazhdan group has infinitely many alternating quotients whose kernels share an infinite normal subgroup
distinct_from:
  caprace-kassabov-hyperbolic-kazhdan-alternating-quotients: that imports hyperbolic Kazhdan groups with torsion and infinitely many alternating quotients; this adds torsion-freeness and shows that the kernels of those quotients all contain one infinite normal subgroup
  sp21-noncongruence-simple-kernels-separate-points: that is the open separation assertion for a cocompact arithmetic Sp(2,1) lattice; this shows that its analogue fails for torsion-free hyperbolic Kazhdan groups in general
---

**ESTABLISHED.** There is a torsion-free word-hyperbolic group `G` with property
(T), together with:
- an infinite normal subgroup `M ⊴ G`;
- one normal subgroup `N_ℓ ⊴ G` for each prime `ℓ >= 3`, with `G/N_ℓ` an
  alternating group whose degree grows with `ℓ`;
- `M ⊆ N_ℓ` for every `ℓ`.

So `G` fails the separation form. Every `1 != g ∈ M` has infinite order and lies
in infinitely many alternating quotient kernels, and `G/M` still has infinitely
many alternating quotients although `M != 1`.

## What it changes

- **Fence on the separation form.**
  `sp21-noncongruence-simple-kernels-separate-points` cannot be derived from
  torsion-freeness, hyperbolicity and property (T). A proof has to use
  arithmeticity (congruence structure, superrigidity), exactly as for the
  finiteness form `sp21-lattice-few-alternating-and-large-rank-quotients`.
- **The open scope note is decided.** `caprace-kassabov-hyperbolic-kazhdan-alternating-quotients`
  recorded that the KMS examples have torsion and that separation for
  torsion-free groups was not decided by them. It now is, negatively.
- **Already inside the KMS group.** Step 1 of the proof shows that one element of
  infinite order of the KMS group `G_HC(1)(p)` lies in all the Caprace–Kassabov
  alternating kernels. Torsion-freeness is only needed for the pulled-back
  statement.

## Scope

`G` is not a lattice and is not arithmetic. Nothing here decides whether a
cocompact arithmetic `Sp(2,1)` lattice has infinitely many alternating quotients.
The mechanism behind these quotients, polynomial transvection groups acting on
affine spaces over finite fields, has no known counterpart for such a lattice.
See the Attempts of `sp21-lattice-few-alternating-and-large-rank-quotients`.

Proof in `tf-kazhdan-hyperbolic-alternating-kernels-proof`. Not reviewed; not in
Lean.
