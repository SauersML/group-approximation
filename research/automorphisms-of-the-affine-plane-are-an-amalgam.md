---
rg: 2
id: automorphisms-of-the-affine-plane-are-an-amalgam
kind: claim
title: The polynomial automorphism group of the affine plane over any field is the amalgam of the affine and de Jonquières groups
artifacts:
  - research/artifacts/formalizability-finite-levels-and-z3-rigidity-2026-09-12.md
---

For every field `K`, `Aut(K[x,y]) = Aff *_B Tri`.
- `Aff` is the affine group.
- `Tri` consists of the de Jonquières maps `(x,y) -> (ax + b, cy + p(x))`, with `a, c` nonzero and
  `p` a polynomial.
- `B = Aff ∩ Tri`.

The amalgam acts without inversion on its Bass–Serre tree.

**Source.** W. van der Kulk, *On polynomial rings in two variables*, Nieuw Arch. Wisk. (3) 1 (1953),
33–41: the arbitrary-field case of Jung's theorem. The tree action is Serre, *Trees*, Chapter I,
Section 4.

**Trust surface.** Imported at statement level; not re-read from the source in this lane.
