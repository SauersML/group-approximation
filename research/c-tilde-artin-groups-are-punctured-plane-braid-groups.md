---
rg: 2
id: c-tilde-artin-groups-are-punctured-plane-braid-groups
kind: claim
title: The Euclidean Artin group of type C̃_n is the n-strand braid group of the twice-punctured plane
distinct_from:
  c-tilde-artin-groups-satisfy-permutational-boone-higman: that derives an embedding in B_(n+2) and the permutational Boone--Higman property; this is only the literature identification of A(C̃_n) with a surface braid group, which that derivation consumes.
artifacts:
  - research/artifacts/bh-artin-groups-2026-09-12.md
---

**ESTABLISHED (literature import).** Let `n >= 2`, and let `A(C̃_n)` be the
Artin group of the Euclidean Coxeter diagram C̃_n, which has `n+1` nodes. Then

```text
A(C̃_n)  ≅  π_1 UConf_n(C - {p, q}),
```

the braid group on `n` strands of the plane with two punctures.

**Source.** D. Allcock, *Braid pictures for Artin groups*, arXiv:math/9907194v1.
- **Table 1.1**, row "˜Cn 2 punctures 1 n > 1". The caption says that, for each
  row, the Artin group "is a normal subgroup of the n-strand braid group of the
  orbifold which is the plane equipped with the given features". The third
  column gives the quotient, here trivial.
- **§4**, "The diagram ˜Cn":
  - "W is the group Zn : 2n : Sn";
  - "V0 = { (x1, . . . , xn) ∈ Cn | xj ± xk /∈ Z for j ⁄= k and xj /∈ 1/2 Z for
    all j }";
  - "this identifies V0/ (Zn : 2n) with the pure braid space of C − {0, 1/2}".
- **The π_1 input.** §4 opens with "The Artin group itself is the fundamental
  group of the quotient of V0 by the Weyl group". For affine Weyl groups this is
  Nguyễn Viết Dũng, Topology 22 (1983) 425--435, Allcock's reference [10].

**Check of the identification** (not a new proof):
- `Z^n : 2^n` acts coordinatewise by the infinite dihedral group
  `<x ↦ x+1, x ↦ -x>`, freely on `C - ½Z`.
- The map `x ↦ e^(2πix) + e^(-2πix)` identifies `(C - ½Z)/D_∞` with the plane
  minus the two points `±2`.
- For coordinates avoiding `½Z`, `x_j ± x_k ∉ Z` says exactly that their images
  differ.
- So `V0/(Z^n : 2^n)` is the ordered configuration space of `n` points in the
  twice-punctured plane, and dividing by `S_n` gives `UConf_n`.

Not reproved here.
