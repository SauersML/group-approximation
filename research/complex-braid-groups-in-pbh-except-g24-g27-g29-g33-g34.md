---
rg: 2
id: complex-braid-groups-in-pbh-except-g24-g27-g29-g33-g34
kind: claim
title: The braid group of every finite complex reflection group lies in B_A, except possibly when an irreducible factor is of type G_24, G_27, G_29, G_33 or G_34
distinct_from:
  complex-braid-groups-satisfy-permutational-boone-higman: that is the open statement for all complex braid groups; this settles every case except five exceptional types.
  imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class: that is the family G(e,e,n); this assembles the whole Shephard--Todd classification, with that node as one input.
  spherical-artin-groups-satisfy-permutational-boone-higman: that is the real (Coxeter) case; this uses it for the real exceptional types and, through Bessis's regular-centralizer theorem, for G_25, G_26, G_31 and G_32.
artifacts:
  - research/artifacts/gq-bh-bh-verify-artin-euclidean-toric.md
---

**ESTABLISHED** through `complex-braid-groups-in-pbh-except-g24-g27-g29-g33-g34-proof`.
This is a lane assembly, not independently reviewed.
- For the real exceptional types it rests on
  `spherical-artin-groups-satisfy-permutational-boone-higman`, and so on that node's
  internal chain (`char-zero-linear-groups-satisfy-permutational-boone-higman`).
- Bessis's Theorem 12.4 and the proof of his Corollary 12.7 were read at source.
- Springer's table of regular centralizers was not read.

No priority is claimed. For the families that are linear, this is known in substance
from linearity together with the repo's linear theorem; the new inputs are the
non-linear-known `B(e,e,n)` and the uniform assembly.

## Statement

Let `W ⊂ GL(V)` be a finite complex reflection group, and `B(W) = π_1(W\V^reg)`.
Suppose no irreducible factor of `W` is of Shephard--Todd type `G_24`, `G_27`, `G_29`,
`G_33` or `G_34`. Then `B(W)` lies in `B_A`, so it embeds in a finitely presented
simple group.

## Case table (irreducible W)

| Type | Reason |
|---|---|
| rank 1, `Z/m` | `B = Z` |
| rank 2 (every rank-2 group: all `G(de,e,2)` and `G_4, …, G_22`) | `P(W) ≅ Z × F_(k−1)`, where `k` is the number of mirrors |
| `G(1,1,n) = S_n` | `B_n` |
| `G(de,e,n)`, `d >= 2`, `n >= 3` | `P(W) ≤ π_1(Conf_n(C^×)) ≤ P_(n+1)` with finite index in the first |
| `G(e,e,n)`, `e >= 2`, `n >= 3` | `imprimitive-braid-groups-b-e-e-n-lie-in-the-pbh-class` |
| `G_23 = H_3`, `G_28 = F_4`, `G_30 = H_4`, `G_35, G_36, G_37 = E_6, E_7, E_8` | `B(W)` is the spherical Artin group (Brieskorn) |
| `G_25`, `G_26`, `G_32` | regular centralizers in `E_6`, `E_7`, `E_8` (`d = 3`), so `B ↪ A(E_k)` by Bessis 12.4(iii) |
| `G_31` | regular centralizer in `E_8` (`d = 4`), so `B(G_31) ≅ C_(A(E_8))(ρ^6)` (Bessis, proof of Cor. 12.7) |
| `G_24`, `G_27`, `G_29`, `G_33`, `G_34` | **open**: `complex-braid-groups-satisfy-permutational-boone-higman` |

Reducible `W` is handled by closure under finite products, since
`B(W_1 × W_2) = B(W_1) × B(W_2)`.
