---
rg: 2
id: ghb7-vertex-irreducibles-edge-restriction-table
kind: claim
title: The GHB_2(7) vertex irreducibles restrict regularly to their edges, except 42 degree-7 irreducibles of each order-2401 vertex on c
distinct_from:
  ghb7-triangle-vertex-groups-split-abelianizations: that computes abelianizations, class numbers and edge centralizer orders of the vertex groups; this lists every irreducible representation of the vertex groups together with its eigenvalue multiplicities on the edge generators
  triangle-edge-matching-reduces-to-one-edge-holonomy: that reduces edge matching to one-edge holonomy absorption under a split-abelianization hypothesis; this records which vertex irreducibles have non-regular edge restrictions, the data that absorption on the edge c has to handle
artifacts:
  - experiments/ghb7-edge-matching/edge_restrictions.py
  - experiments/ghb7-edge-matching/edge_restrictions.json
---

**ESTABLISHED (exact computation).** Let `X_0 = ⟨a,b⟩` (order 343), `X_1 = ⟨c,b⟩` and
`X_2 = ⟨c,a⟩` (order 2401) be the vertex groups of `G = G_{HB_2}(7)`, with edge groups
`⟨a⟩, ⟨b⟩, ⟨c⟩` of order 7 (`cckw-ghb2-kms-group-structure`). Write a multiplicity vector of a
representation of `Z/7` as the counts of the eigenvalues `ζ^0, …, ζ^6`, `ζ = e^(2πi/7)`.

| vertex | linear | degree 7 | restriction of the degree-7 irreducibles |
|---|---|---|---|
| `X_0` | 49 | 6 | `a` and `b` regular, `(1,1,1,1,1,1,1)`, in all 6 |
| `X_1` | 49 | 48 | `b` regular in all 48; `c` regular in 6, and a permutation of `(2,2,2,1,0,0,0)` in 42 |
| `X_2` | 49 | 48 | `a` regular in all 48; `c` regular in 6, and a permutation of `(2,2,2,1,0,0,0)` in 42 |

There are no other irreducibles: the number of irreducibles equals the number of conjugacy classes
(55, 97, 97), and `49 + 49·(number of degree-7 irreducibles) = |X|`.

**Reading.**
1. **Edges `a` and `b`.** Every irreducible of every vertex group restricts to `⟨a⟩` and to `⟨b⟩`
   either as a linear character or as the regular representation.
2. **Edge `c`.** The only non-regular restrictions of nonlinear irreducibles occur on `c`, in 42 of
   the 48 degree-7 irreducibles of `X_1` and in 42 of those of `X_2`. In those, `c` has four distinct
   eigenvalues, three of them twice and one once.
3. **Consistency.** Column orthogonality `Σ_χ |χ(x^j)|^2 = |C_X(x^j)|` holds for `j = 1..6` in every
   case. At `c` it reads `49 + 42·7 = 343`.
4. **Remark, not used.** The pattern `(2,2,2,1,0,0,0)` is the value distribution of a quadratic
   polynomial over `F_7`. That is what Clifford theory predicts when conjugation by `b` (or `a`)
   shifts the character of `C_X(c)` along an orbit on which the exponent of `c` grows quadratically.

DERIVATION
ghb7-vertex-irreducibles-edge-restriction-computation
