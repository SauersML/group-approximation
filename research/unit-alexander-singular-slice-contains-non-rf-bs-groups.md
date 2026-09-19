---
rg: 2
id: unit-alexander-singular-slice-contains-non-rf-bs-groups
kind: claim
title: From length 27 on, the singular unpeelable unit-Alexander slice contains groups with Baumslag-Solitar subgroups, and from length 29 on groups that are not residually finite, so no hyperbolic, virtually special, linear or residually finite certificate can close the slice
distinct_from:
  length21-singular-relators-z-stable-hierarchy-special: that certifies every length-21 member of the slice hyperbolic and virtually special; this shows the method must fail from length 27 on, by explicit members containing BS(k,k+1).
  length19-singular-relators-z-stable-hierarchy-special: that certifies the length-19 members; this is an obstruction to extending such certificates to all lengths.
  bg-shift-chains-die-in-residually-linear-alphabets: that kills linear alphabets for the Magnus shift dictionary of one BG-type step; this puts a non-residually-finite Baumslag-Solitar group inside the Magnus vertex group of relators in the hard slice.
  rank-two-bs-model-roots-need-infinite-order-witnesses: that studies a peelable rank-two BS model, which is residually finite; these relators are unpeelable at both extremes and the groups are not residually finite.
artifacts:
  - experiments/one-relator-bs-in-slice-2026-09-18/family.py
  - experiments/one-relator-bs-in-slice-2026-09-18/family.out
  - experiments/one-relator-bs-in-slice-2026-09-18/bs_search.py
  - experiments/one-relator-bs-in-slice-2026-09-18/verify.py
  - experiments/one-relator-bs-in-slice-2026-09-18/canon_counts.py
  - experiments/one-relator-bs-in-slice-2026-09-18/n2w7.out
  - experiments/one-relator-bs-in-slice-2026-09-18/n2w7.err
  - experiments/one-relator-bs-in-slice-2026-09-18/n2w7.verify
  - experiments/one-relator-bs-in-slice-2026-09-18/n2w7.counts
---

ESTABLISHED (hand proof plus a checked computation, unreviewed). Proof:
[[unit-alexander-singular-slice-contains-non-rf-bs-groups-proof]].

**The slice.** `G = <a,t | w>` with `w` cyclically reduced and `t`-exponent 0. Its Magnus rewriting
`W_0` in `a_h = t^h a t^-h` has levels `0..n`. The slice is the class the length-19 and length-21
censuses close: exactly one level has non-zero exponent sum and it is `+-1` (unit Alexander
polynomial), at least one extreme level is singular (sum 0), and neither extreme is peelable. Since
`b_1(G) = 1`, the extremes are the same in every zero-exponent basis, so unpeelability does not
depend on the basis. The kernel `G'` is perfect, so `G` is not residually solvable.

## Theorem

For `k >= 1` let `T = a_2 a_0 a_1 a_2` and
`W_0 = T a_0^(-k) T^(-1) a_0^(k+1)`. Let `w_k` be the corresponding word in `F(a,t)`, so
`|w_k| = 25 + 2k`:
- `w_1 = aTTatataTTAttATATAttATTaatt` (length 27);
- `w_2 = aTTatataTTAAttATATAttATTaaatt` (length 29).

Then `G_k = <a,t | w_k>` has these properties.

1. **It lies in the slice.** Level 0 has syllables `1, -k, -1, k+1`, with sum 1. Level 2 has
   syllables `1, 1, -1, -1`, with sum 0, so it is singular. Level 1 has sum 0. Both extremes have
   four syllables, so both are unpeelable. The landed census certificate search
   (`census.cert_word`: PEEL, PP, R1, CYC in all small zero-exponent bases) fails on every `w_k`.
2. **It contains `BS(k,k+1)`.** The triple `(T, a_0, a_2)` is a free basis of `F(a_0,a_1,a_2)`,
   so `B_0 = <a_0,a_1,a_2 | W_0> = BS(k,k+1) * Z`. `B_0` is the vertex group of the Magnus HNN
   splitting `G = B_0 *_psi`, so it embeds in `G`.
3. **Consequences.** `G_k` is torsion-free, `pi(w_k) = 2`, and `G_k` is not hyperbolic and not
   virtually special. For `k >= 2`, `BS(k,k+1)` is not residually finite (Meskin), so `G_k` is
   not residually finite and not linear.

**The census.** `bs_search.py 2 7 45` searches all Nielsen bases of `F(a_0,a_1,a_2)` of total
length at most 7, with `W_0 = U^-1 V^p U V^-q`, `(U,V,X)` a basis, `V` of unit exponent vector
and `|p - q| = 1`. `verify.py` independently re-checks every relator it finds. It checks the basis
by Nielsen reduction to letters, the Magnus word from `w`, the slice conditions, and that the
census certificate fails. All 7392 relators pass (`n2w7.verify`). Up to the census symmetries
(`n2w7.counts`):

| subgroup | classes | shortest length (number of classes there) |
|---|---|---|
| `BS(1,2)` | 288 | 27 (32) |
| `BS(2,3)` | 216 | 29 (32) |
| `BS(3,4)` | 216 | 31 (32) |

In this family nothing is shorter than 27, and `w_k` with `p = 0` is trivial. The search says
nothing about lengths 23 and 25 outside the family.

## What it rules out

- **The per-length census program cannot reach all lengths.** The length-19 and length-21 proofs
  run magint, then Collins, then Stallings `sZ`, then kbmag, then Linton Thm 7.1. Linton's
  criterion needs `G` hyperbolic, or at least free of BS subgroups, so it fails on `G_1` at
  length 27. From length 29 on, the slice has members that are not residually finite, so no
  certificate that proves residual finiteness can work there. This covers virtual specialness,
  linearity, the separable-piece route of
  [[nonsingular-magnus-extremes-separable-piece-sofic]] (which needs `B_0` residually finite),
  and profinite gluing.
- **A uniform argument for the slice must be genuinely sofic.** It must handle groups that are
  neither residually finite nor residually solvable, whose Magnus vertex group already contains
  `BS(2,3)`, and whose edge groups are free of rank 2.

## Open

It is open whether `G_2` is sofic. `B_0 = BS(2,3) * Z` is sofic, and it is even residually
solvable. The HNN extension is over the rank-two free subgroups `F(a_0,a_1)` and `F(a_1,a_2)`.
Neither the landed census certificates nor the Linton route close it. `G_2` is the explicit
test group of this class: it is non-residually-finite, the kernel `G_2'` is perfect, it is
torsion-free, and `pi = 2`.
