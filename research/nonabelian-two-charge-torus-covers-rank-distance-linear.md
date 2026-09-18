---
rg: 2
id: nonabelian-two-charge-torus-covers-rank-distance-linear
kind: claim
title: Regular F-covers of a square-tiled torus with at most two charged faces lie within rank 36 rho of a commuting pair, for every finite group F
distinct_from:
  torus-dipole-covers-rank-distance-linear-in-profile: that proves dist <= 24 rho for abelian fibres, where the two charges are a and -a and cancel along a spanning tree; this allows any finite fibre group and any two charges H_0, H_1, whose ordered product need not be trivial, and closes the band with the rung lemma instead.
  torus-abelian-covers-rectangle-profile-near-commute: that is abelian (Stokes); this is the first linear bound with a non-abelian fibre.
  centralizer-rounding-cannot-bound-rank-distance-by-profile: that kills one-sided rounding with a kept word; this is two-sided surgery, which that obstruction does not cover.
  z2-bounded-rectangle-profile-forces-near-commuting: that is the open statement for all pairs; this gives F(K) <= 36 K on regular non-abelian covers with at most two charged faces.
artifacts:
  - research/nonabelian-two-charge-torus-covers-rank-distance-linear-proof.md
  - experiments/nonabelian-rectangle-profile-2026-09-17/rungs.py
  - experiments/nonabelian-rectangle-profile-2026-09-17/rungs-summary.txt
---

**ESTABLISHED (unreviewed)** (`nonabelian-two-charge-torus-covers-rank-distance-linear-proof`). Elementary. It
extends `torus-dipole-covers-rank-distance-linear-in-profile` from abelian fibres to every finite group.

**Class.** `Lambda <= Z^2` has index `N`, and `G = Z^2/Lambda`. `F` is a finite group and `Omega = G x F`. The pair is
`b(x,a) = (x+e1, beta(x) a)` and `c(x,a) = (x+e2, gamma(x) a)`, the regular cover of the connection `(beta, gamma)`.
Face holonomy is `hol(x) = gamma(x)^-1 beta(x+e2)^-1 gamma(x+e1) beta(x)`, and the pair commutes iff every
`hol(x) = 1`.

The class is: **at most two charged faces**, with arbitrary nontrivial holonomies. Write the faces as `x_0` and
`x_1 = x_0 + g`, where `|g|_1` is the least `l^1` norm of a lift. Also:
- `lambda_1` is the least `l^1` norm of a nonzero vector of `Lambda`;
- `rho = sup_(s,t>=1) rank([b^s,c^t]-I)/(s+t)`;
- `dist` is the least `max(rank(b'-b), rank(c'-c))` over commuting permutation pairs of `Omega`.

**Theorem.** `dist <= 36 rho`. By cases:

| case | construction | sites | bound |
|---|---|---|---|
| one charge | rung band | `lambda_1` | `8 rho` |
| two charges, `|g|_1 < lambda_1`, neutral | path push | `|g|_1` | `4 rho` |
| two charges, `|g|_1 < lambda_1`, not neutral | push + rung band | `|g|_1 + lambda_1` | `35.6 rho` |
| `|g|_1 >= lambda_1`, row distance `D <= 2l` | push + rung band | `< 4.54 lambda_1` | `18.2 rho` |
| `|g|_1 >= lambda_1`, `D > 2l` | strip cut + two rung bands | `<= 6 lambda_1 + 2` | `32 rho` |

Here *neutral* means that the boundary of the bounding rectangle of the two charges has trivial holonomy. For
abelian `F` this is exactly `H_1 = H_0^-1`. Each site costs rank at most `|F|`.

**What is new.** Two points differ from the abelian proof.
- **Closing the bands.** The seam charges of a strip piece have a nontrivial ordered product in general, and by
  `nonabelian-band-rungs-absorb-ordered-charge-product` no disk-supported change can cancel them. The rung lemma
  of that node closes each band for one extra edge.
- **Lower bounds.** A nontrivial holonomy on a regular fibre moves every point, so it contributes at least `|F|/2`
  to `rank([b^s,c^t]-I)`. Counting boxes that contain exactly one charge gives `rho >= |F| ceil(m_0/2)/2`, with
  `m_0 = min(|g|_1, lambda_1)`. In the non-neutral short case, counting boxes that contain both charges gives
  `rho >= 9 |F| lambda_1/256`.

**Limits.** The lower bounds need a free fibre action. For a general `F`-set fibre, or for a general permutation
pair, a charge can move few points, so the rank count fails. The several-charge case needs the missing lower bound
for clusters that are not neutral (see the Attempts of `z2-bounded-rectangle-profile-forces-near-commuting`).

**Computation** (`rungs.py`, `rungs-summary.txt`). The construction of the proof was run on 6900 covers:
- fibres `S_3`, `Q_8` and `A_4`;
- random HNF tori with `N <= 24`, and thin tori with `N <= 48`;
- every case of the table.

All assertions pass. The worst ratio is `dist / rho_lower = 7.10` (`A_4`, thin, strip case). The worst site count
is `6.00 lambda_1`.

## Attempts
