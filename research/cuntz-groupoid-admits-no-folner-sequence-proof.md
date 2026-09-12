---
rg: 2
id: cuntz-groupoid-admits-no-folner-sequence-proof
kind: route
title: Push source fibres to the Cantor set with multiplicity and apply the orbit boundary bound
target: cuntz-groupoid-admits-no-folner-sequence
requires:
  - thompson-v-cantor-orbits-have-no-folner-sets
artifacts:
  - research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md
---

Full proof: Section 3 of the artifact, Lemma 3.2 and Theorem 2.

**Multiplicities.** For `m : X -> N` with finite support, put `(s.m)(x) = m(s^-1 x)` and
`F_j = {m >= j}`. The layer-cake identity `||s.m - m||_1 = sum_j |s F_j sym-diff F_j|` and the
bound of `thompson-v-cantor-orbits-have-no-folner-sets` on each `F_j` give
`max_s ||s.m - m||_1 >= (c_S / |S|) ||m||_1`.

**Fibres.** Put `F_u = F ∩ G_u`.
- `K F_u <= G_u`, so `|KF \ F| = sum_u |K F_u \ F_u|`.
- `B_s` has source `X`, so left multiplication by it is injective on `G_u`, with
  `r(B_s gamma) = s r(gamma)`.
- With `m_u = r_*(counting on F_u)`, this gives
  `||s.m_u - m_u||_1 <= |B_s F_u sym-diff F_u| = 2|B_s F_u \ F_u| <= 2|K F_u \ F_u|`.
- Nontrivial isotropy, where `r` is not injective on `G_u`, is absorbed by the multiplicities.

**Conclusion.** Combining, `|K F_u \ F_u| >= (c_S / 2|S|) |F_u|`, and summing over `u` gives the
claim. A normal Følner set contains the unit space, so `S_n u` is nonempty, and the ratio in Ma's
Definition 4.12 stays bounded below. Fiberwise amenability fails because the outer boundary lies
inside Ma's boundary `d_K F`.
