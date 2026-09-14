---
rg: 2
id: independent-free-factor-equivalences-force-common-theory
kind: claim
title: Two log-independent elementary equivalences among free group factors force all interpolated free group factors to be elementarily equivalent
artifacts:
  - research/artifacts/hl-free-group-factors-2026-09-13.md
distinct_from:
  free-group-factor-first-order-trichotomy: that is the Goldbring–Pi trichotomy; this shows directly, without the trichotomy, which finite sets of comparisons force its first case.
---

Let `1 < m_1, n_1, m_2, n_2 < infinity` with `m_i != n_i`. Write `≡` for
elementary equivalence of tracial von Neumann algebras.

1. If `L(F_m) ≡ L(F_n)` with `m != n`, then for every `1 < r < infinity` and
   every `k in Z`, `L(F_r) ≡ L(F_{1 + (r-1) lambda^k})`, where
   `lambda = (n-1)/(m-1)`.
2. If `L(F_{m_1}) ≡ L(F_{n_1})` and `L(F_{m_2}) ≡ L(F_{n_2})`, and
   `log((m_1-1)/(n_1-1)) / log((m_2-1)/(n_2-1))` is irrational, then
   `F_fo(L(F_r)) = R_+` for every `1 < r < infinity`, and all `L(F_r)` with
   `1 < r < infinity` are elementarily equivalent.
3. In particular `L(F_2) ≡ L(F_3)` and `L(F_2) ≡ L(F_4)` together imply that
   every interpolated free group factor `L(F_r)`, `1 < r < infinity`, has the
   same first-order theory. The ratio is `log 2 / log 3`, which is irrational.

Direct proof in `independent-free-factor-equivalences-common-theory-proof`,
from the Dykema compression formula and the Goldbring–Hart / Goldbring–Pi
amplification facts. Elementary; no novelty claimed. It is close to what the
Goldbring–Pi trichotomy already encodes (case 3 has a cyclic first-order
fundamental group), but it needs only closedness of `F_fo`, not the trichotomy.
Not independently reviewed.
