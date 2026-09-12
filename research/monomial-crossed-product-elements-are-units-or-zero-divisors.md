---
rg: 2
id: monomial-crossed-product-elements-are-units-or-zero-divisors
kind: claim
title: Column-monomial or cancellation-free elements of the odd-measure crossed product are units or two-sided zero divisors
distinct_from:
  star-compression-designs-need-weight-four-colliding-columns: that constrains star designs x* x = eps_- by square counting; this makes every column-monomial or cancellation-free non-unit a two-sided zero divisor, so it excludes such corner witnesses and Cohn entries for every partner in S_-.
  odd-measure-space-has-no-honest-thompson-compression: that forbids honest partial isometries compressing M_- by Haar invariance; this uses the same invariance to show every covered non-unit annihilates an explicit nonzero element on both sides.
  mixed-depth-leavitt-lift-is-a-left-zero-divisor: that is the explicit annihilation sigma e' = 0 for the natural lifts; this is the general dichotomy, of which the natural lifts are instances.
artifacts:
  - research/artifacts/crossed-product-zero-divisor-filters-2026-09-12.md
---

Let `B = C(M_-, F_3) x| V`, and write `x in B` as `x = sum_g [g] b_g`. Put

    c_x(mu) = #{ g : b_g(mu) != 0 },        n_x(nu) = #{ g : b_g(g^-1 nu) != 0 },

the column weight and the image multiplicity.

**Theorem.** If `c_x <= 1` everywhere or `n_x <= 1` everywhere, then `x` is a unit of `B`, or `x` is both
a left and a right zero divisor in `B`.

**Covered elements.**
- Two-piece honest lifts `[g_0] P_C + [g_1] P_(X \ C)`, which have `c = 1`.
- Their adjoints, such as `[g_0^-1] P_00 + [g_1^-1] P_01`, which have `n = 1` although `c = 2` on
  `U_00 ∩ U_01`.
- Lifts through orthogonal character idempotents.
- Every cancellation-free element, meaning one whose translated supports are disjoint.

Not covered are honest partial isometries over partitions with three or more atoms, where `c` takes the
value `3`.

**Consequences.**
- *Cohn entries.* In a Cohn family `tau_i sigma_j = delta_ij eps_-` in `S_-`, no entry lying in `B` is
  covered. Neither is `u x v` for a covered non-unit `x in B` and units `u, v` of `S_-`. So the Hadamard
  unit, `1 + s_alpha t_beta`, or any element of `G` cannot revive a covered lift multiplicatively.
- *Corner witnesses.* If `c' q_[0] b' = eps_-` with `b' in B` and `c'` anywhere in `S_-`, then
  `q_[0] b'` has `c >= 2` and `n >= 2` on nonempty clopens.
  - This extends the cancellation-free no-go of the weight-four theorem from star designs to every
    partner.
- *The natural lifts.* Both natural lifts of the Leavitt pair are covered non-units, hence two-sided
  zero divisors.

**Proof.**
- `∫ c_x = ∫ n_x` by Haar invariance, `c_(x*) = n_x` and `n_(x*) = c_x`, and `lambda` charges every
  nonempty clopen.
- A zero column gives `x 1_W = 0`.
- Cancellation-free with no zero column forces `c = n = 1`, a signed permutation with inverse `x*`.
- A collision `g mu = g' mu'` gives `x (epsilon' 1_W - epsilon [g'^-1 g] 1_W) = 0`.
- The right-hand side follows from the left for `x*`.

Theorem 3.1 and Corollaries 3.2–3.3 of the artifact.

**ESTABLISHED 2026-09-12** by `monomial-crossed-product-dichotomy-proof`.
