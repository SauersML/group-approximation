---
rg: 2
id: mass-only-spectral-relaxation-of-subgroup-dominance-is-order-c
kind: claim
title: The law nu_c = 2^-c (delta_0 + delta_(e_1) + ... + delta_(e_(2^c - 1))) satisfies every subspace mass bound nu(W) <= 2^(dim W - c) yet has subgroup-dominance constant at least c 2^(c-1)/(2^c - 1) >= c/2, so no argument using only the mass profile of the spectral law (such as the stopping-time proof of the log loss) can bound C(S) by a constant
distinct_from:
  f2-cayley-subgroup-sets-lose-at-most-log-inverse-density: that proves the upper bound E_c/2 from the mass bound; this proves the matching lower bound c 2^(c-1)/(2^c-1) for every law obeying the mass bound, so that argument is optimal for its information up to an additive 0.81.
  f2-cayley-subgroup-sets-are-constant-factor-optimal: that conjectures C(S) = O(1) for sets; this is about laws that need not come from sets, and kills a class of proofs of that conjecture, not the conjecture.
  f2-set-spectral-laws-obey-quotient-collision-and-harper-bounds: that proves (M) and the Harper bound (H) for set laws; this shows (M) alone is order-c weak, and its witness violates (H).
artifacts:
  - research/mass-only-spectral-relaxation-order-c-proof.md
  - experiments/f2-cayley-dominance-2026-09-17/spectral_relaxation.py
---

**Setting.** Characters and group elements are both `F_2^k`, paired by
`chi.a`. For a probability law `nu` on characters put
`d_nu(a) = 2 nu{chi : chi.a = 1}`. Then

```text
C(nu) = min over laws p on subgroups H of index 2^c  of  max_(a != 0) Pr_p[a not in H] / d_nu(a),
```

with the convention of the target claim: `d_nu(a) = 0` forces `Pr_p[a not in H] = 0`.
For a set `S` of measure `2^-c`, `nu_S = N hat(1_S)^2 / |S|` has `d_(nu_S) = d_S`,
so `C(nu_S) = C(S)`. The **mass-only relaxation** is

```text
R_M(k, c) = sup { C(nu) :  nu(0) = 2^-c  and  nu(W) <= min(1, 2^(dim W - c)) for all subspaces W }.
```

Every `nu_S` is feasible (item (M) of
`f2-set-spectral-laws-obey-quotient-collision-and-harper-bounds`), so
`C(S) <= R_M(k, c)`.

**Theorem.** Let `m = 2^c - 1` and `k >= m`. The law
`nu_c = 2^-c (delta_0 + sum_(i<=m) delta_(e_i))` is feasible, and

```text
C(nu_c) >= L_c := c 2^(c-1) / (2^c - 1)          (L_1 = 1, L_2 = 4/3, L_3 = 12/7, L_c > c/2).
```

Dually, for `w` uniform on the dual vectors `a_1, ..., a_m` (`e_i.a_j = [i = j]`),
`Phi_w(nu_c) = sum_a w_a d_(nu_c)(a) = 2^(1-c)` while every index-`2^c` subgroup
`H` with finite cost has `w(F_2^k \ H) >= c/m`. Proof: route
`mass-only-spectral-relaxation-order-c-proof`. The LP in
`spectral_relaxation.py example c` gives `C(nu_c) = L_c` exactly at `c = 2, 3`
(values `1.33333`, `1.71429`).

**What this kills (precise obstruction).**

- *Invariant.* The subspace mass profile `W -> nu(W)` of the spectral law, together
  with `nu(0) = 2^-c`.
- *Class.* Every argument that produces a law `p` on subgroups with
  `Pr_p[a not in H] <= K d_S(a)` for all `a`, and that uses the set `S` only through
  that profile. The stopping-time/Wald argument of
  `research/artifacts/f2-cayley-subgroup-loss-spectral-sampling-proof-2026-09-17.md`
  is in this class: its steps (3)-(4) use only its facts (1)-(2). So does its
  proposed repair, in which the charge is conditioned on dimension-raising
  samples.
- *Where it dies.* At the charging step. Any such argument must give `K >= L_c > c/2`,
  so it can at best reach the proved `E_c/2 <= (c + 1.61)/2`. The two bounds differ
  by `(sum_(i<=c) 1/(2^i - 1) - c/(2^c - 1))/2 <= 0.81`. The log loss is
  therefore the exact price of the mass profile, not slack in the analysis.

**What survives.** `nu_c` is not the law of any set. It violates the Harper
quotient bound (H) at `B = F_2^m` with basis `a_1, ..., a_m`:
`2 sum_i nu_c{chi.a_i = 1} = 2(1 - 2^-c) < 2 <= c` for `c >= 2`. So any constant
bound must use an inequality that the mass profile does not see, such as (H),
Shannon (rather than collision) entropy of quotients, or the integrality of
`hat(1_S)`. The next relaxation, (M)+(H), is recorded as
`f2-cayley-mass-harper-spectral-relaxation-is-bounded`.
