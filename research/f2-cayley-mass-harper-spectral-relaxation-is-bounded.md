---
rg: 2
id: f2-cayley-mass-harper-spectral-relaxation-is-bounded
kind: claim
title: Every probability law nu on the characters of F_2^k with nu(0) = 2^-c, all subspace mass bounds and all Harper quotient bounds has subgroup-dominance constant C(nu) <= R for an absolute R, a Boolean-free statement that implies C(S) <= R for every set
distinct_from:
  f2-cayley-subgroup-sets-are-constant-factor-optimal: that bounds C(nu) only on laws of sets; this bounds it on the convex relaxation cut out by (M) and (H), so it is strictly stronger and can fail while that conjecture holds.
  mass-only-spectral-relaxation-of-subgroup-dominance-is-order-c: that shows the relaxation with (M) alone has value at least c/2; this asks whether adding (H) brings the value down to a constant.
  f2-cayley-subgroup-sets-lose-at-most-log-inverse-density: that gives E_c/2 from (M) alone; this asks for an absolute constant from (M)+(H).
artifacts:
  - experiments/f2-cayley-dominance-2026-09-17/spectral_relaxation.py
---

**OPEN.** Notation is as in
`mass-only-spectral-relaxation-of-subgroup-dominance-is-order-c`. Let
`F(k, c)` be the set of laws `nu` on the characters of `F_2^k` with:

- `nu(0) = 2^-c`;
- (M) `nu(W) <= min(1, 2^(dim W - c))` for every character subspace `W`;
- (H) `2 sum_(i<=r) nu{chi : chi.b_i = 1} >= log2(1/nu(B^perp))` for every
  independent `b_1, ..., b_r` with span `B`.

`F(k, c)` is convex: (H) says a linear function is at least a convex function
of a linear function. Put `R_MH(k, c) = sup_(nu in F(k, c)) C(nu)`.

**Conjecture.** `R_MH := sup_(k, c) R_MH(k, c) < infinity`. The weak form
suffices: `Phi_w(nu) <= eta` implies `min_H w(F_2^k \ H) <= F(eta)` for all
`nu in F(k, c)`, with `F(eta) -> 0` independent of `k` and `c`.

**Why it is a genuine prerequisite.**

- *Sufficient.* Route `f2-cayley-dominance-from-bounded-mass-harper-relaxation`
  derives `f2-cayley-subgroup-sets-are-constant-factor-optimal` from this claim
  and the established
  `f2-set-spectral-laws-obey-quotient-collision-and-harper-bounds`.
- *Can fail on its own.* It forgets that `hat(1_S)` takes values in `N^-1 Z`, that
  quotient entropies are Shannon rather than collision entropies, and every
  higher-order (triple-correlation) constraint. A law in `F(k, c)` with growing
  `C(nu)` would refute this claim and leave the set conjecture untouched. It
  would also say exactly which extra Boolean constraint is needed.
- *Boolean-free.* It is a statement about a convex set of measures, cut out by
  quotient-collision inequalities, together with a finite LP over subgroups. It
  can be attacked by LP duality: for fixed `w`, a bound is a nonnegative
  combination of (M) and tangent cuts of (H).

**Data** (`spectral_relaxation.py`, cutting planes for (H) at the
minimum-weight basis of every subspace; the values are lower bounds on
`R_MH(k, c)` found by alternating `w -> argmin_nu Phi_w(nu)` and
`nu -> C(nu)`, seeded from locally optimal sets):

| `(k, c)` | best set found, `C(S)` | (M)+(H) climb, `C(nu)` | (M) only |
|---|---|---|---|
| (5, 2) | 52/51 = 1.0196 | 1.0714 (15/14) | >= 4/3 |
| (6, 2) | 1.0141 | 1.0769 (14/13) | >= 4/3 |
| (6, 3) | 1.0386 | 1.0909 (12/11) | 12/7 needs k >= 7 |
| (7, 3) | 1.0163 (100-step search) | 1.0909 (12/11) | 12/7 (the law nu_3) |
| (7, 4) | ball {0, e_1..e_7}: 22/21 | 1.0714 (15/14), from the ball | >= 16/11 (climb from the ball) |

At every tested point, adding (H) cuts the relaxation from order `c/2` down
to within `0.1` of the best sets. The witness at `(5, 2)` is
`nu = 1/4 delta_0 + 1/12 (sum over 9 characters)`. It is not the law of a set,
because `N hat(1_S)` must be an integer. So the relaxation is not tight, but its
excess over the sets is small at these sizes.

## Attempts

* **Hill-climbing lower bounds (2026-09-17, swarm-0917-w7).** See the table.
  - *Where it dies.* Alternating optimisation finds only local optima, and it is
    not monotone in `k` (14/13 at `(6, 2)` is below 15/14 at `(5, 2)`, although
    `R_MH` is monotone under embedding). So the table gives lower bounds, not
    values.
  - *What is missing.* A search at `c >= 4`, which is where the mass-only
    relaxation already reaches `L_4 = 32/15`, together with a
    construction or a dual certificate for general `c`.
