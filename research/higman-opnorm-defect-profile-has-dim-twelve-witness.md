---
rg: 2
id: higman-opnorm-defect-profile-has-dim-twelve-witness
kind: claim
title: The Higman operator-norm defect profile is monotone, and a twelve-dimensional far tuple has defect 0.31
artifacts:
  - research/higman-opnorm-defect-profile-has-dim-twelve-witness-proof.md
  - experiments/higman-opnorm-census-2026-09-17/tuple_search.py
  - experiments/higman-opnorm-census-2026-09-17/matcher_return.py
  - experiments/higman-opnorm-census-2026-09-17/analyze_tuple.py
  - experiments/higman-opnorm-census-2026-09-17/tuple_L12_defect031.txt
  - experiments/higman-opnorm-census-2026-09-17/run_diag13_long.txt
  - experiments/higman-opnorm-census-2026-09-17/run_diag29_long.txt
  - experiments/higman-opnorm-census-2026-09-17/run_diag7_long.txt
  - experiments/higman-opnorm-census-2026-09-17/run_tuple54_warm.txt
  - experiments/higman-opnorm-census-2026-09-17/run_n4_cont.txt
distinct_from:
  higman-four-cycle-intrinsic-mf-seed: that asks for a dimension-free collapse modulus; this reformulates the modulus as the limit of a monotone profile and gives an explicit upper calibration for it, proving nothing about the limit.
  order-four-bs-matcher-builds-higman-opnorm-microstate: that constructs microstates from matchers with vanishing error; this records a free four-tuple witness with no matcher structure and shows that the order-four matcher optimum found numerically is worse than the free one.
  one-small-higman-generator-collapses-the-four-cycle: that proves collapse when one generator is inside a small-arc basin and the defect is below an explicit threshold; this gives a tuple with every generator at distance at least 1.985 and defect 0.3099, calibrating how large a threshold can be once all generators are far.
  periodic-higman-bs-clocks-have-three-opnorm-small-seams: that makes three seams small for clocks with one unpaid return; this measures the whole four-relator defect of actual tuples.
---

**ESTABLISHED** by `higman-opnorm-defect-profile-has-dim-twelve-witness-proof`.
Items 1 and 3 are proofs.  Item 2 is an explicit floating-point witness with a
verification script.

For unitaries `U=(U_0,...,U_3)` in `U(L)` put

```text
def(U)=max_i ||U_i U_(i+1) U_i^* - U_(i+1)^2||_op,
m_c(L)=inf { def(U) : U in U(L)^4, max_i ||U_i-1|| >= c }.       (HDP1)
```

1. **Monotone profile.**  `m_c(L+1) <= m_c(L)` for every `c` and `L`.
   Hence the collapse modulus `(HMF5)` of `higman-four-cycle-intrinsic-mf-seed`
   holds if and only if

   ```text
   lim_(L->infinity) m_c(L) > 0        for every c>0.          (HDP2)
   ```

2. **Dimension-twelve witness.**  The tuple stored in
   `tuple_L12_defect031.txt` has these properties:
   - `U_0` is the diagonal of the primitive thirteenth roots of unity, and
     `U_1,U_2,U_3` were found by descent.
   - The unitarity error is `4.3e-14`.
   - The four relator defects are `0.309828, 0.309192, 0.309802, 0.309377`.
   - `||U_i-1||` is `1.985418, 1.988714, 1.997066, 1.993284`.

   Therefore

   ```text
   m_1.985(L) <= 0.3100                 for every L >= 12.      (HDP3)
   ```

   Any proof of `(HMF5)` must use a threshold `delta(1.985)<=0.31`.

3. **Spectral floor for cycle seeds.**  For every tuple and every `j`,

   ```text
   def(U) >= d_H( spec U_j , spec U_j^2 ).                     (HDP4)
   ```

   In particular, suppose `U_j` has spectrum exactly the `L`-th roots of unity,
   with `L` even.  Then `def(U) >= 2 sin(pi/L)`.  For example, this applies to
   the `L`-cycle `P` of the order-four matcher ansatz.

## Census (evidence, not established)

The free descent in `tuple_search.py` minimizes Schatten-`2m` norms of the four
relator errors over `U_1,U_2,U_3`.  It uses continuation in `m=4,8,...,64` and
Riemannian Armijo steps.  `U_0` is either a squaring-invariant diagonal (the
primitive `o`-th roots) or an `L`-cycle.  Best operator-norm defects:

```text
seed                         L    starts x iters   best def
primitive 7th roots          6    10 x 2000        0.3392
primitive 13th roots        12     6 x 1500        0.3098
primitive 29th roots        28     4 x 1500        0.3100
primitive 37th roots        36     1 x  400        0.3853
L-cycle                     12     2 x  300        0.5188  (floor 2sin(pi/12)=0.5176)
L-cycle, matcher warm start 54     1 x  400        0.3336
```

The order-four matcher gate (`matcher_return.py`, same continuation) gives
`max(eps,r)=0.4009` for `q=27` and `0.3689` for `q=81`.  The corresponding
matcher tuple at `q=81` has actual defect `1.3917`.

What the census shows:

- **Shape of the optimum.**  At optimum the four defects equalize, and every
  `||U_i-1||` sits in `[1.98,2]`.  The spectra of `U_1,U_2,U_3` are nearly
  equidistributed and nearly squaring-invariant, with `d_H(spec U, spec U^2)`
  between `0.13` and `0.17`.  The opposite pairs are far from commuting:
  `||[U_0,U_2]||=1.98` and `||[U_1,U_3]||=2.00`.  All of this is consistent
  with the corona basin theorem.
- **Descent cannot see decay.**  Two independent problem sizes, `L=12` and
  `L=28`, converge to the same value `0.310`.  At `L=36` and `L=54` the
  optimizer does *not* reach even the padded twelve-dimensional value that
  item 1 guarantees.  So at the tested sizes, padding beats descent from random
  or matcher starts, and descent cannot detect a slowly decaying profile
  `m_c(L)`.
- **Cycle seeds.**  Cycle seeds are capped by `(HDP4)`: at `L=12` the descent
  reaches the floor `2 sin(pi/12)` and stops.  The primitive-shell matcher
  starts from a cycle, but its floor `2 sin(pi/L)` tends to zero, so the floor
  does not obstruct it.

**Where this numerical route dies.**  Local descent plateaus at `def ~ 0.31`
for `6<=L<=54`.  It matches the padded twelve-dimensional value only at the
sizes where it found that value.  This supports neither a countermodel (no
decay is seen) nor collapse: by monotonicity, an honest decay test needs a
lower bound on `m_c(L)`, and a numerical local minimum gives none.
