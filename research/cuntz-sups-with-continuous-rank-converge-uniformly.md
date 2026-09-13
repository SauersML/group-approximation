---
rg: 2
id: cuntz-sups-with-continuous-rank-converge-uniformly
kind: claim
title: If a Cuntz-increasing sequence has a supremum with finite continuous rank, the ranks of its terms converge uniformly
distinct_from:
  all-ranks-occur-iff-continuous-ranks-are-dense: that shows exact realization of all ranks is equivalent to uniform density of continuous ranks; this shows that any Cuntz-increasing approximation of one continuous rank is automatically uniform, which turns realizer design into a pointwise selection problem.
  toms-schubert-algebra-continuous-ranks-are-constant: that is the open rigidity conjecture for Toms's algebra, whose attempts use Dini's theorem on tau(h_eps(a)); this is the general lemma for arbitrary increasing approximants of the supremum, not only functional-calculus cut-downs.
---

Let `A` be a unital separable C*-algebra with `QT(A)` nonempty. Let
`[a_1] <= [a_2] <= ...` in `Cu(A)` with supremum `[a]`, and suppose
`tau -> d_tau(a)` is finite and continuous on `QT(A)`.

**Theorem.** `d(a_n) -> d(a)` uniformly on `QT(A)`. Equivalently, for every
`eps > 0` there is `n_0` such that `d_tau(a) - eps <= d_tau(a_n) <= d_tau(a)`
for every `n >= n_0` and every `tau`.

No simplicity, exactness, stable rank or comparison hypothesis is used. The
terms `d(a_n)` need not be continuous. The argument is Dini's theorem applied to
continuous functions squeezed between `d((a - 4/j)_+)` and `d((a - 1/j)_+)`,
plus compact containment `(a - 1/j)_+ << a`. It is elementary and probably
folklore; no literature search was made.

**Use in doubling AH systems.** In Toms's algebra `B`, the branch traces
`sigma_y` (`doubling-ah-finite-stage-continuous-ranks-constant-proof`, Step 1)
satisfy `d_(sigma_y)(b) = beta_M rank b(y) / r_M + c_(b,M)` for `b` at stage
`<= M` and `y in X_M`, with `c_(b,M)` independent of `y`. So a realizer `a` of a
continuous `f`, written as the supremum of finite-stage elements `a_n`, gives
for every `eps` an `n` with

```text
f(sigma_y) - eps <= beta_M rank(a_n)(y) / r_M + c_(a_n,M) <= f(sigma_y)
```

for **every** `M >= stage(a_n)` and **every** `y in X_M`. A realizer must
therefore control fibre ranks pointwise at every point of every deep stage,
not only on average. This is what makes oscillation of fibre ranks, and not
only their mean, the quantity a construction has to kill.

**Model test.** Continuity of `d(a)` is load-bearing. In `C([0,1])`, whose
tracial states are the probability measures, take `a_n >= 0` with open support
`(1/n, 1]`, increasing to `a` with support `(0, 1]`. Then `d_mu(a_n) = mu((1/n,1])`
increases to `d_mu(a) = mu((0,1])` pointwise, but
`sup_mu (d_mu(a) - d_mu(a_n)) = 1` for every `n` (take `mu = delta_(1/(2n))`).
Here `d(a)` is not continuous at `delta_0`, so the hypothesis fails, and so does
the conclusion.

Proof: `cuntz-sups-with-continuous-rank-converge-uniformly-proof`.
