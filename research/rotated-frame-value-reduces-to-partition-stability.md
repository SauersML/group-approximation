---
rg: 2
id: rotated-frame-value-reduces-to-partition-stability
kind: claim
title: The integral value of the rotated-frame universe rich 2-to-1 game satisfies val^4 <= 4 Stab_T(rho_A), where rho_A is the S_2n-average of the left strategy and T is the pair-resampling walk, so functions of the frame sum cost nothing and vanishing value reduces to one partition-stability bound
distinct_from:
  walsh-frame-rich-2to1-games-have-value-near-one: that shows twisted Walsh frames force value near 1; this concerns the Haar-rotated frame universe, the candidate that node leaves as its survivor, and gives an upper bound on the value in terms of a stability quantity. It proves neither low nor high value.
  perfect-completeness-rich-2to1-tractable-skeletons-are-in-p: that is about reductions and computable skeletons; this is about the integral value of one fixed continuum instance and says nothing about hardness.
  sd-rich-and-unique-games-sos-gaps-interconvert: that moves SoS gaps between games at completeness 1 - eta; this is a soundness-analysis lemma for one perfect basic-SDP candidate and transfers no gap.
  affine-ug-easy-on-globally-hypercontractive-graphs: that uses global hypercontractivity to solve affine unique games algorithmically; here a hypercontractive-type bound would be used in the opposite direction, to certify low value, and the operator is the pair-resampling walk on frames.
artifacts:
  - experiments/pair-resampling-hypercontractivity-2026-09-17/linear_partition_stability.py
---

**ESTABLISHED.** Proof: route `equivariant-partition-stability-reduction-proof`.

**The game `U_(n,d)`.** Fix `d >= 2n`. The game has:

* **Left vertices.** Tuples `X = (x_1, ..., x_2n)` of orthonormal vectors in
  `R^d`, drawn from the Haar (Stiefel) measure `mu`.
* **Edges.** Uniform labelled 2-to-1 maps `P : [2n] -> [n]`, independent of `X`.
* **Right vertex.** `Y = Pi_P X = (y_1, ..., y_n)` with
  `y_b = sum_(a in P^(-1)(b)) x_a`.
* **Constraint.** Left label `a` and right label `b` satisfy the edge iff
  `P(a) = b`.

The value is `val(U_(n,d)) = sup_(A,B) Pr_(X,P)[P(A(X)) = B(Pi_P X)]`, over
measurable `A : left -> [2n]` and `B : right -> [n]`. The vectors `x_a / sqrt(2n)`
and `y_b / sqrt(2n)` form a perfect solution of the GKOPTW basic SDP. This is the
pair-sum identity of `walsh-frame-rich-2to1-value-proof`, Step 0, run backwards.

**Richness.** For each fixed `P`, `Pi_P X` is a Haar-distributed orthogonal
`n`-tuple with squared norms 2, so its law does not depend on `P`. Hence `P` is
independent of `Y` and uniform. So the pairing seen at a random edge of a right
vertex is uniform, and the same holds at a left vertex.

**Operators.**

* `T_P f = E[f(X) | Pi_P X]`, the conditional expectation on `L^2(mu)`, is a
  self-adjoint idempotent.
* Concretely, `T_P` resamples the difference vectors `z_b = x_a - x_a'` uniformly
  among orthogonal `n`-tuples in `span(y)^perp` with squared norms 2, keeping
  `Y`.
* `T = E_P T_P` is the *pair-resampling walk*.
* For `rho = (rho_a)_(a in [2n])` with `rho_a in L^2(mu)`, put
  `Stab_T(rho) = sum_a <rho_a, T rho_a> = E_P sum_a ||E[rho_a | Pi_P X]||^2`.

**Symmetrisation.** `S_2n` acts on left vertices by permuting rows:
`(sigma X)_a = x_(sigma^(-1)(a))`. This preserves `mu` and the frame sum
`s(X) = sum_a x_a`. For a left strategy `A`, put

`rho_(A,c)(X) = Pr_(sigma ~ S_2n)[A(sigma X) = sigma(c)]`.

**Theorem.**

1. `rho_A` is a fractional partition: `rho_(A,c) >= 0` and
   `sum_c rho_(A,c) = 1`. It is `S_2n`-equivariant:
   `rho_(A,c)(tau X) = rho_(A, tau^(-1)(c))(X)`. It is *s-balanced*:
   `E[rho_(A,c) | s] = 1/(2n)` for every `c`.
2. **Reduction.** For every strategy pair `(A, B)`,
   `Pr[P(A(X)) = B(Pi_P X)]^4 <= 4 Stab_T(rho_A)`. Hence
   `val(U_(n,d))^4 <= 4 sup_rho Stab_T(rho)`, with the sup over equivariant,
   s-balanced fractional partitions.
3. **The frame-sum algebra is neutral.** `s = sum_b y_b` is a function of
   `Pi_P X` for every `P`, so functions of `s` are `T`-invariant. For any
   s-balanced `rho`, `Stab_T(rho) >= sum_a ||E[rho_a | s]||^2 = 1/(2n)`. Any
   strategy of the form `A(X) = F(s(X))` has `rho_A = 1/(2n)` identically and
   `Stab_T(rho_A) = 1/(2n)`. For `d = 2n`, `T_P` is
   `f -> E_M f(K_P(M) X)` with `M` Haar on the orthogonal group of
   `span{e_a - e_a'}`, and `K_P(M) = I` on `span{e_a + e_a'}`.
4. **Consequence.** Suppose
   `pair-resampling-walk-balanced-partitions-are-unstable` holds
   for a sequence `d_n >= 2n`. Then `val(U_(n,d_n)) -> 0`, and `U_(n,d_n)` is a
   continuum basic-SDP gap for Gap-Rich-2-to-1_n[1, delta] at every constant
   `delta > 0`. That is the evidence question on
   `rich-2to1-perfect-completeness-conjecture`, up to a finite rich
   discretisation, which is not addressed here.

**Why this is a real reduction, not a restatement.** `T` has a huge invariant
subspace: all functions of `s`, a `d`-dimensional variable. So no spectral gap
or hypercontractive inequality holds for `T` on general indicator partitions.
For example, `A(X) = F(s(X))` has `Stab_T(1_A) = 1`. Item 2 moves the problem to the balanced,
equivariant class. There the invariant part contributes exactly `1/(2n)`, and
what is left is a statement about the walk on the fibres of `s`.

**Pitfall recorded.** Averaging the second strategy over ambient rotations
`Q in O(d)` is not legitimate. `Q` is not random in the test: rotating the
second neighbour changes `Y`. Doing so would give `val <~ n^(-1/4)`, which
contradicts the Monte Carlo value of the linear strategy below. Only the label
relabelling `sigma` is realised by the conditional law, which is why the
reduction lands on `S_2n`-equivariant partitions.

**Computation.** The artifact runs Monte Carlo on `d = 2n` for the linear
equivariant strategy `A(X) = argmax_a <x_a, w>` (then `rho_A = 1_A`), with
`B(Y) = argmax_b <y_b, w>`. Seed `20260918`. Output columns are `n`,
`Stab_T(1_A)`, `val_linear`, then two reference powers.

| `n` | `Stab_T` | `val_linear` |
|---|---|---|
| 4 | 0.30066 | 0.69305 |
| 16 | 0.17242 | 0.48004 |
| 64 | 0.09915 | 0.33921 |
| 256 | 0.05798 | 0.24139 |
| 1024 | 0.03430 | 0.17408 |

Over this range the fitted slopes are about `n^(-0.38)` for stability and
`n^(-0.24)` for value. Item 2 checks out at every row (for example
`0.174^4 = 0.00092 <= 4 x 0.0343`). The inequality loses a fourth power, so it
is far from tight for this strategy.
