---
rg: 2
id: finite-dimensional-nielsen-cocycle-models-kill-mark
kind: claim
title: Every exact finite-dimensional equivariant model of the Kun--Thom Nielsen radical kills the marked free generator
distinct_from:
  finite-quotient-blindness: That only collapses the image of Gamma inside genuine finite quotients of G; this treats arbitrary finite-dimensional noncommutative C-star models of the free radical and recovers the missing affine basepoint through a cocycle.
  infranormal-compact-closure-normal: That is the compact-image normality theorem used here; this is its new application to the affine Nielsen action on the even free-lamp radical, where no Gamma-fixed lamp generator belongs to the radical itself.
  lamp-coordinate-collision-obstruction: That rules out finite coordinate identifications by a second-moment calculation; this rules out every exact finite-dimensional equivariant quantum model, including non-coordinate matrix models.
  compression-defect-dies-in-finite-dimensions: That kills intrinsic centralizer-defect words in finite-dimensional representations of the whole compression group; this kills a named free basis element in finite-dimensional equivariant representations of the split radical by a nonabelian cocycle argument.
artifacts:
  - notes/UNIQUE_TRACE_KUN_THOM_DOUBLE.md
  - research/artifacts/hyperlinear-q34-literature-2026-08-18.md
---

Let `Gamma < G` be a compressor-generated infranormal pair, put
`X = G/Gamma`, `o = Gamma`, and write the even free-lamp radical as

```text
N = F({b_x : x in X - {o}}),                 b_o = 1,
alpha_g(b_x) = b_(g x) b_(g o)^(-1).                       (NCM1)
```

Let `H = <<Gamma>>_G`.  For every `h in H` and every exact
finite-dimensional equivariant model consisting of

```text
B                         a finite-dimensional unital C-star algebra,
beta : G -> Aut(B)        an action,
theta : N -> U(B)         a homomorphism,
theta(alpha_g(n)) = beta_g(theta(n)),                       (NCM2)
```

one has

```text
theta(b_(h o)) = 1.                                        (NCM3)
```

In particular, choose the strict Kun--Thom mark `h in H` with `h o != o`.
No sequence of exact finite-dimensional equivariant models of `(N,alpha)`
can converge strongly to its reduced regular model: every stage sends the
nontrivial free generator `b_(h o)` to `1`, whereas

```text
||lambda_N(b_(h o)) - 1|| = 2.                              (NCM4)
```

This closes the direct use of the exact-action ambient-strong-convergence
framework of Gao--Kunnawalkam Elayavalli--Mj, arXiv:2607.29571,
Proposition 2.3, for the split Kun--Thom double.  Their proposition is valid;
the missing ambient models cannot have exact finite-dimensional `G`-actions.
The obstruction is not coordinate classicality: `B` may be any
finite-dimensional noncommutative C-star algebra and `beta` may be inner and
fully quantum.

## Scope

The theorem does **not** decide whether `C*_r(N semidirect G)` is MF or
whether the double is hyperlinear.  An MF embedding only gives actions and
radical representations which are exact after passing to a matrix corona;
the coordinate maps may both have vanishing operator-norm defects rather than
being exact at every stage.  Thus the surviving route is sharply identified:
it must use genuinely asymptotic finite-dimensional actions, and the cocycle
`g -> b_(g o)^(-1)` must retain order-one normalized-HS mass while escaping
compact-image reversal.

This escape is real for compressor pairs in general, not merely a logical
possibility.  `sofic-nielsen-charts-defeat-uniform-compact-collapse` constructs
one fixed monomial ascending-HNN pair with finite-dimensional commutative
models whose local action and covariance defects vanish while the strict
Nielsen mark stays at distance `sqrt(2)`.  Therefore compact recurrence has no
dimension-free approximate form even for that fixed pair.  A corresponding
theorem for the Kun--Thom pair would have to use its extra nonsofic/Kazhdan
geometry.
