---
rg: 2
id: internal-corner-exhaustion-by-uniform-expectations
kind: route
title: "Diagonalize uniform expectation estimates from nearly full internal corners"
target: internal-corners-exhaust-kazhdan-commutants
requires: []
artifacts:
  - research/artifacts/liu-section-six-acceptance-and-thom-bypass-2026-09-20.md
---

## Attribution and scope

This is the independently checked exhaustion argument of Jihao Liu,
[*Nonhyperlinear groups exist*](https://jihaoliu.org/ai-results/nonhyperlinear-groups-exist-2026-09-20.pdf)
(2026-09-20), Proposition 6.6, Steps 2-4. The expectation lift and internal
corners are hypotheses of the target; this proof does not establish their
existence. The downstream conditional normalization/double construction
is due to Andreas Thom, [Theorems 1.2-1.3](https://andreasthom.github.io/pdf/nonhyperlinear.pdf),
and the pair/lamp construction to Gabor Kun and Andreas Thom,
[Theorems A and E](https://arxiv.org/abs/2608.06222). Neither is needed in
the present analytic implication.

Let `C` and the coordinate maps `Phi_n` satisfy the target. Passing to a
subsequence of corner labels if necessary, write
`epsilon_k=tau(1-p_k)->0` with `epsilon_k<1`. Choose projection lifts
`p_k,n` and unital corner algebras `D_k,n` representing `p_k C p_k`.
The unit of `D_k,n` is `p_k,n`. Ambient and corner normalizations have
the same null ideal at fixed `k`, because `tr(p_k,n)->tau(p_k)>0`.

Adjoin scalars to form unital algebras

```text
B_k,n = D_k,n + C(1-p_k,n),
B_k = [B_k,n]_omega = p_k C p_k + C(1-p_k) subset C.
```

The last inclusion does not require `p_k` central. For any contraction
`b in C`, the contraction `p_k b p_k` belongs to `B_k`, and

```text
b-p_k b p_k=(1-p_k)b+p_k b(1-p_k),
||b-E_(B_k)(b)||_2 <= 2sqrt(epsilon_k).
```

Both displayed terms have 2-norm at most `sqrt(epsilon_k)`, by the trace
and operator-norm bound. Since `B_k subset C`, orthogonal projections give
`E_(B_k) E_C=E_(B_k)`. Applying the last estimate to the contraction
`E_C(x)` proves

```text
||E_C-E_(B_k)||_(infinity->2)<=2sqrt(epsilon_k).             (1)
```

Coordinate expectations onto `B_k,n` induce `E_(B_k)`. Indeed their
outputs are bounded lifts in `B_k`, and trace orthogonality against every
bounded sequence from `B_k,n` identifies the output with the orthogonal
projection onto `L2(B_k)`.

We use the following uniform-witness fact. If uniformly operator- and
2-norm-bounded coordinate maps `L_n` induce `L` on all bounded
sequences, then

```text
lim_omega ||L_n||_(infinity->2) = ||L||_(infinity->2).       (2)
```

To prove the upper bound on the left side, choose a maximizing
contraction at each coordinate; its class is a contraction and the
induced-map identity bounds its output. For the converse, every quotient
contraction has contraction lifts: clip the singular values of a bounded
lift at one, which changes its class by zero because the limit positive
part `(|x|-1)_+` vanishes. Apply the coordinate norm bound and then take
the supremum. This uses the stated all-bounded-sequence hypothesis,
including witnesses chosen after the maps; no separability assumption is
made. Near-maximizers suffice if suprema are used instead of maxima.

Apply (2) to `Phi_n-E_(B_k,n)` at each fixed `k`, and then (1). The set

```text
S_k={n: ||Phi_n-E_(B_k,n)||_(infinity->2)
          <=2sqrt(epsilon_k)+1/k}
```

belongs to `omega`. Put `Omega_k={n>=k} intersect (intersection_(i<=k) S_i)`
and let `k(n)` be the largest eligible `k<=n`, or zero if none exists.
Then `k(n)->_omega infinity`. Define `A_n=B_(k(n),n)` when `k(n)>0`,
and `A_n=C I` otherwise. The construction gives
`||Phi_n-E_(A_n)||_(infinity->2)->0`.

Consequently the induced coordinate expectation agrees with `E_C` on
the quotient operator unit ball. Both induced maps are linear, so they
agree on every element of the quotient. Its range is `[A_n]_omega`: one inclusion is immediate
from their outputs, and they fix every bounded sequence from `A_n`.
Equality of the induced maps therefore proves `[A_n]_omega=C` in the
original dimensions. Neither nesting nor a lower bound on any sequence
of scalar gaps is used. This direct proof of the conditional target does
not promote the unrestricted existence of expectation lifts or blocks.
