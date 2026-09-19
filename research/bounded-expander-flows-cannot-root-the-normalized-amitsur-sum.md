---
rg: 2
id: bounded-expander-flows-cannot-root-the-normalized-amitsur-sum
kind: claim
title: Bounded expander flows cannot give a constant-gap rooted proof of the normalized Amitsur sum
distinct_from:
  uniform-linear-pcpp-tensorizes-to-amitsur-hs: that proves a uniformly rooted scalar linear proof would tensorize without operator loss; this rules out the most natural expander divergence construction of that scalar proof under bounded coefficients and bounded exact amplitudes.
  raw-amitsur-permutation-sampling-has-factorial-gap-loss: that treats proof-free sampling of raw Gram entries; this permits a full auxiliary flow proof and finds a separate constant-mode normalization obstruction.
  bounded-template-all-pairs-additive-decoder: that records dilution at one distinguished equality-fiber port; this proves the general root-leverage bound for linear checks and the exact coefficient/amplitude tradeoff for expander conservation laws.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that positively degree-reduces a pre-existing discrete Pauli test; this shows why the same equality-cloud geometry does not create rooted soundness for a continuous normalized sum.
---

ESTABLISHED.  There are two related obstructions.

## Any bounded-occurrence distinguished root has vanishing leverage

Let a scalar linear proof system have checks indexed by `c`, probability
weights `p_c`, and residuals

```text
r_c=a_(c,t)t+sum_(j!=t) a_(c,j)x_j.                    (BEF1)
```

If its rooted soundness includes

```text
sum_c p_c |r_c|^2 >= kappa^2
 |t-N^(-1/2)sum_i v_i|^2                               (BEF2)
```

for every proof assignment, then setting `t=1` and every other coordinate to
zero gives the necessary bound

```text
kappa^2 <= sum_c p_c |a_(c,t)|^2.                      (BEF3)
```

Thus, for `M` uniformly weighted checks, coefficients bounded by `C`, and a
distinguished root occurring in at most `d` checks,

```text
kappa <= C sqrt(d/M).                                  (BEF4)
```

An expander cloud of bounded-degree root copies does not change `(BEF4)` for
the one copy on which the terminal relation is imposed: changing only that
port violates only its bounded set of incident equality checks.  Constant
rooted soundness requires either constant total test probability on that
literal root, unbounded root occurrence, or a different terminal observable
which is already delocalized over the cloud.

## Expander divergence has an unavoidable square-root tradeoff

Let `G_N` be any connected oriented graph on `N` vertices, of maximum degree
`Delta`; no expansion hypothesis is needed.  Consider the natural flow proof
with edge variables `f_e`, boundary leaves `v_i`, root `t`, and uniformly
weighted vertex checks

```text
r_i=(div f)_i-alpha_N v_i+beta_N t.                    (BEF5)
```

Suppose exact solvability is intended to hold precisely when

```text
t=N^(-1/2)sum_i v_i.                                   (BEF6)
```

Summing `(BEF5)` over the vertices and using `sum_i(div f)_i=0` shows that
exact completeness for arbitrary correct boundary data forces

```text
alpha_N=sqrt(N) beta_N.                                (BEF7)
```

Conversely, because the incidence map of a connected graph has range the
zero-sum vectors, `(BEF7)` makes an exact flow exist for every scalar boundary
satisfying `(BEF6)`.

The best rooted coercivity of these checks is at most `|beta_N|`.  Indeed set
`t=1`, all leaves zero, and all flows zero.  Every residual equals `beta_N`,
so the probability-weighted energy is `|beta_N|^2`, while the rooted error is
one.  Therefore bounded local coefficients `|alpha_N|<=C` imply

```text
kappa_N <= |beta_N|=|alpha_N|/sqrt(N)<=C/sqrt(N).       (BEF8)
```

Trying to retain `kappa_N>=kappa_0>0` forces
`|alpha_N|>=kappa_0 sqrt(N)`.  This also destroys bounded exact Fock
completeness, not only coefficient locality.  On the orthogonal-isometry
boundary of the Amitsur instruction, `||v_i||=||t||=1`, so the exact
divergence demand at every vertex obeys

```text
||alpha_N v_i-beta_N t||_op
 >= |alpha_N|-|beta_N|
 >= kappa_0(sqrt(N)-1).                                (BEF9)
```

Since at most `Delta` signed edge flows contribute to one divergence, some
proof flow has

```text
||f_e||_op >= kappa_0(sqrt(N)-1)/Delta.                 (BEF10)
```

Hence it cannot be stored in one uniformly bounded recursively addressed
operator.  Spectral expansion controls inversion on the mean-zero subspace,
but `(BEF7)` is the constant-mode conservation law and is unaffected by the
expander gap.

This does not rule out every rooted linear PCPP.  It rules out bounded-degree
equality anchoring of one root and the canonical expander flow/divergence
extended formulation.  A surviving construction must use a nonlinear
quantization/gap-amplification step, a delocalized terminal observable which
is itself group-word accessible, or a linear extended formulation not based
on bounded-coefficient conservation of the leaf sum.

