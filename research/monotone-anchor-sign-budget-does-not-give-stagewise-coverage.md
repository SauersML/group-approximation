---
rg: 2
id: monotone-anchor-sign-budget-does-not-give-stagewise-coverage
kind: claim
title: A monotone anchor-sign budget does not give one-cut-per-stage operator coverage
distinct_from:
  odd-spectral-anchor-resets-have-monotone-sign-budget: that proves exact trace summability for arbitrary successive odd-square cuts; this shows that trace summability does not bound how many cuts are required before every retained odd part is operator-small.
  translated-three-site-blocks-defeat-global-peeling: that spreads sparse obstruction locations to refute one GLOBAL coordinate reset set; this keeps one fixed anchor and refutes a stagewise PHYSICAL-cut coverage inference even though every cut is central and has zero boundary.
  single-spike-split-or-charge-has-fourth-root-modulus: that gives a one-spike cheap-split versus small-mass dichotomy; every spike here lies in the cheapest possible branch, yet their number is unbounded.
---

For every `N`, let

```text
M_N=direct_sum_(j=1)^N M_2(C)
```

with equal central weights, and let `z_j` be the central unit of the `j`th
block.  Write `X,Z` for Pauli reflections.  Define one anchor and `N` sites
by

```text
A|_(z_j)=Z,
B_i|_(z_j)=X if j=i, and Z if j!=i.                      (MCV1)
```

Then for

```text
Y_i=(B_i-A B_i A)/2,       R_i=Y_i^2,
```

one has exactly

```text
Y_i=z_i X,       R_i=z_i.                               (MCV2)
```

Thus every positive spectral cut of `R_i` is `p_i=z_i`.  It is central, so
its actual boundary against the WHOLE tuple is zero.  Resetting the anchor
to `+1` on `p_i` deletes exactly `tau(p_i)/2=1/(2N)` of negative anchor mass,
as in `odd-spectral-anchor-resets-have-monotone-sign-budget`.

After resetting any subset `J` of these cuts, the current anchor is `+1` on
the blocks in `J` and remains `Z` elsewhere.  For every `i notin J`, its
current odd square is still

```text
R_i=z_i,       ||Y_i||_infty=1.                         (MCV3)
```

Consequently after any `k<N` successive resets there is a retained odd part
of operator norm one.  The negative projections decrease monotonically and

```text
sum_i tau(p_i)=1=2tau((1-A)/2),                          (MCV4)
```

so the exact sign budget is saturated, not violated.  Even COMMUTING,
zero-boundary later cuts therefore need `N` steps for coverage.

At the same time this is a diffuse low-energy family.  For the tuple
`(A,B_1,...,B_N)`, with `L=N+1`,

```text
||[A,B_i]||_2^2=4/N,
||[B_i,B_j]||_2^2=8/N       (i!=j),                     (MCV5)
```

and hence its normalized complete-pair energy is `O(1/N)`.  One reset
removes only `1/N` of the anchor's spike blocks and does not produce a
geometric decrease.

Therefore the proposed rule “one boundary-heavy cut per anchor per
geometric energy stage” does not by itself make all retained odd parts
operator-small.  A valid coverage theorem must batch a trace-weighted family
of central cuts, or prove that the balanced parity relations forbid this
many disjoint cheap spike blocks.  Monotone sign mass controls total reset
TRACE, not the number of operator-norm obstructions.

This is not a countermodel to the balanced overlay: `(MCV1)` does not assert
its local all-dual parity relations.  It is a sharp no-go for deriving
coverage from spectral geometry, complete-pair energy, zero boundary, and
the monotone sign budget alone.

