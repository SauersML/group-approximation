---
rg: 2
id: carmichael-energy-uniform-criteria-incomparable
kind: claim
title: The uniform and subquadratic-energy Carmichael criteria are incomparable
artifacts:
  - research/artifacts/thompson-subquadratic-carmichael-energy-2026-08-24.md
distinct_from:
  subquadratic-carmichael-energy-collapse: that is the energy criterion and its collapse theorem; this compares that criterion with the uniform one and exhibits packets separating them in both directions.
  thompson-carmichael-collapse: that is the uniform complete-graph criterion itself; this proves that neither it nor the energy criterion implies the other, so neither target may be retired in favour of the other.
  literal-one-cell-carmichael-cliques-are-uniformly-finite: that is a free-group obstruction to a fixed finite edge-word template; this is a two-directional non-implication between two analytic criteria, proved by explicit permutation matrices with no word combinatorics.
---

Two sufficient criteria for collapsing a conjugacy packet are in play.  Write
`(UNI)` for the uniform criterion of `thompson-carmichael-collapse`, in the
form used by `thompson-v-r5-coherent-carmichael-family`:

```text
||X_i^3-I||_2 <= C def_R(U),
||(X_iX_j)^2-I||_2 <= C def_R(U)          for all i!=j,       (UNI)
```

and `(ACE)` for the subquadratic energy criterion of
`subquadratic-carmichael-energy-collapse`:

```text
E_M = sum_(i<j)||(X_iX_j)^2-I||_2^2 = o(M^2).                 (ACE)
```

**Neither implies the other.**  Both are sufficient for collapse, and the
uniform target may not be retired in favour of the energy target.

## Failure of `(UNI) => (ACE)`

`(UNI)` bounds each of the `M(M-1)/2` edges by `C def_R(U)`, so it yields only

```text
E_M <= C^2 def_R(U)^2 M(M-1)/2,
```

which is `Theta(M^2)` whenever the defect is positive.  The bound is attained.
Take `d=3`, let `B` be the cyclic permutation matrix of order `3`, and take the
constant packet `X_i=B`.  Then `X_i^3=I` exactly, `(X_iX_j)^2=B^4=B`, and

```text
||B-I||_2^2 = (1/3)tr(2I-B-B^*) = 2,
```

so every edge defect equals `sqrt2` uniformly in `M` while
`E_M = 2 C(M,2) = M(M-1)`.  Thus a family can satisfy the uniform shape at a
fixed positive scale for every `M` and still fail `(ACE)` by a constant factor.

The two criteria therefore convert their hypotheses differently: `(UNI)`
transports its own scale into the conclusion `||B-I||_2 <= 2 C def_R(U)`,
whereas `(ACE)` is a genuine limit statement whose conclusion
`||B-I||_2 <= ||B^3-I||_2` carries no scale at all.

## Failure of `(ACE) => (UNI)`

Take `d=4`, let `B` be the `4`-cycle permutation matrix `Be_k=e_(k+1 mod 4)`,
and let `W` be the permutation matrix of the transposition `(1 2)`.  Then
`B^4=I`, and `WBW^*` is the `4`-cycle `(1 3 4 2)`, so the product
`B(WBW^*)` is the `3`-cycle `(1 4 3)` and

```text
||(B WBW^*)^2 - I||_2^2 = (1/4)tr(2I-P-P^*) = 3/2,      P=(1 3 4),
```

a fixed positive number.  For each `M` choose `S_M` with
`|S_M| = ceil(sqrt M)` and set

```text
X_i = B            for i not in S_M,
X_i = W B W^*      for i in S_M.
```

Pairs inside the bulk and pairs inside `S_M` both give `(X_iX_j)^2 = B^4 = I`
exactly.  Only the at most `|S_M| M <= M^(3/2)+M` mixed pairs are nonzero, each
contributing `3/2`, so

```text
E_M <= (3/2)(M^(3/2)+M) = O(M^(3/2)) = o(M^2),
```

while the maximal edge defect is `sqrt(3/2)`, bounded away from `0` uniformly
in `M`.  Evaluating in the presentation `<x | x^4>` at `U(x)=B` makes
`def_R(U)=0`, so `(UNI)` demands every edge defect vanish and fails outright
while `(ACE)` holds.

## Two corollaries

The second packet also shows `(SCE)` is **sharp**: `B^3=B^*` gives
`||B-I||_2=||B^3-I||_2`, so a packet witnessing `(ACE)` need not force `B=I`.
Separate control of the cube defect is genuinely required.

And a packet witnessing `(ACE)` need not be uniform, need not be exact on any
positive fraction of a fixed edge set, and need not have any per-edge
certificate — only a sublinear-density bad set.  That is the sense in which
`(ACE)` is weaker per edge, and the two displays above are the sense in which
it is stronger in aggregate.
