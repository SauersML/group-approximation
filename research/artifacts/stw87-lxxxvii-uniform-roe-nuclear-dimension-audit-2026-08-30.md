# STW LXXXVII: uniform Roe nuclear dimension audit (2026-08-30)

## Primary-source status

For a countable discrete bounded-geometry metric space `X`, Winter--Zacharias,
[Theorem 8.5](https://arxiv.org/abs/0903.4914), prove

```text
dim_nuc(C*_u(X)) ≤ asdim(X).
```

Li--Willett, [Theorem 2.2 and Remark
2.6](https://arxiv.org/abs/1705.01290), prove equality at asymptotic dimension
zero and observe that the upper bound then gives equality at value one.
Li--Liao--Winter, [Theorem 7.7](https://arxiv.org/abs/2303.16762), prove the
different statement

```text
dim_diag(ℓ^∞(X) ⊆ C*_u(X)) = asdim(X).
```

Their Remark 2.2(i) gives only `dim_nuc ≤ dim_diag`.  An arXiv title/abstract
search through 2026-08-30 found no subsequent primary source proving the
ordinary nuclear-dimension equality; in particular the finite case `X = ℤ²`
remains outside the located results.  Zhu--Zhang's transfinite nuclear dimension
is a one-sided transfinite upper bound, not the missing ordinary lower bound.

## Equality at infinity without property A

Sako, [Theorem 1.1](https://arxiv.org/abs/1212.5900), proves that property A is
equivalent to nuclearity of the uniform Roe algebra.  If `X` lacks property A,
then `C*_u(X)` is not nuclear, so its nuclear dimension is infinite because
finite nuclear dimension implies nuclearity.  Moreover `asdim(X)` cannot be
finite: Winter--Zacharias would then give finite nuclear dimension.  Hence

```text
X lacks property A  ⇒  dim_nuc(C*_u(X)) = asdim(X) = ∞.
```

This is an unconditional extension of the equality class in the extended
natural numbers, obtained by combining existing theorems; it is not asserted
to be a new literature theorem.

## Subspace-corner reduction

For `Y ⊆ X`, let `p_Y = χ_Y`.  Compression of a finite-propagation operator
on `ℓ²(X)` has the same propagation bound on `ℓ²(Y)`.  Conversely, zero
extension of a finite-propagation operator on `ℓ²(Y)` has the same bound on
`ℓ²(X)`.  Taking norm closures gives

```text
p_Y C*_u(X) p_Y = C*_u(Y).
```

Winter--Zacharias Proposition 2.5 says nuclear dimension does not increase on
hereditary subalgebras, so

```text
dim_nuc(C*_u(Y)) ≤ dim_nuc(C*_u(X)).
```

Consequently, if `asdim(X)=n` and `X` contains a subspace `Y` whose uniform Roe
algebra already has nuclear dimension `n`, then equality holds for `X`.  This
is a rigorous propagation theorem, not a solution: no finite seed `n≥2` is
produced here.

## Why diagonal averaging does not give the reverse inequality

Assume `x≠y` in `X`.  In their two-point matrix corner set

```text
p = (e_xx + e_xy + e_yx + e_yy)/2,
q = (e_xx - e_xy - e_yx + e_yy)/2.
```

These are orthogonal rank-one projections, so the map from `ℂ²` sending its
minimal projections to `p,q` is a *-homomorphism and hence order zero.  For the
canonical diagonal expectation `E_X`, however,

```text
E_X(p) = E_X(q) = (e_xx+e_yy)/2,
E_X(p)E_X(q) = (e_xx+e_yy)/4 ≠ 0.
```

Thus postcomposition with `E_X` destroys order zero.  This rules out the raw
strategy of averaging the return maps in an arbitrary nuclear-dimension
approximation to obtain a diagonal-dimension approximation.  It does not rule
out a subtler diagonal-recovery theorem.

## Exact remaining frontier

The cases not covered by the preceding established results are:

1. `2 ≤ asdim(X) < ∞`, where the missing statement is
   `dim_nuc(C*_u(X)) ≥ asdim(X)`;
2. `asdim(X)=∞` with property A, where `C*_u(X)` is nuclear but it is unknown
   here whether its nuclear dimension must be infinite.

No claim in this audit settles either frontier.
