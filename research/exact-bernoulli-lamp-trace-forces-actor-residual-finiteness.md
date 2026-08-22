---
rg: 2
id: exact-bernoulli-lamp-trace-forces-actor-residual-finiteness
kind: claim
title: Exact Bernoulli-lamp trace approximation forces residual finiteness of the actor
distinct_from:
  arithmetic-global-pvm-does-not-bypass-coset-action-gate: that retains only approximately equivariant finite atomic models after rounding a microstate; this theorem uses exact actor normalization and obtains genuine finite actor actions.
  invariant-cartan-completion: that asks an arbitrary matrix-ultraproduct embedding to admit one invariant full diagonal ultraproduct; this theorem begins with exact finite-dimensional representations, where the required finite character actions already exist.
  finite-character-orbits-detect-module-residual: that characterizes residual vectors in an actor module using one finite character orbit; this uses asymptotic Haar lamp trace to find, for every nonidentity actor element, a finite character action on which it moves positive mass.
---

**ESTABLISHED.**  Let `H` be a countably infinite group,

```text
A=direct_sum_H C_2,             W=A rtimes H,
```

where `H` acts by the regular coordinate shift.  Suppose there are exact
finite-dimensional representations

```text
rho_n:W -> U(d_n)
```

such that

```text
tr_(d_n)(rho_n(a)) -> 0                    (BEL1)
```

for every nonidentity `a in A`.  Then `H` is residually finite.

Indeed, restriction to `A` decomposes into its character spaces.  Their
normalized multiplicities define finitely supported probability measures
`mu_n` on

```text
A_hat={-1,1}^H.
```

Exact conjugacy by `rho_n(H)` makes `mu_n` exactly `H`-invariant and makes
the character multiset, with multiplicity, a genuine finite `H`-set.
Condition `(BEL1)` says that every nonconstant Walsh--Fourier coefficient of
`mu_n` tends to zero, hence `mu_n` converges weak-* to Bernoulli product
measure `mu`.

For every `g!=1`, the fixed-coloring set `Fix(g)` is closed and has
`mu(Fix(g))=0`.  Portmanteau therefore gives

```text
limsup_n mu_n(Fix(g)) <= 0.                              (BEL2)
```

For all sufficiently large `n`, `g` moves a point of the finite character
multiset.  The resulting homomorphism from `H` to a finite symmetric group
does not kill `g`.  This holds for every nonidentity `g`, proving residual
finiteness.

The word **exact** is load-bearing.  In a matrix-ultraproduct model, finite
lamp windows can be diagonalized and actor covariance holds in normalized HS
norm, but this supplies only asymptotically equivariant weighted atoms.  It
does not supply a coherent finite `H`-action.  Upgrading it would require the
image of the Bernoulli algebra to lie in one diagonal ultraproduct normalized
by all actor unitaries, precisely `invariant-cartan-completion` (or an
equivalent Cartan/permutation extraction theorem).  Thus the result is an
exact-representation obstruction, not yet an HS obstruction.

