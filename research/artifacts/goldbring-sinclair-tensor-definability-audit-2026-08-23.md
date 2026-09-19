# Goldbring--Sinclair tensor-definability audit

**Source.** Isaac Goldbring and Thomas Sinclair, *On definability of
C*-tensor norms*, arXiv:2509.15086v1 (18 September 2025), especially
Theorem 3.13, Corollary 3.15, Theorem 3.23, Theorem 5.4, and Corollaries
5.5, 5.7, and 5.8.  The supplied PDF
`/Users/user/Downloads/2509.15086v1.pdf` was checked against the official
arXiv record.

## What is genuinely new for Cairn

The paper supplies three rigorous fences around the C*-lifting and
self-aware-compiler routes.

### 1. Uniform maximal-tensor definability is an ultraproduct lifting property

For a C*-algebra `A` and an ultrafilter `U`, property `max-U` says that the
canonical map

```text
A^U tensor_max A^U  ->  (A tensor_max A)^U
```

is isometric.  Theorem 3.13 and Corollary 3.15 show that definability of the
maximal tensor norm over a theory forces property `max-U` for every model
and ultrafilter.  Theorem 3.23 constructs separable algebras failing
`max-U`, using Pisier's ultraproduct characterization of the lifting
property.  Thus there is no uniform first-order maximal-tensor predicate
available as a generic ultraproduct-to-coordinate decoder.

This is relevant to Cairn's LLP route, but it is not itself an LLP
counterexample for a candidate group.  In particular it neither proves nor
disproves LLP of `C^*(F_2 x F_2)` or of the binary Leavitt unit group.

### 2. The standard full C*-presentation of `F_n x F_n` is not computable

Theorem 5.4 proves that if `C` is qc-full then there cannot simultaneously be
computable presentations of `C` and `C tensor_max C` for which both canonical
factor embeddings are computable.  Since `C^*(F_n)` is qc-full and its
standard presentation is computable, Corollary 5.5 gives

```text
the standard presentation of C^*(F_n x F_n) is not computable
```

for every `2 <= n <= infinity`.

Fixing a quotient `C^*(F_infinity) -> C^*(F_n x F_n)`, Corollary 5.7 then
shows that no ucp lift back to `C^*(F_infinity)` is computable in the standard
presentations.  This is stronger than the observation that LP is open: even
if a lift exists, it cannot be the effective compiler required by a Kleene
construction.

### 3. Soft commutation has no computable convergence modulus to exact commutation

Let `C^*(F_n x F_n)_epsilon` be the universal algebra with
`||[u_i,v_j]|| <= epsilon`.  Each positive softening is RFD and its standard
presentation is computable, uniformly in `epsilon`.  Nevertheless Corollary
5.8 proves there is no algorithm which, given a *-polynomial `p` and rational
accuracy `q>0`, chooses `m` such that

```text
| ||p||_(epsilon=1/m) - ||p||_(epsilon=0) | < q.
```

So an effective HS/Boone compiler cannot obtain its runtime-independent
modulus merely by replacing exact cross-commutation with computable
operator-norm softenings and waiting effectively for the maximal tensor norm
to converge.  This is an operator-norm/effectivity fence only.  It does not
rule out a direct normalized-HS inequality which avoids computing the full
maximal tensor norm.

## What the paper does not provide

The paper does not promote a hyperlinear trace to an MF trace, build a
canonical group-factor corner, prove LLP for any non-residually-finite
Kazhdan candidate, or produce a non-hyperlinear group.  Its role in Cairn is
negative but precise: maximal tensor norms, arbitrary ucp lifts, and soft
commutation limits cannot be treated as uniform computable black boxes.
