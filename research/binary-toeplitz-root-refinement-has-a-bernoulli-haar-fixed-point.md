---
rg: 2
id: binary-toeplitz-root-refinement-has-a-bernoulli-haar-fixed-point
kind: claim
title: Binary Toeplitz root refinement has an exact Bernoulli Haar fixed point
distinct_from:
  finite-vn-toeplitz-coefficient-reconstruction-fails: that uses the faithful regular representation to rule out reconstruction of a directly finite coefficient ring; this computes the complete joint law of the binary defect roots and shows that even independent-child spectral refinement has a nontrivial fixed point.
  agent-free-compressor-toeplitz-cell-shift-window-is-lef: that gives finite cyclic models of bounded cell-shift windows; this is an exact all-depth tracial model of the binary root-refinement equation and does not assert finite approximability.
  binary-schur-canonical-weights-have-half-reservoir-escape: that constructs the stationary finite-packet multiplicity ray; this identifies the sharper stationary law of the Toeplitz defect root subgroup itself.
---

**ESTABLISHED.**

Let `Rsharp`, `Sigma`, `P`, `Gsharp`, and `Hsharp` be the binary
Schur--Toeplitz objects of `binary-schur-child-toeplitz-self-embedding` and
`binary-schur-toeplitz-one-branch-hs-payment`.  Thus the coefficient field has
odd characteristic `p`,

```text
e_j=x^j P y^j,                    j>=0,
w_j=x_12(e_j) in Gsharp,
Hsharp=<Gsharp,t | t g t^-1=Sigma(g)>.
```

The defect idempotents are nonzero and pairwise orthogonal.  Their normal
forms `E_jj tensor P` in

```text
<P> ~= M_fin(N,I)
```

show more strongly that they are linearly independent over the prime field.
Root additivity and injectivity of the elementary root map therefore give

```text
<w_0,w_1,...> ~= direct_sum_(j>=0) C_p.                 (BRF1)
```

Indeed, for finitely supported `a_j in F_p`,

```text
product_j w_j^(a_j)=x_12(sum_j a_j e_j)=1
```

if and only if every `a_j=0`.

Let `tau` be the canonical trace in the left group von Neumann algebra
`L(Hsharp)`.  Since the ascending HNN normal-form theorem embeds `Gsharp` in
`Hsharp`, `(BRF1)` remains valid there.  Consequently

```text
tau(product_j w_j^(a_j)) = 0                            (BRF2)
```

for every nonzero finitely supported vector `(a_j)`.  Thus the commuting
order-`p` unitaries `w_j` are an exactly independent iid family, each with
the uniform spectral measure on the `p`th roots of unity.

The binary Toeplitz formula gives, at every depth,

```text
Sigma^n(P)=sum_(0<=j<2^n)e_j.
```

Hence root additivity and stable-letter covariance yield the exact identity

```text
t^n w_0 t^-n
  = x_12(Sigma^n(P))
  = product_(0<=j<2^n) w_j.                             (BRF3)
```

In particular, `w_0` is conjugate to the product `w_0 w_1` of two
independent copies having the same law as `w_0`.  This does **not** force
`w_0=1`: both sides of `(BRF3)` have the uniform order-`p` Haar law, and

```text
||w_0-1||_2^2=2.                                        (BRF4)
```

Equivalently, if `mu` denotes the spectral law of an order-`p` unitary and
the two children are independent copies, conjugacy supplies the scalar
functional equation

```text
mu = mu star mu.                                        (BRF5)
```

For prime `p`, `(BRF5)` has exactly two probability solutions on `C_p`:
the point mass at the identity and uniform Haar measure.  This follows
without an external idempotent-measure theorem.  For every character `chi`,
Fourier transformation gives

```text
hat(mu)(chi)=hat(mu)(chi)^2,
```

so every Fourier coefficient is zero or one.  If a nontrivial coefficient
is one, equality in the triangle inequality says `chi=1` almost surely;
because a nontrivial character of `C_p` is faithful, `mu` is the identity
point mass.  Otherwise all nontrivial coefficients vanish and `mu` is Haar.
The canonical trace above realizes the second alternative.

Therefore no argument using only exact tracial identities, stable-letter
conjugacy, spectral measures, and even exact transverse independence of all
binary descendants can prove collapse of the marked root.  A proof of
`binary-schur-toeplitz-one-branch-hs-payment` or
`hs-schur-toeplitz-root-defect-collapse` must use information absent from
this model: a matricial-lift/direct-finiteness constraint or a genuinely
oriented one-branch payment.  This claim does not assert that `L(Hsharp)` is
Connes embeddable and hence is not a matrix-ultraproduct counterexample.
