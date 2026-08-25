---
rg: 2
id: kt-double-canonical-vertex-marginals-admit-large-amalgam-twists
kind: claim
title: Canonical exact vertex marginals of the Kun--Thom double admit large amalgam-commutant twists
distinct_from:
  kt-pair-group-double-is-nonsofic: that is the nonsoficity theorem for the double; this constructs exact finite-dimensional unitary representations and isolates why vertex stability alone cannot upgrade it to non-hyperlinearity
  exact-codensity-does-not-imply-matricial-rcc: that uses a nonarithmetic direct product or a Baumslag--Solitar near-representation; this works for the explicit Kun--Thom pair with exact canonical residual vertex representations and exact agreement on the amalgam
  kt-centralizer-normalization-hs: that concerns the compressor inclusion and a lamp wall for the wreath; this concerns alignment of the two vertex copies over the amalgam in the group double
  canonical-free-double-escapes-uniform-exact-projective-folding: that uses a finite-dimensionally invisible mark in a sofic free double; this uses a visible commutant twist in the explicit nonsofic Kun--Thom amalgamated double
---

**ESTABLISHED.**  Let `Gamma<G` be the explicit Kun--Thom Theorem E pair and

```text
D=G *_Gamma G.                                           (KDT1)
```

There are finite-dimensional exact representations

```text
rho_(0,n),rho_(1,n):G -> U(d_n)                          (KDT2)
```

such that:

1. `rho_(0,n)|Gamma=rho_(1,n)|Gamma` exactly;
2. both normalized characters converge pointwise to the regular character
   of `G`;
3. for one fixed `g in G`,

   ```text
   ||rho_(0,n)(g)-rho_(1,n)(g)||_2 >= sqrt(2).            (KDT3)
   ```

Consequently the pair integrates to an exact finite-dimensional
representation of the amalgamated double at every `n`.  Thus even property
`(T)`, exact vertex representations, exact amalgam agreement, and canonical
regular vertex characters do **not** align the two copies.  Actor/vertex HS
stability alone cannot turn hyperlinearity of the double into residual
finiteness or soficity.  A successful double argument needs a genuinely mixed
character condition on reduced alternating words—equivalently an obstruction
to an asymptotically amalgamated-free unitary in the `Gamma` commutant.

## Construction

Choose `g` in the `SL_d(Z)` factor whose image is nontrivial in a finite
quotient.  There is a finite quotient `a:G->A` with

```text
a(Gamma)={e},                  a(g)!=e.                  (KDT4)
```

Combine `a` with a residual sequence of finite quotients of the residually
finite group `G`, obtaining `q_n:G->K_n` which separates every fixed
nonidentity element eventually and satisfies

```text
k_n=q_n(g) notin L_n=q_n(Gamma).                         (KDT5)
```

Put `sigma_n=lambda_(K_n)` on `ell^2(K_n)`.  Give each left coset in
`L_n\K_n` a sign `epsilon_C in {+-1}` and define

```text
U_n delta_x=epsilon_(L_n x) delta_x.                    (KDT6)
```

Then `U_n` commutes with `sigma_n(L_n)`.  For random independent coset signs,

```text
E ||U_n-sigma_n(k_n)U_n sigma_n(k_n)^*||_2^2=2,          (KDT7)
```

because `L_n x` and `L_n k_n^(-1)x` are distinct for every `x` by `(KDT5)`.
Choose signs realizing at least the expectation, and set

```text
rho_(0,n)=sigma_n o q_n,
rho_(1,n)=Ad(U_n) o sigma_n o q_n.                       (KDT8)
```

They agree on `Gamma`, `(KDT7)` gives `(KDT3)`, and residuality of `(q_n)`
makes both vertex characters canonical.  All relations are exact.

