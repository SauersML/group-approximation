---
rg: 2
id: fg-cremona-subgroups-have-arithmetic-linear-part-proof
kind: route
title: Good reduction modulo p is a group of birational maps; generators have it almost everywhere; a linear map with it has determinant prime to p
target: fg-cremona-subgroups-have-arithmetic-linear-part
requires: []
---

Direct proof. Lane proof, not independently reviewed.

## Setup

Write `x = (x_0, ..., x_m)`. Every `f ∈ Bir(P^m_Q)` is `(F_0 : ... : F_m)` with the
`F_i ∈ Z[x]` homogeneous of one degree, without common factor, and with coprime
coefficients altogether. This **primitive representative** `F` is unique up to sign
(Gauss's lemma). For a prime `p`, `F mod p` is not the zero tuple. Let `f_p` be the
rational self-map of `P^m_{F_p}` that it defines.

Call `f` **good at `p`** when both `f_p` and `(f^{-1})_p` are dominant. Let `S_p` be
the set of maps good at `p`.

## Step 1: reduction is multiplicative on good maps

Let `f, g` have primitive representatives `F, G`, with `f_p` and `g_p` dominant.

- **`F_p(G_p)` is not the zero tuple.** The affine cone map `G_p` has dense image in
  `A^{m+1}_{F_p}`: the image is a cone whose projectivization is dense, since `g_p`
  is dominant. Some `F_{i,p}` is a nonzero polynomial, and it cannot vanish on a
  dense set, so `F_{i,p}(G_p) ≠ 0`.
- **The reduction of `f ∘ g` is `f_p ∘ g_p`.** Over `Z`, write
  `F(G) = c · H · K`, where:
  - `c ∈ Z`;
  - `H ∈ Z[x]` is primitive, and is the common factor;
  - `K` is the primitive representative of `f ∘ g`.

  Reducing mod `p` gives `F_p(G_p) = c_p H_p K_p`. The left side is nonzero, so
  `c_p ≠ 0` and `H_p ≠ 0`. A common nonzero factor does not change the rational map,
  so `(f∘g)_p` is the map defined by `F_p(G_p)`. That map is `f_p ∘ g_p`, which is
  defined because `g_p` is dominant.
- **It is dominant**, as a composite of dominant rational maps of the irreducible
  variety `P^m_{F_p}`.

## Step 2: `S_p` is a subgroup

- `id ∈ S_p`, and `S_p` is closed under inverses by definition.
- **Products.** For `f, g ∈ S_p`, Step 1 gives `(fg)_p = f_p g_p`, which is dominant.
  It also gives `((fg)^{-1})_p = (g^{-1} f^{-1})_p = (g^{-1})_p (f^{-1})_p`, which is
  dominant.
- **Reduction is a homomorphism.** Also `f_p ∘ (f^{-1})_p = (id)_p = id`, so `f_p` is
  birational. Hence `f -> f_p` is a homomorphism `S_p -> Bir(P^m_{F_p})`. It is not
  needed below.

## Step 3: each map is good at almost every prime

Let `f ∈ Bir(P^m_Q)` with primitive representative `F`.
- **The Jacobian is nonzero over `Q`.** The cone map `F : A^{m+1} ⇢ A^{m+1}` is
  dominant, since `f` is birational and `F` is not the zero tuple. In characteristic
  0 a dominant map between varieties of the same dimension is generically étale, so
  the Jacobian determinant `J_F = det(∂F_i/∂x_j)` is a nonzero element of `Z[x]`.
- **It stays nonzero mod almost every prime.** For every prime `p` not dividing all
  coefficients of `J_F`, the reduction `J_{F,p}` is nonzero. So `F_p` is étale at
  some point of `A^{m+1}_{F_p}`, its image is dense, and `f_p` is dominant.

Apply this also to `f^{-1}`. Then `f ∈ S_p` for all primes outside a finite set
`N_f`.

## Step 4: the linear part

Let `Γ = <g_1, ..., g_k>` and `N = ∏` of the primes in `N_{g_1} ∪ ... ∪ N_{g_k}`
(`N = 1` if there are none).
- **Every element of `Γ` is good outside `N`.** By Steps 2 and 3, `Γ ⊆ S_p` for
  every prime `p ∤ N`.
- **Linear elements.** Let `f ∈ Γ` be linear, `f = [A]` with `A` a primitive
  integer matrix. Then `f_p = [A mod p]`, and a linear map is dominant iff it is
  invertible. So `p ∤ det A` for every `p ∤ N`.
- **Conclusion.** The integer `det A` has all its prime factors in `N`, so
  `A ∈ GL_{m+1}(Z[1/N])` and `f ∈ PGL_{m+1}(Z[1/N])`.

## Step 5: residual finiteness

`PGL_{m+1}` acts faithfully on `M_{m+1}` by conjugation. So `PGL_{m+1}(Z[1/N])`
embeds in `GL_{(m+1)^2}(Z[1/N])`, a linear group over a finitely generated ring. It
is residually finite through reduction modulo primes `q ∤ N` and their powers
(Mal'cev), and so is every subgroup.

The statement about `φ PGL_{m+1}(Q) φ^{-1}` follows by applying this to the finitely
generated group `φ^{-1} Γ φ`.
