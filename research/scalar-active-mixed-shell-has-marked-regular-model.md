---
rg: 2
id: scalar-active-mixed-shell-has-marked-regular-model
kind: claim
title: Every scalar-active mixed-root shell has a marked finite regular model
distinct_from:
  finite-positive-root-fragments-have-marked-regular-models: that proves local finiteness for arbitrary coefficients by nilpotence, but only inside a positive unitriangular radical; this allows all positive and negative roots because the coefficient algebra is the finite scalar active corner.
  mixed-steinberg-loops-admit-morita-rectangular-model: that changes coefficient object sorts to retain the one-to-two Leavitt table; this is an untyped same-object model of every elementary relation over the literal active idempotent.
  finite-affine-sl3-root-shell-keeps-interior-overlap: that constructs a characteristic-two affine lamp countermodel for a Weyl apartment; this works over the odd splitting field and keeps the actual marked active elementary root.
  full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark: that uses the full non-scalar affine-Leavitt occurrence table and consequently kills the mark in every exact finite-dimensional representation; this isolates the strictly smaller scalar-active shell which still has an exact marked model.
---

**ESTABLISHED.**  Let `k=F_q` be a finite field, let `R` be a unital
`k`-algebra, and let `A in R` be a nonzero idempotent.  For fixed finite
`n`, define

```text
Phi_A:GL_n(k) -> GL_n(R),
Phi_A(M)=I_n+(M-I_n)A.                                  (SAM1)
```

Here the `(i,j)` entry of `(M-I_n)A` is `(M_ij-delta_ij)A`.
Then `Phi_A` is an injective group homomorphism.  In particular the subgroup

```text
H_A=<x_ij(cA):i!=j, c in k> <= GL_n(R)                  (SAM2)
```

is finite (indeed it is the image of the elementary subgroup `E_n(k)`).
This shell contains positive and negative roots simultaneously.  It also
contains their rank-one Weyl words, all Steinberg commutator consequences,
all Weyl conjugacy relations between root positions, and every global
same-object return which is an identity among elementary matrices over the
scalar corner `kA`.

Fix `c!=0` and a root position `(i,j)`.  The marked element

```text
z=x_ij(cA)                                               (SAM3)
```

is nonidentity and has order `p=char(k)`.  Therefore the left regular
representation of the finite group `H_A` is an exact finite-dimensional
unitary model of **every finite scalar-active mixed-root fragment** and
satisfies

```text
tau(lambda(z))=0,
||lambda(z)-I||_2=sqrt(2),
tau(1-1_{ {1} }(lambda(z)))=(p-1)/p.                   (SAM4)
```

For the affine-Leavitt programme this rules out the first apparent repair of
`finite-positive-root-fragments-have-marked-regular-models`.  Adding the
opposite active root, the active rank-one braid, its Weyl/Whitehead word, any
finite collection of Weyl conjugates, or even the complete finite elementary
shell over `kA` creates no normalized-Hilbert--Schmidt payment at all.  The
marked regular model has zero relator defect.

Consequently the first potentially load-bearing mixed relation must use a
coefficient outside `kA`: a literal branch inclusion/projection such as
`s_i,t_i`, a proper prefix partial equivalence, or another non-scalar
Leavitt coefficient.  Moreover it must use that coefficient in a row which
cannot be evaluated in the typed Morita model of
`mixed-steinberg-loops-admit-morita-rectangular-model`; otherwise that model
still changes the object identity and avoids the same-reservoir return.

This theorem does not give a model of the full signed Whitehead amalgam.  Its
non-scalar coefficients `x=s_(00)t_0` and `y=s_0t_(00)`, together with the
full occurrence table, are precisely what lie outside `(SAM1)--(SAM2)`.
`full-signed-whitehead-amalgam-has-fd-invisible-clifford-mark` proves that
those additional rows eliminate all exact finite-dimensional marked models.
Promoting that exact collapse to a uniform HS payment remains the open gate.

DERIVATION
scalar-active-mixed-shell-regular-proof
