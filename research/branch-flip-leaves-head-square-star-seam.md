---
rg: 2
id: branch-flip-leaves-head-square-star-seam
kind: claim
title: The branch flip leaves the deep-star frame, while its q-fixed localization retains an independent gauge
artifacts:
  - research/branch-flip-head-square-seam-fence-proof.md
distinct_from:
  head-square-whitehead-loop-preserves-deep-star-flag: that isolates the forked-arm transition in the odd Whitehead cube; this tests the literal branch-flip Weyl on the only two coordinate pairs capable of returning that fork to an anchored arm.
  branch-flip-weyl-joins-complementary-q-child-to-native-head: that uses the full branch flip to join an orthogonal q-child root to the native projective head and obtains an SL13 fence; this tests whether the same flip preserves the positive marked-star Pauli flag while repairing the head-square chart.
  binary-branch-flip-weyl-has-s3-c2-model: that gives a finite character/Pauli model for a complete two-branch exchange; this separates the outer-index and middle-index placements at the literal marked-star fork and also tests the stronger q-fixed corner localization.
  constant-outer-weyls-retain-an-sl3-spectator-on-the-deep-star: that retains the full regular constant-outer gauge after all internal SL3 relations are imposed; this adjoins a coefficient-sensitive fork-to-anchor occurrence and shows that its quotient with the constant Weyl is still a nontrivial Pauli-commutant involution.
---

**ESTABLISHED BRANCH-FLIP SEAM FENCE.**  Retain the notation

```text
A_i=x_(alpha_i,k_i)(a_i),
F_i=x_(alpha_(i+1),k_i)(a_i),
a_i=s_1t_(0^i),       b_i=s_(0^i)t_1,                (BHS1)
```

and let `E_+` denote either the quarter or deeper all-positive `Z` atom in
the marked-star carrier.  Thus the central roots

```text
C_j=x_(alpha_j,2)(q)
```

act as `-1` on the containing star carrier, while the retained anchored
arms `Z_j=B_j=x_(k_j,2)(b_j)` act as `+1` on `E_+`.

Let

```text
w=a_1+b_1=s_1t_0+s_0t_1
```

and place its ordinary Weyl word on the only two coordinate pairs which
can turn the root rectangle of `F_i` into an anchored rectangle.

1. On the outer pair `(alpha_i,alpha_(i+1))`, the branch-flip Weyl sends

```text
F_i |-> x_(alpha_i,k_i)(w a_i),
w a_i=s_0t_(0^i),                                    (BHS2)
```

but it also sends

```text
C_i     |-> x_(alpha_(i+1),2)(b_1),
C_(i+1) |-> x_(alpha_i,2)(b_1),                      (BHS3)
```

because `wq=b_1`.  It therefore leaves the literal q-star carrier before
any reservoir comparison can be made.

2. On the middle pair `(k_i,k_(i+1))`, it sends

```text
F_i |-> G_i=x_(alpha_(i+1),k_(i+1))(a_iw),
a_iw=s_1t_(0^(i-1))t_1.                              (BHS4)
```

This has the root position of `A_(i+1)` but the wrong Pauli type:

```text
[G_i,B_(i+1)]=1,
[A_(i+1),B_(i+1)]=C_(i+1).                           (BHS5)
```

Hence on `E_+`, `G_i` preserves the `B_(i+1)=+1` space while
`A_(i+1)` sends it to the negative space.  Their restrictions cannot be
identified.  The branch flip also sends the two anchored `Z` roots to
non-anchored coefficient roots, so it is not a normalizer of the
all-positive `Z` packet.

Every constant-coordinate conjugate of the original branch-flip Weyl is
one of these two cases if it has an anchored target rectangle; every other
placement misses both anchored root positions.  The same fence covers all
coefficient conjugates `v=rwr^(-1)` by prefix-code monomial units.  An
outer match would require

```text
v a_i=a_i,
```

and hence `vq=q`; but the prefix permutation of `w` is fixed-point-free,
whereas `vq=q` fixes the whole `1` cylinder pointwise, and conjugacy
preserves fixed points.  A middle match would require

```text
a_i v=a_(i+1),
```

which would conjugate the right-support projection `e_i` to its proper
subprojection `e_(i+1)`.  This is impossible for an involution, since
applying the same conjugacy again reverses a strict inclusion.

There is a sharp near miss.  Localize the flip in the complementary
`p=s_0t_0` corner:

```text
w_p=q+s_0wt_0.                                       (BHS6)
```

Then

```text
w_p^2=1,        w_pq=qw_p=q,        w_pa_j=a_j       (BHS7)
```

for every anchored coefficient `a_j`.  The outer Weyl

```text
Theta_i=w_(alpha_i,alpha_(i+1))(w_p)                  (BHS8)
```

therefore preserves `E_+` and gives the exact same-carrier occurrence

```text
Theta_i F_i Theta_i^(-1)=A_i.                         (BHS9)
```

This is stronger than anything supplied by the literal full flip, but it
still does not kill `D_(L_i)` or `D_(X_i)` in `(HSW5)`.  Let `L_i` be the
constant outer Weyl already used there.  In the elementary image,

```text
T_i=L_iTheta_i=diag(w_p,w_p)                          (BHS10)
```

on the two outer coordinates.  It fixes every q-anchored Pauli generator
and `E_+`, but is nonidentity on the complementary `00/01` atoms.  Thus
`L_i` and `Theta_i` induce the same fixed label transport and may still
differ by the nontrivial reservoir involution carried by `T_i`.

This residual freedom has an exact finite model.  Close the finitely many
labelled prefix atoms used in `(BHS1)--(BHS10)` inside their finite binary
matrix-unit group and take its left regular representation.  The signed
star/positive-`Z` idempotent `E_+` is nonzero.  The element `T_i` commutes
with its full anchored Pauli subgroup, is not in that subgroup because it
swaps the unused `00/01` atoms, and acts nontrivially on the multiplicity
space of `E_+`.  All head-square, Whitehead, branch-flip-localization, and
same-carrier occurrence rows are exact in this model.

Consequently the original branch flip and its native prefix-code
conjugates do not repair the HSW5 seam.  Even the q-fixed corner
localization which literally returns `F_i` to `A_i` leaves an independent
identity-label `C_2` gauge.  A successful row must additionally identify
the torus `(BHS10)` with the identity on the selected reservoir, rather
than merely provide a second transporter between the same two Pauli
charts.

All identities are asserted in the elementary image, consistently with
`head-square-whitehead-loop-preserves-deep-star-flag`.  No Property `(T)`,
canonical trace, computation, or literature theorem is used.

DERIVATION
branch-flip-head-square-seam-fence-proof
