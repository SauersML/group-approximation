---
rg: 2
id: magic-arrangement-profile-absorption-proof
kind: route
title: Build the controlled Magic Square and classify degree-two contextual profiles
target: magic-square-one-port-is-a-universal-phase-absorber
requires:
  - join-tree-overlap-gadgets-have-no-contextual-escape
---

## 1. A controlled four-dimensional square

Use the Pauli involutions `X,Y,Z` and the following square on `C^2 tensor
C^2`:

```text
A_11=I tensor X,   A_12=X tensor I,   A_13=X tensor X,
A_21=Z tensor I,   A_22=I tensor Z,   A_23=Z tensor Z,
A_31=Z tensor X,   A_32=X tensor Z,   A_33=Y tensor Y.   (MAP1)
```

The entries in each row and column commute.  Direct multiplication gives

```text
product_j A_ij=I                    for i=1,2,3,
product_i A_ij=I                    for j=1,2,
product_i A_i3=-I.                                      (MAP2)
```

Let `rho:L->U(H)` be an operator representation and put
`P_plus=(I+rho(z))/2` and `P_minus=(I-rho(z))/2`.  On
`H tensor C^4` define

```text
rho_tilde(x)=rho(x) tensor I_4                 for x in L,
rho_tilde(a_ij)=P_plus tensor I_4+P_minus tensor A_ij.   (MAP3)
```

The two summands in the second line have orthogonal central supports within
the algebra they generate.  Thus every `rho_tilde(a_ij)` is a self-adjoint
involution.  Commutation within a row or column follows blockwise from
`(MAP1)`.  Equations `(MAP2)` give

```text
product_j rho_tilde(a_ij)=I,
product_i rho_tilde(a_ij)=I                 for j=1,2,
product_i rho_tilde(a_i3)
 =P_plus tensor I_4-P_minus tensor I_4
 =rho(z) tensor I_4.                                     (MAP4)
```

Every new cell commutes with `rho(z) tensor I_4`, so the last LCS context is
valid.  All old relations are preserved by amplification.  This proves the
forward implication in `(MSA3)`; the reverse implication is restriction to
the old generators.

If `rho` is finite-dimensional, so is `rho_tilde`, with dimension multiplied
by four.  If `rho` carries a trace or commuting-strategy state, tensor it
with the normalized matrix trace.  Exact relations, and hence perfect LCS
acceptance, remain exact.

For ports `z_1,...,z_k`, apply `(MAP3)` successively with a fresh
`C^4` factor.  The controlled cells for different squares need not commute
and no such relation is imposed.  Earlier equations are simply amplified by
the identity.  Therefore arbitrary noncommuting source ports are harmless
when each belongs to its own one-port square.

## 2. Sign gauges on an arrangement graph

Consider a connected finite loopless graph `G=(V,E)`.  Associate one
involution `A_e` to each edge and, at each vertex `v`, require the incident
edge involutions to commute and have product `sigma_v I`.  This is the dual
form of a magic arrangement in which every cell belongs to exactly two
contexts.

In additive `F_2` notation, multiplying selected edge observables by `-1`
changes the vertex sign vector by the incidence boundary

```text
partial:F_2^E->F_2^V.                                   (MAP5)
```

For connected `G`,

```text
image(partial)={b in F_2^V:sum_v b_v=0}.                (MAP6)
```

One proof chooses a spanning tree and removes leaves, assigning the leaf edge
to correct the leaf sign.  Hence two sign profiles are related by scalar edge
flips exactly when their total parities agree.  In particular, every
even-parity profile has a scalar realization.

Arkhipov's planarity theorem for magic arrangements
(arXiv:1209.3819, Theorem 20) states that an arrangement is magic exactly
when its intersection graph is nonplanar.  Its planar direction says that
no odd-parity operator realization exists.  Its nonplanar direction gives
one finite-dimensional odd-parity realization; the construction reduces to
the `K_5` and `K_(3,3)` Pauli models along a Kuratowski subdivision.
Paddock--Russo--Silverthorne--Slofstra, `Arkhipov's theorem, graph
minors, and linear system nonlocal games`, Algebraic Combinatorics 6 (2023),
gives a group-theoretic rederivation.

Combine that theorem with `(MAP6)`:

```text
G planar:
  realizable operator profiles = even profiles = scalar profiles;

G nonplanar:
  even profiles are scalar and every odd profile is a scalar edge-sign
  gauge of one finite-dimensional odd profile, so every profile is
  finite-dimensionally realizable.                              (MAP7)
```

This proves the arrangement dichotomy stated in the claim.

## 3. Commuting central ports

Let the desired vertex products be mutually commuting involutions
`B_v` which are required to commute with all new edge observables.  In a
finite-dimensional source representation they have joint spectral
projections

```text
B_v=sum_(sigma in {+1,-1}^V) sigma_v P_sigma.           (MAP8)
```

For nonplanar `G`, choose for every scalar profile `sigma` a
finite-dimensional solution `{A_e^(sigma)}` from `(MAP7)`.  There are
finitely many profiles, so amplify these solutions to a common dimension
`D_G`.  Define

```text
A_e=sum_sigma P_sigma tensor A_e^(sigma).               (MAP9)
```

The operators in `(MAP9)` are involutions, commute in every vertex context,
commute with all `B_v`, and their product at `v` is `B_v tensor I`.
Thus a nonplanar arrangement absorbs every commuting central source profile
with a fixed finite amplification.

For planar `G`, centrality lets every `P_sigma` reduce the gadget.  By
`(MAP7)`, only even profiles may occur.  This is equivalent to the single
condition

```text
product_(v in V) B_v=I.                                 (MAP10)
```

Conversely, if `(MAP10)` holds, use scalar edge-sign solutions on every joint
spectral sector and the construction `(MAP9)`.  A planar arrangement
therefore imposes only the affine parity relation `(MAP10)`, whereas a
nonplanar arrangement imposes no condition at all.

In particular, right-hand-side twists by long-code observables cannot
distinguish dictators from their odd affine hull: the planar case is another
parity equation, and the nonplanar case has a finite-dimensional absorber.
The argument does not cover a connected gadget with two or more
noncommuting source ports that are not central in the gadget algebra.  Such a
multi-port coupling is the exact residual cyclic seam.
