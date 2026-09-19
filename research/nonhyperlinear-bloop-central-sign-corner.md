---
rg: 2
id: nonhyperlinear-bloop-central-sign-corner
kind: claim
title: Put the explicit no-CE loop BCS in one authenticated central-sign group corner
artifacts:
  - research/artifacts/nonhyperlinear-normal-augmentation-source-audit-2026-08-30.md
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that permits a selected irreducible type of a possibly nonnormal finite subgroup; this asks for the sole nontrivial type of one central C2, which every surviving finite-subgroup image must see.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for a machine-indexed quantitative LCS family; this asks for one exact algebraic corner map for one already explicit fixed no-CE BCS and no approximation modulus.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that proves what an arbitrary nonzero algebraic corner map implies; this isolates the authenticated central-sign construction which forces the sign into the operator-MF radical.
---

Let `B_loop` be the effectively specified finite BCS of
`lin-explicit-fixed-bcs-gap-via-generic-conversion`.  Construct explicitly a
countable group `G`, a nontrivial central involution `J`, and finite
group-ring expressions giving a unital star homomorphism

```text
Phi:A(B_loop) -> q C[G]q,       Phi(1)=q,
q=(1-J)/2.                                                   (BCS1)
```

A recursive presentation of `G` is allowed; finite support localization and
effective Higman promotion may be applied afterward.  No injectivity,
surjectivity, trace classification, quantitative decoder, stability theorem,
or finite-dimensional representation is required.

This is the smallest authenticated exact map gate.  With `K=<J>~=C_2`, its
corner unit `q` is the full augmentation complement `q_K`.  Therefore
`nonhyperlinear-normal-augmentation-corner-kills-mf` implies

```text
1!=J in Rad_MF(G),                                          (BCS2)
```

and supplies an explicit countable weak non-MF group with a named element
killed by every norm-matrix-corona homomorphism, without Property `(T)`.

## Attempts

- `B_loop` already supplies all source data: it has a perfect commuting
  tracial state and a strict finite-dimensional gap, hence no CE tracial
  state.  The missing datum is only `(BCS1)`.
- For an actual LCS, the assignment `y_i |-> qx_i` gives `(BCS1)` in its
  solution group.  Replacing `B_loop` by an LCS with the same tracial/CE gap
  is exactly the still-open nonhyperlinear-group threshold.
- Slofstra's embedding theorem starts from an ordinary marked group; it does
  not convert the additive forbidden-atom relations of `A(B_loop)` into
  group relators.
- The signed-Hecke program solves each local context in a selected
  higher-dimensional packet but remains open at cross-context marginal
  equality.  Even a completed selected-type atlas would not formally have
  unit `q`: a faithful finite-subgroup representation may omit that type.
- Taking `K=C_2` removes this authentication defect but also removes the
  higher-dimensional local matrix block.  Thus a successful construction
  must use genuinely nonlocal finite-support elements of the infinite
  negative corner rather than a larger finite packet or finite Bass--Serre
  transport.
- Taller--Vidick explicitly rule out a generic BCS-to-LCS algebra-morphism
  compiler.  This source-specific central-sign map is not ruled out, but its
  existence already proves the desired new group theorem; it cannot be
  obtained as a harmless uniform syntax translation.
