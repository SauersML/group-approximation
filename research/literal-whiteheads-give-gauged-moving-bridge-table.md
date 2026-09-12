---
rg: 2
id: literal-whiteheads-give-gauged-moving-bridge-table
kind: claim
title: The literal Whiteheads give the exact moving bridges but retain the selector gauge
artifacts:
  - research/literal-whitehead-moving-bridge-proof.md
distinct_from:
  el20-six-moving-coefficient-square-bridges: that asks for bridges typed as identity on the reservoir; these have exact full Grams and exact squares but carry the same reservoir gauge as the native transition.
  incoming-lagrangian-refinement-preserves-hecke-actor-support: that rules out pure Pauli bridges by actor support; these use the necessary subgroup-moving Whitehead quotient.
  moving-order-seven-stage-gauges-have-coboundary-drift: that constructs arbitrary chart drift abstractly; this identifies the canonical concrete bridge and shows why its square does not measure that drift.
---

**ESTABLISHED EXACT GAUGED BRIDGES.**  For row `i=1,2`, put

```text
t_i=J_iv_i,                 v_1=B_2A_1,   v_2=B_3A_2,
Q=e_(L_0,lambda_0),         Q_(i,k)=t_i^kQt_i^(-k).    (LWB1)
```

Both `v_i` normalize the signed Hecke pair `(L_0,lambda_0)`.  Consequently

```text
J_iQJ_i^(-1)=t_iQt_i^(-1).                             (LWB2)
```

The six conjugates

```text
R_(i,k)=t_i^kJ_it_i^(-k),             0<=k<=6,         (LWB3)
```

are therefore actual full-Gram transports

```text
R_(i,k)^*R_(i,k)=Q_(i,k),
R_(i,k)R_(i,k)^*=Q_(i,k+1)                             (LWB4)
```

after restriction to their source and range cuts.  They obey the exact
six-square table

```text
t_iR_(i,k)=R_(i,k+1)t_i,              0<=k<=5.         (LWB5)
```

Thus the missing transport and covariance are not combinatorial: the two
literal Whiteheads and their Singer conjugates already provide them on the
common positive signed Hecke carrier.

They do **not** establish `el20-six-moving-coefficient-square-bridges`.
The native/Hecke discrepancy being synchronized is precisely the
multiplicity gauge of `J_i` relative to `v_i`.  If the stage chart types
the native transition with gauge `D_(i,k)`, then `(LWB3)` types as

```text
R_(i,k)=N_(i,k) tensor D_(i,k)+o_2(1),                 (LWB6)
```

not `N_(i,k) tensor 1+o_2(1)`.  Substitution in `(LWB5)` cancels the same
gauge on both sides and gives no estimate on
`D_(i,k+1)-D_(i,k)`.  This is the concrete gauged version of the
tautological head bridge, not the ungauged parallel edge required by the
six-square lemma.

Within the seven-coordinate actor quotient this conclusion is sharp.  The
coset carrying `L_0` to `t_iL_0t_i^(-1)` contains no single transvection;
its unique permutation representative is the swap implemented by `J_i`.
Hence neither a root nor a dual Pauli translation supplies a simpler
subgroup-moving bridge.  A successful construction still needs an
independently authenticated full-EL20 coefficient occurrence whose
reservoir action is trivial.  No Property `(T)`, Kazhdan input, or
literature theorem is used.

DERIVATION
literal-whitehead-moving-bridge-proof
