---
rg: 2
id: common-partial-isometry-swap-game-compiler
kind: claim
title: Compile one static gap game through a common nonlinear partial-isometry swap
distinct_from:
  fanizza-native-signal-groupification: that asks for a uniform finite-matrix decoder for a computable BCS family and feeds a reverse-Kleene diagonal; this is a one-instance static compiler for an already separated commuting-versus-finite game.
  block-encoded-acceptance-still-needs-corner-return: that packages all tests into a cyclic superoperator return and needs a Hecke-corner authentication; this asks instead for one common matrix partial-isometry swap and then uses one ordinary commutator per test.
  capacity-gated-common-corner-bcs-two-cell: that asks for one globally reducing common corner; this only asks for a common partial-isometry source and uses exact graph-swap commutator identities rather than intersection rounding.
---

**OPEN.**  Fix the finite constraint-variable game `G_cv` from
`oracularizable-tracial-nonru-game-exists`, with

```text
omega_co(G_cv)=1,
omega_qa(G_cv)<=theta<1.                               (CPS1)
```

Construct a finite group presentation `Gamma=<X|R>`, a nonidentity marked
involution `J`, and one fixed finite packet decoder with these properties.

1. **Exact completeness.**  The perfect commuting model of `G_cv` extends,
   after arbitrary countable amplification, to an exact unitary
   representation of `Gamma` in which `J` is nonidentity.
2. **Common finite-matrix source.**  In every sufficiently accurate
   canonical-trace matrix model, after exactifying only the fixed finite
   packets, the separated `J` sector supplies a matrix partial isometry `S`
   with

   ```text
   ||S||_2^2>=gamma tau((I-J)/2)-o(1)                 (CPS2)
   ```

   for one `gamma>0` independent of matrix dimension.
3. **One literal swap.**  The same decoded involution is the
   partial-isometry reflection

   ```text
   J_S=[[I-SS^*, S],
        [S^*, -(I-S^*S)]]                             (CPS3)
   ```

   in every predicate and consistency test.  Separate context copies are
   not allowed.
4. **Test rows.**  Fixed packet words decode the context predicate
   reflections `I-2F_c`, the occurrence involutions `A_(c,x)`, and the
   global variable involutions `B_x`.  The presentation contains the
   ordinary commutator relators

   ```text
   [diag(I-2F_c,I),J_S]=1,
   [diag(A_(c,x),B_x),J_S]=1.                         (CPS4)
   ```

   Their approximate decoded defects differ from the literal relator
   defects by `o(1)` with a dimension-independent modulus.

The common-source clause is load-bearing.  A different `S_c` for every
context gives only a convex family of partial strategies and is defeated by
`pairwise-cross-grams-do-not-supply-one-game-state`.  The nonlinear swap
clause is also load-bearing: its truth table is an AND and cannot be forced
inside an abelian parity packet.

## Why these clauses are enough

By `partial-isometry-swap-wordizes-one-bcs-gram-row`, every predicate
commutator in `(CPS4)` controls `4||F_cS||_2^2`, and every consistency
commutator controls `||A_(c,x)S-SB_x||_2^2`, with universal two-sided
constants.  Hence vanishing group-relator defect gives

```text
E_S=o(1).                                              (CPS5)
```

But `one-gram-vector-decodes-a-finite-bcs-strategy` and `(CPS1)` give

```text
E_S>=(1-theta)||S||_2^2.                              (CPS6)
```

Together with `(CPS2)`, a canonical matrix model with separated mark has a
fixed positive relator-energy floor.  The exact commuting model is not
contradicted: its Gram rows vanish, so every commutator in `(CPS4)` is exact.

## Narrow construction problem

The analytic soundness after `(CPS3)` is complete.  The sole new object is a
finite ordinary-group packet which authenticates **one common nonlinear
partial-isometry swap** on the marked carrier while allowing the separate
context representations required by the perfect infinite model.

Finite context packets already name every local predicate reflection, and
countable amplification supplies exact infinite multiplicities.  The known
failure is source alignment: ordinary finite HNN edges either see too little
of the selector type or, when the logical selectors centralize the edge,
force full selector support.  A successful compiler must therefore use a
multi-piece/Hecke or properly-infinite source which is common at the level of
`(CPS3)` but does not globally identify unrelated context observables.

## Attempts

- **One finite common edge group.**  The commuting-selector induction
  barrier forces the selected target type to contain the full compatible
  selector cube.
- **One source per context.**  This loses the single Gram state required by
  the finite game gap.
- **PAZ rank-one graph promotion.**  Its normalized endomorphism trace is
  `Theta(d^(-2))`.
- **Abelian control of `J_S`.**  The controlled-swap truth table is
  nonlinear and cannot be cut out by parity relations.
- **Globally identify all context variables.**  This adds cross-context
  commutation and may destroy the exact perfect commuting representation.

