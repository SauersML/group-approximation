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
3. **One literal swap.**  The same decoded involution has off-diagonal block
   `S` in the common copy grading.  It may be the partial-isometry reflection

   ```text
   J_S=[[I-SS^*, S],
        [S^*, -(I-S^*S)]]                             (CPS3)
   ```

   in the exact witness.  In finite models its diagonal complement may have
   either dihedral character sign; `dihedral-spin-packet-supplies-common-partial-swap`
   proves that this does not affect the required Gram-row lower bound.
   Separate context copies are not allowed.
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

## Remaining narrow construction problem

The analytic common-source problem is now complete.
`dihedral-spin-packet-supplies-common-partial-swap` shows that the fixed
packet `D_8=<z,j,y>` authenticates the common partial isometry: the odd
`y=-1` spin sector is exactly the paired source, the off-diagonal block of
the one literal generator `j` is the partial isometry, and its normalized
mass is at least half the marked mass.

The remaining object is a finite ordinary-group packet which names the
**hybrid row involutions** `diag(A_(c,x),B_x)` and
`diag(I-2F_c,I)` on that common `z`-grading.  It must allow the separate
context representations required by the perfect infinite model while
keeping the same global-variable action in every negative block.

The first half can be weakened further.  One literal variable involution
`d_x` commuting with `z` already has blocks `diag(A_x,B_x)` and introduces
no commutation between unrelated contexts.  The load-bearing unsolved row
is the oriented nonlinear predicate reflection `diag(I-2F_c,I)`: an
ordinary Boolean word in the `d_x` has the predicate value on **both**
blocks.  The controller rule which erases its negative-block value is the
remaining selected-type/Hecke orientation problem.  The induction audit is
spelled out in `dihedral-spin-packet-supplies-common-partial-swap`.

The absolute orientation bit is no longer open.
`centralizing-d8-word-anchors-relative-row-orientation` adjoins one
centralizing involution `e` for which

```text
[e,j]=1,                    [ze,j]=y.                 (CPS7)
```

Thus a simultaneous wrong relative twist pays the full marked distance,
while arbitrary transported whole-row multiplicity carried by `e` preserves
all row energies.  The remaining issue is narrower: a selected nonlinear
row packet must expose a **relative comparison** tying its extension bit to
this anchor.  It still may not ask one ordinary finite-packet word to equal
the nonlinear hybrid reflection on the entire marked regular sector.

`perfect-tracial-bcs-has-one-common-module-swap` proves that this common
swap exists exactly in the standard form of every perfect tracial source.
Thus exact completeness is not asking for a new operator-algebraic
phenomenon.  The open work is only its finite packet localization.

Finite context packets already name every local predicate reflection, and
countable amplification supplies exact infinite multiplicities.  The known
failure is source alignment: ordinary finite HNN edges either see too little
of the selector type or, when the logical selectors centralize the edge,
force full selector support.  A successful compiler must therefore use a
multi-piece/Hecke or properly-infinite source which is common at the level of
`(CPS3)` but does not globally identify unrelated context observables.

## Attempts

- **One finite common edge group for the hybrid rows.**  The commuting-selector induction
  barrier forces the selected target type to contain the full compatible
  selector cube.
- **One source per context.**  This loses the single Gram state required by
  the finite game gap.
- **PAZ rank-one graph promotion.**  Its normalized endomorphism trace is
  `Theta(d^(-2))`.
- **Abelian control of `J_S`.**  The controlled-swap truth table is
  nonlinear and cannot be cut out by parity relations.  The nonabelian
  dihedral spin packet resolves exactly this issue; no larger nonlinear
  truth-table packet is needed for the swap itself.
- **Globally identify all context variables.**  This adds cross-context
  commutation and may destroy the exact perfect commuting representation.
- **Leave the selected rows in an unanchored comparison cycle.**  A common
  relative `z`-twist survives exactly.  The D8 anchor `(CPS7)` removes the
  absolute bit, but the row-to-anchor comparison word remains part of the
  nonlinear selected-type compiler.
