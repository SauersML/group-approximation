---
rg: 2
id: common-partial-isometry-swap-game-compiler
kind: claim
title: Compile one static gap game through a common nonlinear partial-isometry swap
distinct_from:
  fanizza-native-signal-groupification: that asks for a uniform finite-matrix decoder for a computable BCS family and feeds a reverse-Kleene diagonal; this is a one-instance static compiler for an already separated commuting-versus-finite game.
  block-encoded-acceptance-still-needs-corner-return: that packages all tests into a cyclic superoperator return and needs a Hecke-corner authentication; this asks instead for one common matrix partial-isometry swap and then uses one ordinary commutator per test.
  capacity-gated-common-corner-bcs-two-cell: that asks for one globally reducing common corner; this only asks for a common partial-isometry source and uses exact graph-swap commutator identities rather than intersection rounding.
  shared-multiplicity-commutator-builds-selected-hybrid-row: that constructs every nonlinear predicate row on one selected context type with exact multiplicity cancellation in the final D8 test; this still needs joint promotion of those selected types to the common source.
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

The local finite ordinary-group predicate row is now constructed on every
selected support-menu type.  In
`shared-multiplicity-commutator-builds-selected-hybrid-row`, a doubled
signed-permutation truth table is one commutator `[S_c,P_c]`.  Inner-covariant
implementers have

```text
u_c=S_c tensor R_c,             v_c=P_c tensor T_c,
e_c=[u_c,v_c]=D_c tensor [R_c,T_c].                  (CPS8)
```

The arbitrary factor `[R_c,T_c]` is common to both roles, so the final word
`[e_c,j]` cancels it exactly and is `-1` precisely on rejecting labels.  The
presentation uses `[e_c,j]=1` as the predicate relator.  Support-adaptive
menu types make this exact in every perfect model: its selected support
contains only allowed labels, so the final word is identically `1` there.

One literal variable involution
`d_x` commuting with `z` already has blocks `diag(A_x,B_x)` and introduces
no commutation between unrelated contexts.  The load-bearing unsolved row
is no longer its truth table or orientation.  It is promotion/alignment of
the separately selected context types to the **same** D8 source.  In the
notation of the selected-row construction, the exact remaining axiom is

```text
sum_(c,T) ||([e_(c,T),j]-1)Q_(c,T)||_2^2
 >= kappa E_BCS(S_D8)-o(1)                            (CPS9)
```

for one `kappa>0`, with all rows evaluated on the common partial isometry
`S_D8`.  Separate Plancherel bounds for each `Q_(c,T)` do not imply `(CPS9)`;
the projections can occupy disjoint carriers.  Equivalently one may prove
contextwise selected-type saturation of `S_D8` plus shared-variable
compression alignment.  This is the sole promotion axiom left by the local
D8 compiler.

The absolute orientation bit is no longer open.
`centralizing-d8-word-anchors-relative-row-orientation` adjoins one
centralizing involution `e` for which

```text
[e,j]=1,                    [ze,j]=y.                 (CPS7)
```

Thus a simultaneous wrong relative twist pays the full marked distance,
while arbitrary transported whole-row multiplicity carried by `e` preserves
all row energies.  The shared-multiplicity construction has exactly this
permitted form, so the row's absolute orientation is no longer an additional
open datum.  It still may not ask one ordinary finite-packet word to equal
the nonlinear hybrid reflection on the entire marked regular sector.

`perfect-tracial-bcs-has-one-common-module-swap` proves that this common
swap exists exactly in the standard form of every perfect tracial source.
Thus exact completeness is not asking for a new operator-algebraic
phenomenon.  The open work is only its finite packet localization.

Finite context packets now name every local predicate test word, and
countable amplification supplies exact infinite multiplicities.  The known
failure is only source alignment: ordinary finite HNN edges either see too
little of the selector type or, when the logical selectors centralize the
edge, force full selector support.  A successful compiler must prove
`(CPS9)` by a multi-piece/Hecke or genuinely finite-matrix return which is
common at the level of `(CPS3)` but does not globally identify unrelated
context observables.

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
  absolute bit, and the shared-factor row is compatible with its arbitrary
  whole-row multiplicity.  What remains is the joint carrier inequality
  `(CPS9)`, not another scalar orientation choice.
