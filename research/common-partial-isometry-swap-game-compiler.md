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
notation of the selected-row construction, put

```text
E_pred(S_D8)=sum_c mu_c ||F_c S_D8||_2^2.
```

The exact remaining axiom is

```text
sum_(c,T) ||([e_(c,T),j]-1)Q_(c,T)||_2^2
 >= kappa E_pred(S_D8)-o(1)                           (CPS9)
```

for one `kappa>0`, with all rows evaluated on the common partial isometry
`S_D8`.  Separate Plancherel bounds for each `Q_(c,T)` do not imply `(CPS9)`;
the projections can occupy disjoint carriers.  Equivalently one may prove
contextwise selected-type saturation of `S_D8` plus shared-variable
compression alignment.  This is the sole promotion axiom left by the local
D8 compiler.  The right side must be the predicate energy, not the full BCS
energy: the displayed left side contains no consistency-row commutator.  The
already constructed literal rows `[d_x,j]` control
`sum_(c,x)mu_(c,x)||A_(c,x)S_D8-S_D8B_x||_2^2` separately.  Adding those
inequalities to `(CPS9)` gives the full `E_BCS(S_D8)` estimate used in
`(CPS5)--(CPS6)`.

### Exact audit of the proposed saturation mechanisms

None of the existing common-source lemmas proves `(CPS9)`.

1. `common-source-hnn-bridges-need-one-gram-saturation-identity` proves that
   the scalar deficit

   ```text
   sum_c ||(1-p_c)U_cQ||_2^2
   ```

   is sufficient for common-source polar rounding, and its regular-packet
   model proves that ordinary HNN edges do not force the deficit to vanish.
   It identifies the missing datum; it does not supply it.
2. `exhaustive-marked-type-energy-summation` sums already available
   typewise inequalities over the mutually orthogonal central isotypic
   projections of **one fixed packet**.  The projections `Q_(c,T)` here come
   from separately amalgamated context packets and are not one common
   orthogonal decomposition of the D8 source.  Moreover
   `algebraic-exhaustive-marked-type-detectors-violate-induction` rules out
   obtaining the needed exhaustive typewise bounds from the selected SMC
   word identities alone.
3. `dihedral-spin-packet-supplies-common-partial-swap` gives the same literal
   `S_D8` and its mass floor for every row, but says nothing about how much of
   that source lies in a selected context carrier.  The exact amalgam model
   in `role-hyperoctahedral-type-has-an-orthogonal-amalgam-model` makes two
   selected carriers orthogonal while retaining the common D8 restriction,
   decisively refuting saturation from D8 compatibility alone.
4. `orthogonal-hecke-row-packs-common-source-energy-into-one-root` preserves
   the sum of a list of covariance norms once those coefficients already
   occupy one reservoir.  It does not authenticate the root coefficient or
   identify its source with `S_D8`; `hecke-dilation-gram-no-go-proof` exhibits
   precisely the surviving source deficit.
5. Replacing the scalar bus by finitely many nonscalar conjugates of the
   selected context block still fails if the conjugating swaps preserve the
   context selector algebra and its allowed support.
   `predicate-preserving-nonscalar-frames-miss-forbidden-source` proves that
   every pulled-back carrier then lies below the same allowed spectral
   projection, so the forbidden source atom is a literal common kernel and
   each bridge has full leakage on it.  Free/generic relative position on the
   allowed part cannot produce `(CPS9)`.  A surviving transporter must mix
   selector and payload non-equivariantly and nevertheless return to the one
   shared-variable row.

The non-equivariant alternative now has a dimension-free payment theorem.
`nonscalar-frame-or-selector-mixing-pays-forbidden-source` proves that if
such transports supply an actual operator frame on the common D8 source,
then every part of that frame crossing the forbidden selector wall is
charged by the selector-intertwining residuals.  Hence the next construction
may break predicate equivariance, but it must wordize those mixing residuals
as consistency rows.  The remaining finite target is one literal common-
source frame, not another predicate-preserving carrier family.

There is a zero-defect firewall on how that frame can be groupified.
`algebraic-selector-mixing-frame-collapses-forbidden-sector` proves that an
operator frame supplied universally by a finite Weyl, controlled-Fourier, or
finite Morita packet, combined with exact wordized mixing rows, forces the
forbidden source projection to vanish in `C^*(Gamma)`.  This contradicts a
phase-safe embedding of the full marked selector packet.  Therefore the
frame lower bound itself must be matrix-only or canonical-trace-only; the
obvious exact finite Weyl tight-frame realization cannot close `(CPS9)`.

The obstruction already appears in the smallest possible concrete packet.
`two-qubit-pauli-frame-covers-common-d8-source` splits the target of one D8
swap by a transverse Pauli, obtaining a two-atom frame with exact bound one;
one four-letter D8 Gram word measures the selector-mixing residual exactly.
Imposing that word forces the forbidden source atom to vanish.  Thus even the
minimal order-thirty-two Pauli frame is useful only as a residual wordizer,
not as the universal lower-bound certificate required by `(CPS9)`.

Thus `(CPS9)` is neither a consequence of exhaustive summation, the D8 mass
floor, nor Hecke packing.  A proof must add a genuinely finite-matrix
same-reservoir inequality which rules out the established orthogonal-amalgam
model; repackaging the existing local rows cannot do so.

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

Once the trace-level saturation inequality `(CPS9)` is proved, no further
vector-state promotion is needed.  By
`centralized-gram-row-words-upgrade-trace-gap-to-vector-gap`, add the finitely
many ordinary relations `[q_j,s]=1`, where the `q_j` are the literal Gram-row
words and `s` ranges over the finite generating set.  Their total defect then
becomes central, `(CPS9)` upgrades to an operator inequality on the marked
sector, and every finite-dimensional vector state pays the same gap.  These
relations preserve exact completeness because all `q_j=1` in the
standard-form perfect model.  Thus the remaining issue is genuinely the
trace-level nonlinear predicate/source alignment, not a hidden conversion
from normalized trace to arbitrary vector states.

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
- **Take a free frame of nonscalar selected-type conjugates.**  If the stable
  letters preserve the predicate support so that all copies are semantically
  the same row, their pulled-back type projections have the forbidden source
  atom as a common kernel.  If they do not preserve that support, the rows are
  no longer conjugate copies of the same predicate and their consistency with
  the literal shared variables becomes a new payload-mixing relation.  Thus
  free position alone does not solve the alignment seam.
- **Use an exact finite Weyl/controlled-Fourier mixer.**  Its tight-frame
  identity is an operator inequality in the finite packet algebra.  Once the
  mixing residuals are ordinary defining words, compressing that identity to
  the forbidden atom makes the atom zero in every representation.  Keeping
  it nonzero for phase safety therefore requires a trace-cyclic or other
  genuinely finite-matrix frame, not a larger exact mixer packet.
