---
rg: 2
id: literal-prefix-three-root-swap-retains-typed-carriers
kind: claim
title: The literal prefix three-root swap authenticates only typed corners, not their common active carrier
distinct_from:
  whitehead-swap-copy-completion-retains-rectangular-escape: that treats diagonal Whitehead amplification and its branch-swap completion; this audits the genuinely off-diagonal three-elementary prefix word.
  mixed-steinberg-loops-admit-morita-rectangular-model: that gives the general typed-category countermodel for commutator triangles; this identifies the exact missing relation for the new coarse-to-fine partial-swap word and its Pauli carrier packets.
  one-coarse-to-fine-prefix-isometry-closes-the-reservoir: that constructs the exact infinite bridge and proves its finite rank gap conditional on a common carrier; this proves the existing word relations do not supply that condition.
  controlled-pauli-corner-has-clifford-groupification: that groupifies the conjugation action of the fine-atom controlled-Z but leaves an arbitrary multiplicity involution; this needs the literal fine-atom reflection in a support row, where that twist does not cancel.
---

**ESTABLISHED AUDIT.**  The Leavitt coefficient identities for

```text
x=s_(00)t_0,              y=s_0t_(00),
yx=e,                     xy=f                             (LTS1)
```

and the three-root factorization

```text
J_x=E_12(x)E_21(y)E_12(x)                              (LTS2)
```

do authenticate a partial swap between the source object of `e` and the
target object of `f`.  They do **not** identify the two object identities
with the same finite projection `P` on which the coarse `M_2` and fine
`M_4` packets are being compared.

The exact finite typed countermodel is immediate.  Take one nonzero finite
space `K`; use separate copies `E=K`, `F=K`, let `x:E->F` be unitary and
`y=x^*`, and evaluate `(LTS2)` on `F direct_sum E`.  Then `(LTS1)--(LTS2)`
and `J_x^2=1` hold exactly.  Complete `E` to one leaf of a two-leaf source
object `P_src=K direct_sum K`, and complete `F` to one leaf of a four-leaf
target object `P_tgt=K^(direct sum 4)`.  All local matrix-unit and rectangular
Morita identities hold, but

```text
1_(P_src) != 1_(P_tgt).                                 (LTS3)
```

This is precisely the typed escape: the swapped minimal corners have equal
rank because their ambient packet identities have not been identified.
Stabilized block permutations and further Steinberg associativity triangles
preserve this model.

The support-leakage lemma shows what would defeat it.  One needs carrier
reflections

```text
R_e=1-2e,                  R_f=1-2f                    (LTS4)
```

on a **common** marked projection and one relation
`R_f J_x R_e J_x^*=1`.  Then
`unitary-offdiagonal-block-gram-is-support-leakage` and the `2`-versus-`4`
rank floor force that marked projection to vanish.

The current Pauli/Leavitt packet does not contain the second word in
`(LTS4)`.  The coarse corner `e` is a one-bit Pauli atom, but the fine corner
`f` is a joint atom of two commuting Pauli bits.  Its reflection

```text
1-2f = 1-2 [(1+Z_1)/2][(1+Z_2)/2]                     (LTS5)
```

is a two-qubit controlled-Z phase: a nonlinear Boolean conjunction, not a
word forced by the abelian Pauli/parity relations.  This is the same finite
truth-table boundary as the controlled-swap compiler, now localized to one
fine prefix atom.

`controlled-pauli-corner-has-clifford-groupification` is the optimal existing
finite-packet repair, but it groupifies only the covariance of `(LTS5)`.  In
an arbitrary marked representation its stable letter has the form

```text
(1-2f) tensor V,                                       (LTS6)
```

where `V` is an uncontrolled multiplicity involution.  Covariance arguments
cancel `V`; the support row `R_f J_x R_e J_x^*` does not.  The twist can
therefore absorb the coarse/fine multiplicity mismatch, so the Clifford
extension does not authenticate the literal carrier reflection required by
the Gram-leakage lemma.

Therefore the literal three-root word supplies the correct **actuator** but
not its common-carrier control.  The exact remaining construction is either

1. wordize the fine-atom reflection `(LTS5)` on the marked packet while
   preserving infinite Leavitt completeness; or
2. prove the support row `(1-f)J_xe=o(1)` by a genuinely finite-matrix
   selection theorem without naming `(LTS5)` as a universal word.

Adding more typed Morita/Steinberg relations cannot close this gap.
