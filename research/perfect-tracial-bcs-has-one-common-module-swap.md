---
rg: 2
id: perfect-tracial-bcs-has-one-common-module-swap
kind: claim
title: A perfect tracial BCS model has one common left-right module swap
distinct_from:
  private-gauges-close-fanizza-triangle: that constructs context-private packet gauges and closes one incidence triangle after countable amplification; this gives a single standard-form intertwiner for every observable at once before finite packet localization.
  one-gram-vector-decodes-a-finite-bcs-strategy: that starts with a finite matrix Gram operator and decodes a tensor strategy; this starts with an exact tracial strategy and proves the common full-module swap required for exact compiler completeness.
  common-partial-isometry-swap-game-compiler: that asks for finite ordinary syntax and positive-density matrix soundness; this proves only its exact semantic common-swap clause.
---

Let `(M,tau)` be a finite tracial von Neumann algebra carrying an exact BCS
representation.  Write

```text
H=L^2(M,tau),
L_a(x)=ax,
R_a(x)=xa.                                             (PCS1)
```

Let `bar(H)` be the conjugate Hilbert space.  There is one linear unitary

```text
S:bar(H)->H                                             (PCS2)
```

which simultaneously intertwines the conjugate right action and the left
action of every self-adjoint BCS observable:

```text
L_a S=S overline(R_a)             (a=a^* in M).        (PCS3)
```

### Proof

Let `C:H->bar(H)` be the canonical antiunitary `xi -> bar(xi)`, and let

```text
J_tau(hat(x))=hat(x^*)                                  (PCS4)
```

be the tracial modular conjugation.  Both maps are antiunitary, so

```text
S=J_tau C^(-1)                                         (PCS5)
```

is a linear unitary.  Standard-form left-right duality gives

```text
J_tau R_a J_tau=L_(a^*).                               (PCS6)
```

For self-adjoint `a`, conjugating `(PCS6)` through `C` is exactly `(PCS3)`.
The same `S` works for all contexts and all shared variables.  ∎

## Exact swap relators

On `H direct_sum bar(H)`, put

```text
J_S=[[0,S],[S^*,0]],
D_a=diag(L_a,overline(R_a)).                           (PCS7)
```

Then `J_S` and every `D_a` are self-adjoint unitaries and `(PCS3)` says

```text
[D_a,J_S]=I.                                          (PCS8)
```

If `F_c` is the forbidden projection of an exact BCS context, then
`F_c=0`, so the predicate specialization

```text
[diag(I-2L_(F_c),I),J_S]=I                            (PCS9)
```

also holds.  Thus all commutator rows in
`partial-isometry-swap-wordizes-one-bcs-gram-row` have one simultaneous
exact extension in the perfect tracial model.

This is stronger than merely fixing the tracial vector: the full conjugate
right standard module is unitarily equivalent to the left standard module.
Accordingly, the common-swap compiler does not face an exact-completeness or
intertwiner-torsor obstruction at the BCS level.

## What this does not solve

The finite local predicate packets do not present the operators `L_a` and
`overline(R_a)` as two globally conjugate copies for free.  Conjugating a
whole finite packet from a common source makes every observable in the
source commutant land in the target commutant; a nonlinear context
observable generally is not in that commutant.  Conversely, putting all
context truth tables in one common finite source type forces cross-context
commutation or a global classical support condition.

Therefore `(PCS2)--(PCS9)` settle the semantic firewall but not the finite
ordinary-word localization.  The remaining question in
`common-partial-isometry-swap-game-compiler` is precisely how to expose
this one standard-form swap on selected context carriers without turning
the separate context algebras into one finite classical packet.

## Attempts

- **Use a separate modular swap for every context.**  Semantically legal,
  but finite soundness then sees separate Gram states and the game gap does
  not combine them.
- **Conjugate one full finite source packet into every context.**  A logical
  observable in the source multiplicity commutant must land in each target
  packet commutant, whereas the intended nonlinear context involution acts
  on the packet label factor.
- **Put every context truth table in one finite packet.**  The resulting
  label observables commute across contexts; matching shared variables is
  equivalent to a global classical support condition and need not exist.

