---
rg: 2
id: relative-c2-square-pauli-counterpacket-proof
kind: route
title: Rotate one regular involution through an anticommuting Pauli direction
target: relative-finite-group-gh-cannot-fix-two-generating-subgroups
requires:
  - gowers-hatami-finite-group-hs-stability
---

The Pauli tensors `B=I tensor Z` and `C=X tensor Y` anticommute and square to
the identity.  Hence `(RFG1)` gives `B_t^*=B_t` and `B_t^2=I`.  Both `A` and
`B_t` have two positive and two negative eigenvalues, proving the two
regular-restriction statements.

Every Pauli tensor other than `I tensor I` has trace zero.  Since

```text
AB_t=cos(2t)(Z tensor Z)+sin(2t)(ZX tensor Y),
```

all three nonidentity values in `(RFG2)` have trace zero, proving `(RFG3)`.
In the sixteen products of the four normal forms, every nonexact product is
made exact by commuting `A` past `B_t` exactly once.  Because `A` commutes
with `B` and anticommutes with `C`,

```text
[A,B_t]=2sin(2t)AC.
```

The normalized Hilbert--Schmidt norm of the unitary `AC` is one.  This proves
`(RFG4)` and `(RFG5)`; equivalently

```text
||AB_tAB_t-I||_2=||[A,B_t]||_2=2sin(2t).
```

Any subspace invariant under the two unitaries is reducing for both, hence
reducing for their commutator.  The restriction of the invertible operator
in `(RFG5)` cannot vanish on a nonzero such subspace.  Tensoring by `I_m`
preserves invertibility and every normalized norm, proving the flexible
quarantine assertion.

Finally, anticommutation gives

```text
B_t B B_t=cos(4t)B+sin(4t)C.
```

Therefore

```text
E_(B_t)(B)=cos^2(2t)B+sin(2t)cos(2t)C.
```

Conjugation by `A` fixes `B` and negates `C`; applying `E_A` proves `(RFG7)`.
Since `delta_t=2sin(2t)`, its second form follows exactly.
