---
rg: 2
id: returned-a2-native-arm-orbit-authenticates-same-v-pauli-rows
kind: route
title: Use an uncancelled native arm on every returned A2 occurrence to authenticate the same Pauli word
target: separate-native-quarter-carrier-recovery
requires:
  - native-opposite-arm-return-has-finite-s6-model
  - returned-opposite-cross-zero-has-finite-s6-model
  - relative-gauge-invariance-transfers-cross-orthogonality
---

**INVALIDATED MIXED-OCCURRENCE ROUTE.**  Strengthen the returned `A_2`
window by attaching the native fold--opposite-arm cell at one returned
parent-mark occurrence and all of its translates under the literal
order-three word `V`.  Thus every returned mark occurrence is now the final
output of a genuine cell containing uncancelled `s_0` and `t_0` roots, its
partial Whitehead, braid, root swaps, and fixed root-position transports.

The hoped inference was that this first excursion outside the Boolean
coefficient inventory removes the cyclic packet-copy gauge and gives, on the
common positive Pauli cut,

```text
[V,X]=o(1),                    [V,Z]=o(1).             (NAR1)
```

Together with `relative-gauge-invariance-transfers-cross-orthogonality`,
these two rows would transfer returned target orthogonality to the source
and close `separate-native-quarter-carrier-recovery`.

`returned-a2-native-arm-orbit-leaves-same-cut-pauli-free` refutes the
inference.  A finite quotient of a finite-group amalgam retains the entire
returned model injectively, hence retains squared corner-normalized defect
`2` for both commutators, while the second factor supplies the literal
uncancelled native arm cell at the source mark.  Conjugating that factor by
`V` supplies the same cell at the other two returned occurrences.

Therefore merely putting a non-Boolean native cell on every occurrence of
the returned orbit is not occurrence authentication.  A live row must
identify one of the native arm/payload words with the source Pauli word
itself, or charge the mismatch by a finite-coordinate boundary estimate.

