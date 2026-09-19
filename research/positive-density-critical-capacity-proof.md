---
rg: 2
id: positive-density-critical-capacity-proof
kind: route
title: Put the nested Pauli tower inside the whole active carrier
target: active-core-density-keeps-rectangular-capacity-critical
requires:
  - gowers-hatami-uniqueness-does-not-lock-nested-pauli-reservoirs
---

Use the exact model from `nested-pauli-reservoir-no-go-proof` on

```text
H_N=(C^2)^(tensor N) tensor C^m.
```

At depth `n`, let the label packet act on the first `n` qubits and let the
remaining factor be multiplicity.  Then its label degree is `2^n`, its
multiplicity is `2^(N-n)m`, and their product is the fixed ambient dimension
`2^N m`.  The two child ranges are the two coordinate halves of the next
label qubit, so they are orthogonal and their total rank equals the whole
next target carrier.  This proves exact criticality and zero cross Gram.

Take the active projection to be the identity.  For a smaller prescribed
rational density, direct-sum the model with a trivial spectator and choose
the block sizes to obtain that density.  Common amplification supplies all
required divisibilities without changing normalized ratios.  This proves
the claim.
