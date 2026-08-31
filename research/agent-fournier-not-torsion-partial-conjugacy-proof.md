---
rg: 2
id: agent-fournier-not-torsion-partial-conjugacy-proof
kind: route
title: Reduce the full torsion corner equality to a faithful cyclic character
target: agent-fournier-not-torsion-partial-conjugacy-detector-no-go
requires: []
---

The target claim contains the complete direct proof.  Corner unitarity makes
the compressed group element normalize the full nontrivial cyclic spectral
projection, whose group-ring support recovers the entire subgroup `<z>`.
The proposed compressed conjugacy equality then reduces to

```text
q_z(z^(a(1-r))-1)=0.
```

Evaluating in a faithful nontrivial character of the cyclic group forces
`a(1-r)=0 mod m`, which is exactly the original uncompressed conjugacy
equality.

