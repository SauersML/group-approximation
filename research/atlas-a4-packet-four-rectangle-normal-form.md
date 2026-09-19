---
rg: 2
id: atlas-a4-packet-four-rectangle-normal-form
kind: claim
title: Any unitary edge-message model of the A4 packet has a four-rectangle gauge normal form
---

Use the twelve distinct pair constraints of the shortest A4 packet, with the
simple pair graph identified in `atlas-a4-packet-biclique-decomposition`.
Assign an arbitrary unitary matrix `M_e in U(d)` to each distinct edge.

There are vertex gauges on the two connected components for which every edge
message is exactly factorized except for four canonical edges, and the total
squared factorization error is exactly the sum of four rectangle-holonomy
defects:

```text
Err_packet
 = ||H_1-1||_2^2
   +||H_2-1||_2^2+||H_3-1||_2^2+||H_4-1||_2^2.        (A4-4RECT)
```

Here `H_1` is the unique fundamental rectangle holonomy of the `K_(2,2)`
component and `H_2,H_3,H_4` are a fundamental set of three rectangles for the
`K_(2,4)` component.

Thus **any** compiler which succeeds in representing the local A4
qutrit/multiplicity coherence by one unitary message per distinct pair has
only four genuinely noncommutative packet-cycle variables after gauge.  The
thirty context occurrences and the external matrix dimension do not enlarge
that cycle space.
