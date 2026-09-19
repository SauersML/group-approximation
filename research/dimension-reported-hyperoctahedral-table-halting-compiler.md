---
rg: 2
id: dimension-reported-hyperoctahedral-table-halting-compiler
kind: claim
title: A halting output activates one low-dimensional hyperoctahedral predicate packet
distinct_from:
  dimension-reported-clifford-table-halting-compiler: that activates an extraspecial Pauli table and uses exponential spin dimension; this activates a signed-permutation table which also enforces the terminal Boolean predicate.
---

Construct a total machine-to-group compiler with fixed positive HS modulus.
If the source machine halts and prints `D`, choose even `m` satisfying
`(MHB4)`, repeat every allowed terminal assignment evenly, and activate the
complete multiplication table of the resulting `W_m`.  Every marked
`D`-dimensional microstate must decode to the all-pairs map in `(MHB1)`, so
the robust linear dimension floor is impossible.  If the machine does not
halt, retain an exact representation in which the global marked word is
nontrivial.

The finite breaker and arbitrary-predicate packet are established.  The open
content is the same runtime-independent activation problem as in the
Clifford-table compiler: one finite presentation must expose the table chosen
by the halting output with constants independent of `D` and halting time.

## Attempts

- Ordinary Boone/HNN simulation derives the terminal table with
  runtime-dependent area and loses the fixed defect modulus.
- Listing the table in the source presentation works only when `D` is known
  before compilation; the Kleene program prints `D` after the presentation
  has already been computed.
- Recursive verifier compression has the right uniform soundness shape.  The
  remaining backend is a perfect-complete group-word activation of one finite
  signed-permutation table.
