---
rg: 2
id: four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap
kind: claim
title: Four Pauli words give an explicit amplification-blind gap against rectangular escape
---

**ESTABLISHED.**

Four approximate two-qubit Pauli words have standard-polynomial norm at
least `8-144 epsilon`, while four words within `delta` of one `M_2` factor
have norm at most `96 delta`.  Hence `144 epsilon+96 delta>=8`, and a common
error is at least `1/30`.

The gap is unchanged by spectator amplification.  What remains is the
matrix-only theorem putting the same returned tuple in the source factor and
the target Pauli table on one carrier.
