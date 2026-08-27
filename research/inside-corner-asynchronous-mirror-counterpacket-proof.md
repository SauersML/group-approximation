---
rg: 2
id: inside-corner-asynchronous-mirror-counterpacket-proof
kind: route
title: Swap the missing source block with an equal-rank complement and compress away the mirror
target: inside-corner-hecke-tests-miss-the-asynchronous-mirror-exit
requires:
  - toeplitz-range-commutator-has-a-balanced-mirror-exit
---

Decompose the ambient space as

```text
FH direct-sum HH direct-sum CH direct-sum R.           (ICP1)
```

Let `T` be the identity on `FH`, the transposition between `HH` and `CH`,
and any unitary on `R`.  Since `E=F+H`, conjugation gives `Q=F+C`.  Moreover

```text
FTE=F T(F+H)=F,
```

because `T` fixes `F` and sends `H` orthogonally into `C`.  This proves
`(ICH3)`.

Every `a in A` is supported in `E`, while `C<=1-E`.  Hence `aC=Ca=0` and

```text
aQb=a(F+C)b=aFb,
```

proving `(ICH4)`.  Repeatedly replace every sandwiched occurrence of `Q` by
`F` to obtain equality of all listed trace polynomials and HS tests.

In infinite dimension, arrange that `E`, `F`, and both ambient complements
are countably infinite.  A unitary from `E` onto `F`, completed arbitrarily
between the complements, gives the exact proper return and source-full
compression.

Finally, if `(1-E)Q=0` is imposed functorially, then `Q<=E`.  In any finite
tracial representation `Q=TET^*` gives `tau(Q)=tau(E)`, so faithfulness and
`Q<=E` force `Q=E`; since the intended inside range is `F=E-H`, this forces
`H=0`.  Thus only a nonfunctorial finite-coordinate mirror payment can close
the cell.
