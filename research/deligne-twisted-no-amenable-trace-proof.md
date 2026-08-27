---
rg: 2
id: deligne-twisted-no-amenable-trace-proof
kind: route
title: Pass C-star property T to the central fibre and apply Brown's amenable-trace theorem
target: deligne-twisted-fibres-have-no-amenable-trace
requires:
  - property-t-cstar-amenable-trace-forces-fd-quotient
  - deligne-triple-cover-fd-central-invisibility
---

Property (T) passes from `Sp_4(Z)` to its finite central extension `E_3`, from
`E_3` to `C^*(E_3)`, and from that algebra to each central-character quotient.
Brown's theorem then turns an amenable trace on a nontrivial quotient into a
nonzero finite-dimensional quotient.  Pulling its representation back to
`E_3` sends `z` to the prescribed nontrivial scalar, contradicting Deligne
finite-dimensional invisibility.
