---
rg: 2
id: stw93-singular-kernel-witness-proof
kind: route
title: Distinct quasitraces must differ on the kernel of the unique-quasitrace quotient
target: stw93-singular-trace-kernel-witness-for-any-negative-answer
requires:
  - stw93-super-mcduff-tracial-central-quotient
---

If `q` vanished on `I=J_τ∩D`, it would descend to the quotient.  Uniqueness
there would force `q=τ_ω`, contrary to hypothesis.  Hence `q` is nonzero on
`I_+`; rescaling a positive element gives a contraction `h` with `q(h)>0`.
By definition of the trace-kernel ideal, `τ_ω(h)=0`.  Any inequality
`q(x)≤Cτ_ω(x)` on positive elements fails at `h`.
