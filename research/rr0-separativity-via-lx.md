---
rg: 2
id: rr0-separativity-via-lx
kind: route
title: Weak cancellation of all real rank zero algebras gives their separativity
target: rr0-c-star-algebras-are-separative
requires: [stw99-problem-lx-rr0-weak-cancellation, agor-separative-rr0-algebras-are-k1-bijective]
---

Only part (1) of the root is used.  With `stw99-lx-via-rr0-separativity`
this makes `rr0-c-star-algebras-are-separative` equivalent to the root.

Let `A` have real rank zero and let `A~` be its unitization if `A` is not
unital (`A~ = A` otherwise).  Real rank zero passes to matrix algebras
(Brown--Pedersen, *C\*-algebras of real rank zero*, J. Funct. Anal. 99 (1991);
theorem number not re-verified here), so every `M_n(A~)` has real rank zero and
therefore weak cancellation by part (1) of the root.  By part 2 of
`agor-separative-rr0-algebras-are-k1-bijective`, `A~` is separative.

Now let `p, q` be projections in `M_k(A)` with
`p direct_sum p ~ p direct_sum q ~ q direct_sum q` in `M_inf(A)`.  The same
equivalences hold in `M_inf(A~)`, so `p ~ q` there, by a partial isometry `v`
in some `M_m(A~)` with `v*v = p` and `vv* = q`.  Since `v = v p` and `p` has
entries in the ideal `A` of `A~`, `v` lies in `M_m(A)`.  So `p ~ q` over `A`,
and `A` is separative.
