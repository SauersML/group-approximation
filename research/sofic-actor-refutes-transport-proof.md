---
rg: 2
id: sofic-actor-refutes-transport-proof
kind: route
title: Make the lamplighter sofic and read the atomic mass off its own microstates
target: sofic-actor-refutes-lamp-character-transport
requires:
  - gkp-sofic-action-toolkit
  - gkp-wreath-permanence-theorem
  - infinite-schreier-pvm-transport-kills-finite-mark
  - kesten-amenable-stabilizer-uniform-gap
  - lamp-character-transport-bounds-schreier-dirichlet
  - tarski-lamp-nonconstant-sector-has-amenable-stabilizers
---

Suppose `A` is sofic.  The regular action of `A` on itself is sofic, by GKP
Theorem 2.14 with the trivial (locally finite) subgroup, imported in
`gkp-sofic-action-toolkit`.  `C_2` is finite, hence sofic.  So by GKP Theorem
3.6, imported in `gkp-wreath-permanence-theorem`,

```text
Gamma = C_2 wr_(regular) A
```

is sofic, hence hyperlinear: a sofic approximation lands in permutation
matrices, which are unitary, and its Hamming estimates are the normalized-HS
estimates.  So for every `delta > 0` there is a `U : T -> U(d)` with
`Def(U) <= delta` and, because `w =/= 1` and soficity separates nonidentity
elements, `|| U_w - 1 ||_2^2 >= 2 - o(1)`.

Assume `(DLT1)` and `(DLT2)` hold with dimension-free constants and decode
`rho`.  Its joint resolution has at most `d` nonzero atoms.  By clause `(5)` of
`tarski-lamp-nonconstant-sector-has-amenable-stabilizers` applied to the
selfadjoint unitary `rho(w)`, together with `(DLT1)`, the mass of
`{chi : chi(w) = -1}` is at least

```text
(1/4) || U_w - 1 ||_2^2 - C' Def(U)  >=  1/2 - o(1) - C' delta,
```

and by clauses `(1)`--`(3)` that set sits inside the invariant set `Omega`,
whose orbits all have amenable stabilizers.  So `mu >= 1/2 - o(1) - C' delta`
in the notation of `(ISP2)`.

`kesten-amenable-stabilizer-uniform-gap` gives the bottom gap
`gamma = 1 - rho(A,S) > 0` of `(ISP1)` on every orbit of `Omega`, hence on
`Omega`.  By the dictionary `(CTL3)`,

```text
E_PVM = (1/D) sum over s in S of sum over chi of
        || U_s P_chi U_s^* - P_(s chi) ||_2^2 = (2/D) sum_s L_s,
```

so `(DLT2)` gives `E_PVM <= (2/D) sum_s C_s delta`.  Now `(ISP3)` of
`infinite-schreier-pvm-transport-kills-finite-mark` reads

```text
1/2 - o(1) - C' delta  <=  mu  <=  E_PVM / (2 gamma)
                       <=  (1/(D gamma)) sum over s in S of C_s delta.
```

Letting `delta` tend to `0` gives `1/2 <= 0`.  Hence no such constants exist.
