---
rg: 2
id: nonhyperlinear-from-atomic-lamp-collapse
kind: route
title: Collapse the atomic character mass of a Tarski lamplighter against its Kesten gap
target: non-hyperlinear-group
requires:
  - defect-controlled-lamp-character-transport
  - infinite-schreier-pvm-transport-kills-finite-mark
  - kesten-amenable-stabilizer-uniform-gap
  - lamp-character-transport-bounds-schreier-dirichlet
  - tarski-lamp-nonconstant-sector-has-amenable-stabilizers
---

The witness is `Gamma = C_2 wr A` for an actor `A` that is nonamenable with
every proper subgroup amenable, marked by `w = m_e m_a`.

Let `U : T -> U(d)` be any map with `Def(U) <= delta_0`, and decode `rho` by
`defect-controlled-lamp-character-transport`.  The decoded resolution is exact
and has at most `d` atoms, so by clause `(5)` of
`tarski-lamp-nonconstant-sector-has-amenable-stabilizers` and `(DLT1)` its
negative sector for `w` carries mass at least
`(1/4) || U_w - 1 ||_2^2 - C' Def(U)`, and by clauses `(1)`--`(3)` that sector
lies inside the invariant set `Omega`, all of whose stabilizers are amenable.

`kesten-amenable-stabilizer-uniform-gap` supplies the bottom gap
`gamma = 1 - rho(A,S)` required by `(ISP1)`.  The dictionary `(CTL3)` turns
`(DLT2)` into the covariance bound
`E_PVM = (2/D) sum_s L_s <= (2/D) sum_s C_s Def(U)`.  Feeding both into
`(ISP3)`,

```text
(1/4) || U_w - 1 ||_2^2 - C' Def(U)  <=  (1/(D gamma)) sum over s in S of C_s Def(U),
```

so with `Lambda = C' + (1/(D gamma)) sum_s C_s`,

```text
Def(U) >= || U_w - 1 ||_2^2 / (4 Lambda)                            (ALC1)
```

for every finite-dimensional `U` of defect below `delta_0`.  A hyperlinear
`Gamma` supplies `U` with `Def(U) -> 0` and `|| U_w - 1 ||_2^2 -> 2`, because
`tau(w) = 0` for the canonical trace, contradicting `(ALC1)`.  So `Gamma` is
not hyperlinear.

**Price of admission, recorded so no reader mistakes this route for a short
one.**  By `sofic-actor-refutes-lamp-character-transport` the prerequisite is
false for every sofic `A`, so working this route means proving a non-soficity
statement about the chosen Tarski monster.  Every other ingredient is
established and elementary.  Property (T) has been removed from the amplifier
only -- the Kesten constant replaces the Kazhdan constant there -- and the
rounding step (T) used to supply is exactly the open prerequisite.
