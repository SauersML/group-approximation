---
rg: 2
id: tarski-lamp-nonconstant-sector-proof
kind: route
title: Right translations commute with the actor and only constants are fixed
target: tarski-lamp-nonconstant-sector-has-amenable-stabilizers
requires: []
---

**Complete direct proof.**

`(1)`  Right and left translation commute:
`(s.(R_a chi))(x) = chi(s^(-1) x a) = (R_a (s.chi))(x)`.  Hence
`R_a chi =/= chi` if and only if `R_a (s.chi) =/= s.chi`, so `Omega` is
invariant under the dual action.

`(2)`  `chi(w) = chi(e) chi(a) = chi(e) (R_a chi)(e)`, so `chi(w) = -1` forces
`(R_a chi)(e) =/= chi(e)`, that is `chi in Omega`.

`(3)`  If `Stab_A(chi) = A` then `chi(s^(-1) x) = chi(x)` for all `s, x`, so
`chi` is constant; a constant character satisfies `R_a chi = chi` and is
therefore not in `Omega`.  So `chi in Omega` has proper stabilizer, and every
proper subgroup of `A` is amenable by hypothesis.

`(4)`  `a =/= e` gives `w =/= 1` in `Gamma`, so `tau(w) = 0` for the canonical
trace, and `w^2 = 1` because `M` is elementary abelian.  Thus `(1-w)/2` is the
projection onto the `(-1)`-sector and `tau((1-w)/2) = 1/2`.  Under the Fourier
identification `L(M) = l^infinity(M^)` that sector is `{chi : chi(w) = -1}`.

`(5)`  For a self-adjoint unitary `U_w` with `(-1)`-sector mass `p`,
`tau(U_w) = 1 - 2p` and

```text
|| U_w - 1 ||_2^2 = 2 - 2 tau(U_w) = 4p.
```

Existence of an `A` as hypothesised is Ol'shanskii's construction of Tarski
monster groups (A. Yu. Ol'shanskii, *An infinite group with subgroups of prime
orders*, Izv. Akad. Nauk SSSR 44 (1980) 309--321), which are nonamenable and
have all proper nontrivial subgroups of order `p`.
