---
rg: 2
id: order-two-universal-reduction-proof
kind: route
title: Pair a mark-retaining map with the symbol map into a product of two MF groups
target: order-two-defect-question-reduces-to-one-universal-ring
requires:
  - order-two-universal-ring-has-finitary-symbol-sequence
  - laurent-elementary-groups-are-residually-finite
artifacts:
  - research/artifacts/fullness-corner-and-order-two-reduction-2026-09-08.md
---

## Proof

**1 implies 2.**  `A_2` is countable unital with `TS = 1` and defect of
additive order two, by `(OT2)`, so it is one of the rings in statement 1.

**3 implies 2.**  `w != 1` because `Q != 0` in `A_2`, again by `(OT2)`.  A
homomorphism killing a nonidentity element is not injective.

**2 implies 3.**  Suppose `phi : EL_n(A_2) -> H` has `H` MF and
`phi(w) != 1`.  By `(OT4)`, `w` lies in the kernel `L_n` of the symbol
map, since `Q` has zero symbol; and `L_n` is simple.  Hence
`ker(phi) cap L_n` is a proper normal subgroup of `L_n`, so trivial, and
`phi` restricted to `L_n` is injective.

Consider

```text
g |--> (phi(g), sigma(g))  :  EL_n(A_2) --> H x EL_n(D).
```

If `g` is in its kernel then `sigma(g) = 1`, so `g in L_n` by `(OT4)`,
and then `phi(g) = 1` forces `g = 1`.  So the map is injective.

`EL_n(D)` is residually finite by the second prerequisite, hence MF.  A
product of two MF groups is MF: take approximate matrix models for each
factor and form block-diagonal sums coordinatewise; multiplicative errors
add and still tend to zero, and the norm of a block-diagonal matrix is
the maximum of the two block norms, so every nonidentity pair stays
separated.  Therefore `H x EL_n(D)` is MF, and MF passes to subgroups, so
`EL_n(A_2)` is MF — contradicting statement 2.

**3 implies 1.**  Let `R, s, t` be as in statement 1.  The relations
`ts = 1` and `2(1-st) = 0` are exactly the defining relations of `A_2`,
so there is a unital ring map `A_2 -> R` with `S |-> s`, `T |-> t`, hence
a group homomorphism `psi : EL_n(A_2) -> EL_n(R)` with
`psi(w) = e_12(1-st)`.  Given `rho : EL_n(R) -> H` with `H` MF, the
composite `rho . psi` is an MF-target homomorphism out of `EL_n(A_2)`, so
statement 3 gives `rho(e_12(1-st)) = 1`.  That element is nonidentity
because `1 - st` has additive order two and in particular is nonzero.  So
no `rho` is injective and `EL_n(R)` is non-MF, which is statement 1 and
also the final marked assertion.

## No cycle is recorded

The three statements are equivalent, but only the forward payoff is
wired as a route elsewhere (`order-two-low-rank-from-universal-ring`).
The reverse implication is the trivial specialization proved above as
"1 implies 2", and recording it as a second route would create a
dependency cycle warning without adding content.
