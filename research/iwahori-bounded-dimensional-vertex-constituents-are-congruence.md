---
rg: 2
id: iwahori-bounded-dimensional-vertex-constituents-are-congruence
kind: claim
title: Bounded-dimensional irreducible constituents of an almost compatible Iwahori vertex are asymptotically congruence
distinct_from:
  bounded-dimension-iwahori-pairs-have-holder-capture: that bounds the total matrix size of the pair; this allows arbitrary total dimension and constrains only the irreducible constituents of one vertex, whose multiplicities may be unbounded and which need not be constituents of the other vertex.
  capture-gap-localizes-to-regular-character-face: that moves a capture gap to a regular-character corner of the pair, through an open regular-branch prerequisite; this is an unconditional statement about the constituent decomposition of one exact vertex, proved from Choquet uniqueness on the character simplex of SL2(Z).
  bs14-character-split-leaves-only-the-regular-microstate-face: that cuts the ultraproduct character of SL2(Z[1/2]) into finite and regular faces; this restricts the cut to the vertex SL2(Z) and reads off which finite-dimensional extremal characters of the vertex can carry mass.
  iwahori-one-vertex-congruence-capture: that asks the whole vertex to be near congruence; this proves it for the part carried by constituents of bounded dimension.
---

**ESTABLISHED (unreviewed).** Notation as in
`iwahori-congruence-capture-transfers-across-one-edge`. Put `C = SL_2(Z)`
with its fixed generating set `S_C`. For an exact unitary representation `rho`
of `C` on `C^k`, put

```text
dist_cong(rho) = inf { max_(s in S_C) ||rho(s) - tau(s)||_op :
                       tau : C -> U(k) factors through some SL_2(Z/N) }.
```

For an exact representation `alpha` of `C` on `C^d`, integers `D >= 1` and
`eta > 0`, let `m(alpha; D, eta)` be the normalized dimension `dim Q / d` of the
sum `Q` of those irreducible constituents `rho` of `alpha` with `dim rho <= D`
and `dist_cong(rho) >= eta`. This depends only on the isomorphism classes and
multiplicities of the constituents.

**Theorem.** Let `pi_n = (pi_(n,+), pi_(n,-))` be exact pairs with
`def(pi_n) -> 0`. Then for every `D >= 1` and `eta > 0`,

```text
m(pi_(n,+); D, eta) -> 0   and   m(pi_(n,-); D, eta) -> 0.        (BDC1)
```

**Diagonal form.** There are `D_n -> infinity` with
`m(pi_(n,+); D_n, 1/D_n) <= 1/D_n`. Thus the constituents of `pi_(n,+)` of
dimension at most `D_n` are, apart from normalized mass `1/D_n`, each within
operator distance `1/D_n` on generators of a congruence representation of its
own dimension. **Every positive congruence-capture gap of an almost compatible
vertex is carried by irreducible constituents whose dimensions tend to
infinity.**

**What it kills.** Each of the following is excluded as a countersequence to
`iwahori-one-vertex-congruence-capture`, however large the total dimension and
multiplicities:
* amplified or mixed copies of a fixed finite family of small non-congruence
  representations, for example a triangle-group representation into `SO(3)`
  pulled back to `C`, or a representation with dense image in `SU(2)`;
* non-congruence finite quotients seen only through irreducibles of bounded
  degree;
* continuous families of bounded-dimensional infinite-image representations.

The invariant is the mass that the Choquet boundary measure of the vertex's
limit character gives to finite-dimensional non-congruence extremal
characters. In every such construction it is positive. It is zero for every
almost compatible sequence, because by Peterson--Thom the limit character is
restricted from `SL_2(Z[1/2])`, and restrictions of its extremal characters
charge only congruence irreducibles and the two type-II_1 characters of `C`
supported on `{±1}`. This is the step where every member of the class dies.

**What it does not kill.** Constituents of dimension tending to infinity are
invisible to the argument, as they must be. A limit of normalized characters
of irreducibles of growing dimension can be the regular character. This is
exactly the Peterson--Thom blind spot recorded in
`iwahori-local-global-defect-question`.

Proof in `iwahori-bounded-dimensional-vertex-constituents-proof`.
