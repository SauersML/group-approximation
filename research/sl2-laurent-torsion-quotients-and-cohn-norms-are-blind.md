---
rg: 2
id: sl2-laurent-torsion-quotients-and-cohn-norms-are-blind
kind: claim
title: "Over Z[t,t^-1], E_2 maps onto SL_2 of every quotient of positive characteristic, every degree function is zero, and no discrete norm exists"
distinct_from:
  sl2-laurent-integers-equals-elementary-subgroup: that is the open question SL_2 = E_2 over Z[t,t^-1]; this is a calibration that proves two families of detectors cannot answer it negatively.
  sl2-laurent-integers-is-not-finitely-generated: its Attempts sketch in one sentence that congruence quotients have SL_2 = E_2, citing Vaserstein for the characteristic-zero orders; this gives a complete self-contained proof for every quotient containing a nonzero integer, including non-reduced and zero-divisor quotients, derives the subgroup consequence, and adds the degree-function and discrete-norm obstructions, which are not recorded there.
  elementary-sl2-laurent-integers-is-finitely-generated: that proves E_2(Z[t,t^-1]) is finitely generated; this uses only its first step (diagonal unit matrices are elementary) and concerns the images of E_2 in quotients.
---

**ESTABLISHED.** Let `R = Z[t,t^{-1}]`, `G = SL_2(R)`, and for an ideal `J` let
`SL_2(R,J) = ker(G -> SL_2(R/J))`.

**(C) Positive-characteristic quotients see nothing.** If the ideal `J` contains
a nonzero integer, then `SL_2(R/J) = E_2(R/J)`. Consequently:

1. `E_2(R) -> SL_2(R/J)` is surjective, so `G = E_2(R) · SL_2(R,J)`.
2. Every `A in G` agrees modulo `J` with a product of elementary matrices.
   Equivalently, every unimodular row over `R` can be reduced to `(1,0)` modulo
   `J` by elementary column operations with multipliers in `R`.
3. A subgroup `H <= G` that contains `E_2(R)` and some `SL_2(R,J)` with
   `J ∩ Z != 0` is all of `G`. This applies to every `J` with `R/J` finite. So a
   proper finite-index subgroup of `G` containing `E_2(R)`, if one exists, contains
   no principal congruence subgroup of finite level. Likewise, a homomorphism out
   of `G` that kills `E_2(R)` and factors through some `SL_2(R/J)` with
   `J ∩ Z != 0` is trivial.

**(D) Degree functions are zero.** Let
`d : R \ {0} -> [0, infinity)` satisfy `d(xy) = d(x) + d(y)`, and
`d(x+y) <= max(d(x), d(y))` whenever `x, y, x+y != 0`. Then `d = 0`
identically. So the degree-zero subring `R_0 = {0} ∪ d^{-1}(0)` of any degree
function is all of `R`. Degree-function (Cohn–Nagao) arguments compare `GE_2(R)`
with `GE_2(R_0)` and the triangular group over `R`, so they need `R_0` to be a
proper subring. Over `R` they return the tautology `GE_2(R) = GE_2(R)`.

**(N) No discrete norm.** There is no function `|.| : R \ {0} -> [1, infinity)`
with `|xy| = |x||y|`, `|x+y| <= |x| + |y|`, and `|x| >= 2` for every nonzero
non-unit `x`.

**Where the obvious candidates fail.**
- The top degree satisfies both axioms of (D) but takes the value
  `-1` at `t^{-1}`.
- The width `w = (top degree) - (bottom degree)` is nonnegative and additive but
  not ultrametric: `w(1+t) = 1 > 0 = max(w(1), w(t))`.

**What this kills.** It kills any proof of `SL_2(R) != E_2(R)` (for
[[sl2-laurent-integers-equals-elementary-subgroup]]) that proceeds in one of
these ways:
- **(K1)** reduce modulo an ideal containing an integer, including every finite
  quotient, every mod-`n` census, and every non-reduced thickening. It dies at the
  step "the image of the witness is not elementary modulo `J`", by (C).
- **(K2)** a Cohn-style degree function on `R`. It dies at the step "`R_0` is a
  proper subring", by (D).
- **(K3)** a discrete norm in the sense of (N). It dies at the first step, because
  no such norm exists.

The still-uncovered specialisations are quotients `R/J` with `J ∩ Z = 0`,
`J != 0`. Their reduced torsion-free parts are orders `Z[α, α^{-1}]` in number
fields with infinitely many units unless `α` is a root of unity. The expected
input there is Liehl's extension of Vaserstein's theorem to orders of arithmetic
type (J. Reine Angew. Math. 323 (1981) 153–171, Zbl 0447.20035). Its exact
hypotheses have not been read from the source, so that case is not claimed
here. For every witness the remaining detectors are therefore two-dimensional
(`J = 0`) or characteristic-zero one-dimensional.

DERIVATION
[[sl2-laurent-torsion-quotients-and-cohn-norms-are-blind-proof]]
