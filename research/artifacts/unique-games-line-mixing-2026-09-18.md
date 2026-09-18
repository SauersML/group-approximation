# Mixing the one-half hard instances with a satisfiable identity edge

Lane `e-ugc-pull-inverter`, wave `swarm-0917`, 2026-09-18. Hole worked:
`unique-games-gap-admits-polynomial-time-algorithm`. Claim argued here:
`unique-games-np-hard-above-the-two-c-minus-one-line`.

**Status of this artifact.** This is the full mixing argument, written as a
complete proof. It is recorded as an *attempt*, not as a compiled route: the
wave's three-lens referee stage returned no votes for it (see the Attempts entry
on the claim), so it did not clear the wave's bar for ESTABLISHED. Nothing here
is known to be wrong; it awaits an adversarial read. Promote it to a
`kind: route` node with `target: unique-games-np-hard-above-the-two-c-minus-one-line`
and `requires: [unique-games-hard-at-completeness-one-half]` once it has been
refereed.

**Import.** `unique-games-hard-at-completeness-one-half`: for every `eps > 0`
there is `l = l(eps)` such that `Gap-UG[F_2^l]((1-eps)/2, eps)` is NP-hard, with
linear constraints `T x_i + T' x_j = b`, `T, T'` invertible. (Khot--Minzer--Safra,
ECCC TR18-006, Appendix B, p. 55.)

**Mixing map.** Fix a rational `lambda in (0, 1]`. Given such an instance `U`
with edge weights summing to `1`, let `W = M_lambda(U)` be the disjoint union of
`U`, with every weight multiplied by `lambda`, and a new two-vertex game `T` with
one edge `x_p + x_q = 0` (so `T = T' = I`, `b = 0`) of weight `1 - lambda`. `W`
is a linear unique game over the same alphabet `F_2^l`, computable in polynomial
time.

**Values.** The vertex sets are disjoint, so a labeling of `W` is a pair of
independent labelings and

```text
val(W) = lambda val(U) + (1 - lambda),
```

because `T` is satisfied by `x_p = x_q`.

* YES: `val(U) >= (1-eps)/2` gives `val(W) >= 1 - lambda(1+eps)/2`.
* NO: `val(U) <= eps` gives `val(W) <= 1 - lambda(1-eps)`.

**(A) The hardness segment.** Given rational `c in [1/2, 1)` and
`eps in (0, (1-c)/2)` (so that the completeness bound exceeds the soundness
bound), put `lambda = 2(1-c)`, which lies in `(0, 1]`. Then
`1 - lambda(1+eps)/2 = c - lambda eps/2 >= c - eps` and
`1 - lambda(1-eps) = 2c - 1 + lambda eps <= 2c - 1 + eps`, both because
`lambda <= 1`. So `M_lambda` reduces `Gap-UG[F_2^l]((1-eps)/2, eps)` to
`Gap-UG[F_2^l](c - eps, 2c - 1 + eps)`, and NP-hardness transfers. The gap is
non-degenerate exactly when `c - eps > 2c - 1 + eps`, i.e. `eps < (1-c)/2`.

**(B) The linear-loss kill.** Fix `C < 2`. Choose a rational `eps_C in (0,1)`
with `C < 2(1 - eps_C)/(1 + eps_C)` — possible because the right side tends to
`2` as `eps_C -> 0` — and let `k(C) = 2^(l(eps_C))`. Let `A` and rational
`x in (0, 1/2]` be as in the claim. Put `lambda = 2x/(1+eps_C)`, rational and in
`(0, 1]`. For an instance `U` of the imported gap problem at `eps_C`:

* YES: `val(W) >= 1 - lambda(1+eps_C)/2 = 1 - x`, so `A(W)` has value `>= 1 - C x`.
* NO: every labeling of `W` has value
  `<= 1 - lambda(1-eps_C) = 1 - 2x(1-eps_C)/(1+eps_C) < 1 - C x`.

Compute `W`, run `A`, and evaluate the returned labeling exactly (rational
weights, polynomial time). Accept iff its value is `>= 1 - C x`. This decides the
NP-hard imported problem in polynomial time, so `P = NP`. Note that the alphabet
`k(C)` is fixed by `C` alone, so the kill needs no alphabet growth.

For the relaxation form: `Rel(W) >= val(W) >= 1 - x` on YES, so the rounding
guarantee gives a labeling of value `>= 1 - Cx`, and the same test decides.

**The invariant.** Branch multiplicity `2`: an honest labeling of the proved
2-to-2 constraints satisfies exactly one of the two unique branches, so the split
halves the value. Mixing carries the halved point `(1/2, 0)` along the segment to
`(1, 1)`, where the completeness error is `x` and the soundness error is `2x`. A
rounding with loss constant `C < 2` separates the two errors, so it dies at the
decision step of (B).
