---
rg: 2
id: unique-games-np-hard-above-the-two-c-minus-one-line
kind: claim
title: For every rational c in [1/2,1) and eps > 0, Gap-UG[F_2^l](c - eps, 2c - 1 + eps) is NP-hard, so no polynomial-time rounding with alphabet-uniform linear loss 1 - C x, C < 2, exists unless P = NP
distinct_from:
  unique-games-hard-at-completeness-one-half: that is the single point (1/2, eps); this is the whole segment from (1/2, 0) to (1, 1), obtained from it by mixing, and the linear-loss kill it gives near completeness 1.
  unique-games-conjecture: that asks hardness at (1 - eps, eps), strictly below the line s = 2c - 1; this is hardness on or above that line only.
  grassmann-composed-2to2-coarsenings-are-satisfiable: that shows affine-view verifiers over DKKMS inputs cannot go below s = 2c - 1 (a verifier floor); this shows the same line is reached by a reduction and is an algorithmic ceiling for linear-loss rounders.
  spectral-gap-no-outputs-cannot-prove-ugc: that is a rounding with loss 768 eps/gamma on few-eigenvalue instances; this bounds from below the loss constant of any alphabet-uniform rounding on all instances.
  unique-games-gap-admits-polynomial-time-algorithm: that is the open algorithmic refutation, equivalent to some point strictly below the line being easy; this is the claimed hardness above the line.
artifacts:
  - research/artifacts/unique-games-line-mixing-2026-09-18.md
---

**OPEN.** A full proof is written out in
`research/artifacts/unique-games-line-mixing-2026-09-18.md`: a short consequence
of `unique-games-hard-at-completeness-one-half` (Khot--Minzer--Safra) by
disjoint-union mixing with a satisfiable identity edge. It is recorded as an
attempt rather than compiled as a route because the wave's referee stage returned
no votes on it (see ## Attempts). Nothing in it is known to be wrong; it needs an
adversarial read before it becomes a reusable theorem.

The mixing step is elementary and is already noted, in verifier language, in the
Attempts of `unique-games-conjecture` (sw-034: "mixing the split with trivial exact
tests attains s ~ 2c - 1"). What would be new here is the statement as a hardness
segment and the algorithmic class kill (B). Both are stated below as the
proposition this claim asserts, not as settled facts.

**(A) Hardness segment.** For every rational `c in [1/2, 1)` and every `eps in (0, (1-c)/2)`
there is `l = l(eps)` such that it is NP-hard to tell linear unique games over
`F_2^l` (constraints `T x_i + T' x_j = b`, `T, T'` invertible) of value
`>= c - eps` from value `<= 2c - 1 + eps`.

**(B) Linear-loss kill.** Fix `C < 2`. There is a fixed alphabet size
`k(C) = 2^(l(eps_C))` with the following property. Suppose a polynomial-time
algorithm `A` and a rational `x in (0, 1/2]` satisfy: for every unique game `U`
over `[k(C)]` with `val(U) >= 1 - x`, `A(U)` is a labeling of value `>= 1 - C x`.
Then `P = NP`. The same holds for any polynomial-time relaxation `Rel >= val`
with a rounding guarantee `Rel(U) >= 1 - x  =>  A(U)` has value `>= 1 - C x`.

**The invariant and the step where every member dies.** The invariant is the
*branch multiplicity* `2` of the proved 2-to-2 constraints: an honest labeling
satisfies exactly one of the two unique branches, so the split halves the value.
Disjoint-union mixing with a satisfiable game carries the halved point `(1/2, 0)`
along the segment to `(1, 1)`, where the completeness error is `x` and the
soundness error is `2x`. A rounding with loss constant `C < 2` separates the two
errors, so it dies at the decision step of (B) on these mixed instances, at every
scale `x`, including `x -> 0`, and already at one fixed alphabet.

**What it does not kill** (granting (B)). Rounding losses that grow with the alphabet (the
`1 - O(sqrt(eps log k))` of CMM, `1 - O(eps log k)` of
`elementary-abelian-galois-games-round-with-linear-loss`), losses with constant
`>= 2`, and guarantees that are not linear in the completeness error. It neither
proves nor refutes `unique-games-conjecture`.

**Phase diagram this would record** (points `(c, s)` of `Gap-UG[c, s]` with the
alphabet allowed to depend on the point):

* `c = 1`: in P for every `s < 1` (propagation; perfect unique games are easy).
* `s > max(0, 2c - 1)`, `c < 1`: NP-hard, by (A) — unrefereed — and, for `c < 1/2`,
  by the one-half theorem itself, which is established independently of (A).
* `0 < s < 2c - 1`: unknown unconditionally. `unique-games-conjecture` says all of
  it is NP-hard, and a refutation must put an easy point here
  (`unique-games-gap-admits-polynomial-time-algorithm`).

**Two monotonicity remarks, not part of the claimed statement.** If
`c' >= c` and `s' <= s`, then `Gap-UG[c', s']` is a restriction of
`Gap-UG[c, s]`. So:

1. An algorithm for one point `(c, s)` with `0 < s < 2c - 1` decides
   `(1 - eps, eps)` for every `eps <= min(s, 1 - c)`.
2. `(1 - eps, eps)` lies strictly below the line whenever `eps < 1/3`.

So "some point strictly below the line is in P" is equivalent to the refutation
form. "Every point strictly below the line is NP-hard" is equivalent to
`unique-games-conjecture`. The whole open part of UGC lives in the open triangle
below the line, and the line itself is where the proved theory stops.

**Conditional SoS form.** If `sos-cannot-refute-unique-games-at-completeness-one-half`
is established, the same mixing gives degree-`N^c` SoS pseudo-value
`>= 1 - x(1+eps)` on instances of value `<= 1 - 2x(1-eps)`: the product of the
pseudo-distribution with the honest assignment of the satisfiable component is a
valid pseudo-distribution, and pseudo-values add over disjoint components. Then
every SoS rounding with linear loss constant `C < 2` fails unconditionally. This
remark is not part of the claimed statement.

## Attempts

* **Disjoint-union mixing with a satisfiable identity edge** (e-ugc-pull-inverter,
  wave swarm-0917, 2026-09-18). Full write-up:
  `research/artifacts/unique-games-line-mixing-2026-09-18.md`. Take a hard
  instance `U` of `Gap-UG[F_2^l]((1-eps)/2, eps)` from
  `unique-games-hard-at-completeness-one-half` and form the disjoint union of `U`
  at weight `lambda` with a single satisfiable edge `x_p + x_q = 0` at weight
  `1 - lambda`, so `val(W) = lambda val(U) + 1 - lambda`. Setting
  `lambda = 2(1-c)` gives (A); setting `lambda = 2x/(1+eps_C)` gives (B). The
  argument is elementary and the author found no gap in it.
  **Why this claim is nevertheless OPEN:** the wave's three-lens adversarial
  referee stage produced no verdicts for this result — the votes were lost before
  they reached the lander, so the establishment is unconfirmed rather than
  contested. The wave's rule is that an unrefereed establishment lands OPEN. The
  proof is therefore kept as this attempt instead of as a `kind: route` node.
  Next step: referee the artifact on the three standard lenses (first step that
  does not follow; whether the KMS import is used with exactly its quantifiers
  and hypotheses; calibration). If it survives, promote the artifact to a route
  `unique-games-line-mixing-proof` with
  `target: unique-games-np-hard-above-the-two-c-minus-one-line` and
  `requires: [unique-games-hard-at-completeness-one-half]`, which establishes this
  claim with no further mathematics. Until then this claim is an isolated lane
  top, so `bin/cairn check` reports it as sitting on no live path to a root; that
  warning is expected and clears when the route is added.
