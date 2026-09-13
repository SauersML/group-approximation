---
rg: 2
id: kun-thom-wreath-embeds-in-leavitt-unit-group
kind: claim
title: The Kun--Thom coset wreath embeds in the binary Leavitt unit group
distinct_from:
  kun-thom-wreath-carries-rigid-defect: that computes a nontrivial rigid defect inside the wreath; this asks whether the wreath is a subgroup of the binary Leavitt unit group.
  char-two-curve-linear-groups-satisfy-boone-higman: that embeds characteristic-two linear groups of transcendence degree at most one in the unit group; the wreath's actor contains SL_d(Z) with d >= 3, which is linear over no field of positive characteristic, and its vertex has transcendence degree d >= 3.
  leavitt-pair-vertex-rounding-is-nonhyperlinearity: that shows the internal Leavitt pair cannot carry the arithmetic rounding of the Kun--Thom chain; this is the other way to bring that chain to bear on the unit group.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-l-times-2026-09-12.md
refuted_by:
  - kun-thom-wreath-does-not-embed-in-leavitt-unit-group
---

**OPEN.** Let `Gamma = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x_1^(+-1)..x_d^(+-1)]) semidirect SL_d(Z)`
be the Theorem E pair of `kun-thom-nonsofic-wreath`, with `r, d >= 3`, and let

```text
W = (direct_sum_(G/Gamma) Z/2) semidirect G .
```

The claim is that `W` embeds as a subgroup of `Q = L_(F_2)(1,2)^x` for some admissible `(q, r, d)`.

**Payoff.**
* **Nonhyperlinearity of `Q`.** Hyperlinearity passes to subgroups. So if the Kun--Thom chain
  `kt-wreath-nonhyperlinear-via-unit-type-vertex-rounding` closes, `Q` is not hyperlinear and
  `leavitt-steinberg-hs-stable` holds (route `leavitt-nonhyperlinear-via-kun-thom-wreath-embedding`).
* **Refutation in the other direction.** If `Q` is hyperlinear and this claim holds, then `W` is
  hyperlinear. Its other two premises are established, so that refutes
  `theorem-e-vertex-rounds-to-unit-type-representations`.
* **Alternatives.** The same transfer works for any group with the same hyperlinearity status, such as
  the double `G *_Gamma G` or `G *_Gamma (Gamma x Z)` (`kt-wreath-hyperlinear-iff-double-hyperlinear`).
  Every alternative still contains `G`.

## Attempts

* **The actor is not linear in positive characteristic** (lane `hyperlinear-nonsofic-l-times`,
  2026-09-12). This is proved here, and it rules out every matrix embedding over a commutative
  subring of `L_(F_2)(1,2)`.
  1. Let `a, b` lie in `GL_n(K)`, `char K = p > 0`, and suppose `c = [a,b]` commutes with `a` and
     `b`.
  2. `a` and `b` preserve every generalized eigenspace `E` of `c`. On `E`, `a b a^-1 = c b`, so
     `det(b|E) = lambda^(dim E) det(b|E)`, and `lambda` is a root of unity.
  3. So the semisimple part of `c` has finite order. The unipotent part has `p`-power order, so `c`
     has finite order.
  4. The integer Heisenberg group inside `SL_d(Z) <= G` has an infinite-order central commutator.
     So `G` has no faithful linear representation over any field of positive characteristic.
* **The regular-representation embedding stops at transcendence degree one.** This is recorded on
  `char-two-curve-linear-groups-satisfy-boone-higman`. The vertex needs `F_q[x_1..x_d]` with `d >= 3`,
  and the semidirect factor `SL_d(Z)` is not linear anyway, by the previous item.
* **Commuting Thompson elements give no second variable.** Let `g, h` in the embedded `V` have
  disjoint supports. `R` is simple, so the Chen module on infinite paths is faithful. On it, the
  paths show `(g - 1)(h - 1) = 0` in `R`, so `F_2[g^(+-1), h^(+-1)]` is not a Laurent ring in two
  variables.
* **Digit interleaving fails.** Realizing `C ~= C x C` by odd and even digits makes length-preserving
  prefix replacements act coordinatewise. An infinite-order element of `V` changes lengths, and then
  it moves infinitely many digits between the two coordinates. So it acts on no single factor.
* **The sharpest first test.** An embedding needs `Q` to contain a copy of `H_3(Z)` whose central
  commutator has infinite order. The previous items show that such a copy cannot come from matrices
  over commutative subrings, or from disjointly supported elements of `V`.
* **The test is now its own node, with two firewalls** (lane `ex-q34-leavitt-hs`, 2026-09-12). The
  Heisenberg question is `leavitt-unit-group-has-no-integer-heisenberg-subgroup`. A positive answer
  refutes this claim for every parameter, through `kun-thom-wreath-does-not-embed-in-leavitt-unit-group`.
  - `thompson-v-has-no-heisenberg-subgroup` (established): a Heisenberg subgroup of `Q` is not
    contained in any conjugate of `V`, because cyclic subgroups of `V_n` are undistorted.
  - `leavitt-north-south-thompson-unit-has-cyclic-centralizer` (established): the north--south
    unit `c = s_00 t_0 + s_01 t_10 + s_1 t_11` has `C_Q(c^a) = <c>`. So no Heisenberg center is
    conjugate to a power of `c`.
  - Two exact screens (`research/artifacts/leavitt-unit-depth-growth-experiment-2026-09-12.md`)
    followed about 1200 short random units for at least 8 powers without detecting a finite order.
    Apart from bounded-depth units of large finite order, none met the screens' criteria for
    sublinear depth growth.
    Heisenberg centers have sublinear depth growth, so this is evidence against them. It is not a
    proof.
  - A center that is a genuinely linear unit remains unexcluded.
  - `leavitt-unit-groups-over-finite-fields-mutually-embed` makes the question the same for every
    `L_(F_q)(1,n)^x` with `q` a power of `2`.
