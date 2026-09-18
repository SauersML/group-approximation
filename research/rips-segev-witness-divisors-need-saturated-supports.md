---
rg: 2
id: rips-segev-witness-divisors-need-saturated-supports
kind: claim
title: A zero divisor on {1,a,b,ab} in a Rips--Segev core must be rank two with a saturated support, and extreme-coefficient data cannot exclude it
distinct_from:
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this reduces its witness-support case to a coefficient-free statement about finite subsets of K.
  rips-segev-witness-pairs-carry-no-zero-divisors: that excludes annihilators supported on the witness set A; this constrains every annihilator, and settles rank one for every coefficient pattern.
  rips-segev-witness-supports-carry-no-zero-divisors: that uses clean a-squares on the specific support A; this turns the clean-square argument into a saturation condition on an arbitrary support.
  rips-segev-port-data-cannot-exclude-balanced-divisors: that kills port-data arguments; this extends the kill to ports plus top and bottom coefficients, and shows the realizing configuration is not saturated.
  rips-segev-cores-have-no-infinite-cyclic-quotient: that kills quotient gradings; this is a direct coefficient-level reduction inside K.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-witness-divisors-need-saturated-supports-proof`.

**Setting.**  `G` is torsion-free, `S = {1, a, b, ab}` has four elements, and `a, b, ab, a^{-1}b, b^{-1}ab` have
infinite order (true in the core `K` and in every generalized Rips--Segev group).  Let
`beta = c_0 + c_1 a + c_2 b + c_3 ab != 0` and `D = c_0 c_3 - c_1 c_2`.

**Theorem.**
1. **Rank one.**  If `D = 0` then `beta = (x_0 + x_1 a)(y_0 + y_1 b)` is a non-zero-divisor, for every
   coefficient pattern, with any number of nonzero coefficients.
2. **Rank two forces saturation.**  If `D != 0`, `Sigma = supp beta` and `alpha beta = 0` with `alpha != 0`, then
   `X = supp alpha` satisfies:
   - (N) no product in `X Sigma` has exactly one expression `x s`, `s in Sigma`;
   - (C) for all `h, h a in X`, at least one of `h a`, `h a b` has at least three expressions in `X × S`.

   The left analogue holds for `beta alpha = 0`: for all `y, b y in X`, at least one of `b y`, `a b y` has at
   least three expressions in `S × X`.
3. **Extreme data is realized.**  If every line endpoint of `Gamma` is both a source and a target of `b`-edges, and
   no `b`-edge joins two endpoints (Steenbock's graphs satisfy both), then `Gamma`'s port configuration in `K`,
   with arbitrary nonzero top and bottom coefficients, satisfies every constraint that the zero product imposes at
   extreme points.  This holds for all nonzero `c_j`, whether `D = 0` or not.
4. **Reduction.**  If `K` has no finite nonempty right or left `Sigma`-saturated subset, for every `Sigma`
   containing `{1, ab}` or `{a, b}`, then every element of `k[K]` and of `k[G(Gamma)]` supported on `S` is a
   non-zero-divisor, for every field `k`.  Only this direction is claimed.

**Calibration.**
- In unique-product groups (for example `F_2`) condition (N) already fails for every `X`.
- In `K` the witness set `A` satisfies (N) but fails (C).
- In `Z/2 × Z/2`, `alpha = 1 + a + b + ab` and `beta = 1 + a + b - 3ab` (with `D = -4`) give `alpha beta = 0`, and
  `supp alpha` is saturated.  So saturated sets carrying rank-two zero divisors exist once torsion is allowed.

**Class killed.**  Arguments that exclude a witness zero divisor using only ports and top or bottom coefficients.
- **Exact failing step:** Theorem 3.  `Gamma` has no extreme coincidences, since endpoint sources map to interior
  targets and endpoint targets come from interior sources.  So these arguments cannot see `D`, and the extreme data
  are the same when `D = 0`, where regularity holds.

**Next step.**  Decide whether `K` contains a finite set satisfying (N) and (C) for `Sigma = S`.
- Condition (C) says that every `a`-adjacent pair `h, h a` has a triple product at `h a` or at `h a b`.
- The proposed attack is a van Kampen or walk argument on a maximal `a`-run of `X`.  At its top pair, a triple at
  `h a` or `h a b` must come from a relator piece, and `Gr'_*(1/8)` bounds how often that can happen.
- Alternatively, find a nontrivial unique-product quotient of `K`.
