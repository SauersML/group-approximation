---
rg: 2
id: rips-segev-short-syllable-two-layer-elements-are-regular
kind: claim
title: In a Rips--Segev core every element supported on {1,a,b,ab} is a non-zero-divisor, and so is every short-span u(a)+w(a)b; the core has no nontrivial left-orderable quotient
distinct_from:
  rips-segev-witness-divisors-need-saturated-supports: that reduces rank-two witness divisors to the non-existence of finite saturated sets and leaves it open; this proves the regularity directly, bypassing saturation, by closing a short-syllable alternating walk and excluding it with small cancellation.
  rips-segev-core-large-gap-two-layer-elements-are-regular: that needs an offset outside [Delta_-, Delta_+] and uses only supports; this covers the balanced region it cannot reach (span below the minimal line gap), using the 2x2 coefficient determinant.
  rips-segev-witness-supports-carry-no-zero-divisors: that excludes annihilators supported on the witness set A; this excludes every annihilator, of any support.
  rips-segev-port-data-cannot-exclude-balanced-divisors: that shows port data alone cannot exclude balanced divisors; this uses the full coefficient data of each coset, which that obstruction does not constrain.
  rips-segev-cores-have-no-infinite-cyclic-quotient: that kills Z, locally indicable and bi-orderable quotients; part 3 here kills every nontrivial left-orderable quotient.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this settles its witness-support case and the short-span two-layer case.
artifacts:
  - experiments/rips-segev-short-syllable-2026-09-17/neighbour_check.py
  - experiments/rips-segev-short-syllable-2026-09-17/results.txt
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-short-syllable-two-layer-elements-are-regular-proof`.

**Setting.**
- `K = (<a> * <b>) / <<R>>` is the core of a generalized Rips--Segev graph `Gamma` whose labelling satisfies
  `Gr'_*(1/8)`.  `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2` for torsion-free `G_1 ∋ a`, `G_2 ∋ b`.
- A position `l` of line `i` is *distinguished* if the vertex `v_il` carries a `b`-edge.
- `m_Gamma` is the least distance `|l - l'|` between two distinct distinguished positions of one line.
- For Steenbock's explicit coefficient table `(10^{5i-4}, ..., 10^{5i})`, `m_Gamma >= 10`.
- For `u, w in k[t^{±1}]`, not both zero, let `g = gcd(u, w)`.  The *reduced span* `d(u, w)` is
  `max - min` of `supp(u/g) ∪ supp(w/g)`.

**Theorem.**  Let `k` be any field.  All statements hold in `k[K]` and in `k[G(Gamma)]`.
1. **Long b-syllables.**  If `m_Gamma >= 2`, every nonzero element of `k[<b>] + a k[<b>]` or of
   `k[<b>] + k[<b>] a` is a non-zero-divisor.  In particular this holds for every nonzero
   `beta = c_0 + c_1 a + c_2 b + c_3 ab`, whatever `D = c_0 c_3 - c_1 c_2` is.
2. **Short a-span.**  If `u, w in k[t^{±1}]` are not both zero and `d(u, w) < m_Gamma`, then `u(a) + w(a) b` and
   `u(a) + b w(a)` are non-zero-divisors.  For Steenbock's graphs this covers all `d(u, w) <= 9`, for example
   `(1 + a) + (1 + lambda a) b` for every `lambda`.
3. **No left-orderable quotient.**  For Steenbock's explicit graphs, every homomorphism from `K` to a
   left-orderable group is trivial.  So `K` has no nontrivial action on the real line by orientation-preserving
   homeomorphisms.

**Mechanism.**
- *Neighbour lemma.*  Let `x` have infinite order, `beta = u(x) + w(x) y` with `u, w` linearly independent of joint
  span `d`, and `alpha beta = 0`, `alpha != 0`.  Then `V = supp(alpha u) ∪ supp(alpha w)` is finite and nonempty.
  Every `p in V` has `p y` or `p y^{-1}` in `V`, and some `p x^n` in `V` with `1 <= |n| <= d`.  The second
  property uses the coefficients.  An isolated point would force `u` and `w` to be proportional.
- *Walk.*  Alternating `x`-steps and `y`-steps inside `V` closes into a relation
  `x^{n_1} y^{±1} ... x^{n_L} y^{±1} = 1` with `L >= 1` and `1 <= |n_k| <= d`.
- *Small cancellation.*  An exterior arc of a minimal van Kampen diagram contains a complete block
  `y^{±1} x^{n} y^{±1}`.  If `(x, y) = (a, b)`, the block lifts to an `a`-path on one line of `Gamma` whose two
  ends are distinguished, so `|n| >= m_Gamma`.  If `(x, y) = (b, a)`, a complete `a^{±1}` syllable between
  `b`-letters lifts to one `a`-edge with distinguished ends, so `m_Gamma <= 1`.
- Part 3 uses the positive relations of the explicit graphs, with all exponents `>= 99900` and with all exponents
  `<= -10`.

**What this settles.**
- The step asked of `rips-segev-witness-divisors-need-saturated-supports` is answered in the strongest form.  For
  graphs with `m_Gamma >= 2` (Steenbock's included), no zero divisor is supported on `{1, a, b, ab}`, so any
  saturated set there carries none.
- The saturation question itself is bypassed, not decided.  The neighbour lemma is a stronger necessary
  condition, and it is the one small cancellation can refute.
- Part 3 kills the route "find a unique-product quotient of `K` through a left-orderable quotient".  It dies at
  the two positive relations of opposite sign.

**Calibration.**
- `F_2`: no alternating relation exists, consistent with regularity.
- `Z^2`: `[a, b]` is an alternating relation with `|n_k| = 1`, so the method (correctly) gives nothing.
- `Z/2 × Z/2`: `(1 + a + b + ab)(1 + a + b - 3ab) = 0`, and `abab = 1` is the relation the walk reads.
- Finite groups (`experiments/rips-segev-short-syllable-2026-09-17/results.txt`): full left kernels over
  `GF(2), GF(3), GF(5)` in 124 random (permutation group, role, span) configurations, with 30393 kernel vectors in both roles
  `(x, y) = (a, b), (b, a)` and spans `d = 1, 2`.  The neighbour lemma had 0 failures, and every walk closed into
  a trivial word with the predicted exponent bounds.

**Limits.**
- Theorem 2 needs `d(u, w) < m_Gamma`.  Two-layer elements with reduced span in `[m_Gamma, N]` and balanced
  offsets (inside the large-gap box) remain open, as do elements meeting three or more `b`-layers.
- Theorem 1 needs `m_Gamma >= 2`.  A generalized graph may have one pair of distinguished positions at distance 1.
