---
rg: 2
id: ct-z-torsion-certificate-periodic-itinerary
kind: claim
title: "Torsion in CT(Z): a periodic itinerary with block slope ≠ 1 is a semi-decidable certificate of infinite order (by a closing lemma for boxes), and slope-1 recurring blocks are the identity; it is complete whenever every minimal set contains an eventually periodic itinerary, which holds for all monomial elements (a proof independent of Kari–Ollinger); so torsion in CT(Z) is decidable unless some element has a minimal set with square-free itineraries"
requires:
  - ct-z-torsion-reduces-to-hyperbolic-primes
  - ct-z-monomial-elements-have-decidable-torsion
  - ct-z-residue-partition-certificates-live-on-s-adic-coordinates
---

**ESTABLISHED** (lane proof, not reviewed). Elementary and self-contained. No priority is claimed.
- This works on Conjecture 7 of `ct-z-torsion-reduces-to-hyperbolic-primes`.
- It replaces certificates (a) and (b) there with one certificate (e). Certificate (e) catches both
  counterexamples of that node's Proposition 5.
- It proves (e) complete under a hypothesis that monomial elements satisfy.
- It reduces full decidability of torsion in `CT(Z)` to one statement about square-free minimal
  sets (Conjecture 6).
- The torsion problem of `CT(Z)` stays **OPEN**.

## Setting

- **The space.** `g ∈ CT(Z)`, and `S` is the set of primes dividing its moduli, so every slope is a
  positive `S`-unit. `ĝ` acts on `Ẑ_S`, and `L` is the lcm of the moduli.
- **Itineraries.** The *itinerary* of `x ∈ Ẑ_S` is the sequence of classes `ĝ^t(x) mod L`, for
  `t ≥ 0`.
- **Blocks.** A *block* is a word `β` of length `n` over the classes mod `L`.
  - `D_β` is the set of points whose itinerary begins with `β`. It is a box or empty, since it is an
    intersection of preimages of boxes under affine maps.
  - On `D_β`, `ĝ^n` is a single rational affine map `A_β(x) = U_β x + B_β`.
- **Certificate (e).** There is a block `β` with `D_{ββ} ≠ ∅` and `U_β ≠ 1`.
  - This is Σ₁: enumerate words and compute the boxes.
  - `D_{ββ} ≠ ∅` iff `A_β(D_β) ∩ D_β ≠ ∅`.

## Statement

**Lemma 1 (recurring slope-1 blocks are trivial).** If `U_β = 1` and `A_β(D_β) ∩ D_β ≠ ∅`, then
`A_β` is the identity on `D_β`. So every point of `D_β` is fixed by `ĝ^n`.

**Lemma 2 (closing lemma).**
- **Hypothesis.** `U_β ≠ 1` and `A_β(D_β) ∩ D_β ≠ ∅`.
- **Conclusion.** Let `E_β` be the product of:
  - `{y*_p}` for the primes `p` where `|U_β|_p > 1`, with `y* = B_β/(1 − U_β)`;
  - the ball `(D_β)_p` for every other `p ∈ S`.

  Then `E_β` is nonempty, `A_β(E_β) ⊆ E_β`, and every point of `E_β` has itinerary `β^∞`.

**Theorem 3 ((e) certifies infinite order).** If (e) holds, `g` has infinite order.

**Theorem 4 (completeness under itinerary tameness).** Suppose every minimal set of `ĝ` contains a
point with an eventually periodic itinerary. Then `g` has infinite order iff (e) holds. So torsion is
decidable on every class of elements with this property: run the search for `N` with `g^N = 1`
alongside the search for (e).

**Corollary 5 (monomial elements, without Kari–Ollinger).** Every monomial `g` (piecewise
`n ↦ λn`) satisfies the hypothesis of Theorem 4. So its order is infinite iff (e) holds.
- This decides torsion on `Mon` directly, replacing the appeal to Kari–Ollinger Thm 4 in
  `ct-z-monomial-elements-have-decidable-torsion`.
- It covers `F_M` for periodic, non-uniformly periodic `M`, where compression fails.

Elements with `H(g) ⊆ {2}` also satisfy the hypothesis, by the structure theorem for `V` applied to
the quotient of `ct-z-torsion-reduces-to-hyperbolic-primes`. The counterexample
`ψ_{0(3)}τ_{1(3),2(9)}` of that node satisfies (e).
- Near the attractor, `x_2` stays in `14 + 16Z_2`, while `x_3 = 3u` has `u ↦ 4u + 2`.
- So the itinerary mod `L = 144` has period 3, and `U_β = 4^3 ≠ 1`.

**Conjecture 6 (the remaining case).**
- **The reduction (proved).** If (e) fails, every minimal set of `ĝ` is either a periodic orbit,
  on which `ĝ^n` is the identity nearby, or has a *square-free* itinerary subshift, i.e. no
  itinerary contains a factor `ww`.
- **The conjecture.** No element of `CT(Z)` has a minimal set with square-free itineraries unless
  (e) holds.
- **What it would give.** Torsion in `CT(Z)` would be decidable, and then `2V ⊄ CT(Z)`.
- **Further reduction.** By lane bh-free-57's closing theorem (861494c34), an ergodic measure with
  every Lyapunov exponent nonzero yields a periodic point of slope `≠ 1`, which is a case of (e).
  So Conjecture 6 is needed only for square-free minimal sets all of whose ergodic measures have a
  zero exponent at some surviving prime.

## Proofs

**Lemma 1.**
- **The block fixes its box.** Slope 1 means `A_β(D_β)` is a box of the same modulus as `D_β`, and
  two such boxes that meet are equal. So `A_β` translates the class `D_β ∩ Z = r(m)`, with
  `0 ≤ r < m`, onto itself by some `B ∈ mZ`. Here `B` is an integer because `g^n` maps integers to
  integers.
- **The translation is zero.** Every element of `CT(Z)` satisfies `k ≥ 0 ⇔ g(k) ≥ 0`: class
  transpositions do, hence so do their products and powers. If `B > 0`, the point `r − m < 0` goes
  to `r − m + B ≥ 0`. If `B < 0`, the point `r ≥ 0` goes to `r + B < 0`. So `B = 0`. ∎

**Lemma 2.** Fix `p ∈ S`. The balls `(D_β)_p` and `A_β((D_β)_p)` meet, so one contains the other.
- If `|U|_p > 1`, then `A_β((D_β)_p) ⊇ (D_β)_p`, so `A_β^{-1}` maps `(D_β)_p` into itself and
  contracts it. Its fixed point `y*_p` lies in `(D_β)_p`.
- If `|U|_p < 1`, then `A_β((D_β)_p) ⊆ (D_β)_p`.
- If `|U|_p = 1`, the balls have equal radius, so `A_β((D_β)_p) = (D_β)_p`.

In every case `A_β(E_β) ⊆ E_β ⊆ D_β`, so `A_β^k(y) ∈ D_β` for all `k`. That means the itinerary of
`y` is `β^∞`. ∎

**Theorem 3.** By Lemma 2 there is `y` with `ĝ^{kn}(y) = A_β^k(y) = y* + U^k(y − y*)`.
- **If `y = y*`**, then `y` is periodic, and the germ of `ĝ^{nN}` at `y` has slope `U^N ≠ 1` for
  every `N`. So `g^N ≠ 1`.
- **Otherwise**, `U^k ≠ 1` in every `Q_p`, so the points `A_β^k(y)` are pairwise distinct and the
  orbit of `y` is infinite. ∎

**Theorem 4.** Assume (e) fails.
- **Step 1: every point is periodic.** Suppose `x` has an infinite orbit.
  - Its `ω`-limit set contains a minimal set `Mn`. By hypothesis `Mn` contains a point whose image
    `z′ = ĝ^{t_0}(z)` has periodic itinerary `β^∞`.
  - Then `D_{ββ} ∋ z′`, and `U_β = 1` because (e) fails. By Lemma 1, `ĝ^n` is the identity on the
    open box `D_β ∋ z′`.
  - The orbit of `x` enters `D_β`, because `z′ ∈ ω(x)`. So some `ĝ^t(x)` is periodic, and hence `x`
    is periodic. This is a contradiction.
- **Step 2: finite order.** Every periodic point `z`, of period `n`, has periodic itinerary `β^∞`
  with `|β| = n`. Again `U_β = 1`, so `ĝ^n = 1` on the box `D_β ∋ z`. These boxes cover the compact
  space `Ẑ_S`, so finitely many do, and `ĝ^N = 1` for the lcm `N` of their periods. ∎

**Corollary 5.** Let `g` be monomial: `ĝ(x) = λ_{[x]} x`.
- **Strata.** For `A ⊆ S`, the closed set `Z_A = {x : x_p = 0 for p ∈ A}` is invariant under `ĝ`
  and `ĝ^{-1}`, since multiplying by an `S`-unit preserves zero coordinates.
- **A minimal set lies in one stratum.**
  - Let `Mn` be minimal, and choose `y ∈ Mn` whose zero set `B = {p : y_p = 0}` is maximal.
  - Then `Z_B ∩ Mn` is closed, invariant and nonempty, so it equals `Mn`. So every point of `Mn` has
    zero set exactly `B`.
- **Bounded counters.** For `p ∉ B`, write `x_p = p^{e_p}u_p`.
  - If some counter `e_p` were unbounded along an orbit in `Mn`, a limit point would have `x_p = 0`.
    It would lie in `Mn` with a larger zero set, which is impossible.
  - So the counters are bounded on each orbit in `Mn`.
- **Periodic itinerary.** The class `ĝ^t(x) mod L` is a function of the base data: the counters,
  and the unit parts `u_p` modulo `p^{k_p}`. That data evolves deterministically, since
  `e_p ↦ e_p + v_p(λ)` and `u_p ↦ u_p·λp^{−v_p(λ)}`. With the counters bounded it takes finitely many
  values, so it is eventually periodic, and so is the itinerary. ∎

**The reduction in Conjecture 6.** Let `Mn` be minimal, (e) fail, and some itinerary in `Mn`
contain `ww`, say at `ĝ^t(y)`.
- Then `D_{ww} ≠ ∅`, and `U_w = 1` because (e) fails. By Lemma 1, `ĝ^{|w|}` fixes `ĝ^t(y)`.
- So `Mn` is a periodic orbit, and `ĝ^{|w|}` is the identity on a box around it. ∎

## What this says

- **One certificate.** (e) replaces (a) and (b). It is complete wherever minimal sets have
  eventually periodic itineraries, and in particular on `Mon`. There the gap between "all cycles
  finite" and "bounded order" (the `F_M` case) is closed by the stratum argument.
- **Where the question now sits.** Minimal sets whose itineraries avoid every square `ww`, and whose
  ergodic measures all have a zero exponent at some surviving prime.
  - Squares close up by Lemma 2.
  - Fully hyperbolic measures close up by 861494c34.
  - Both closing lemmas rest on the same ultrametric fact: two balls that meet are nested.
- **Next step, jointly with bh-free-57.**
  - Show that a zero exponent at a prime on a non-compressible minimal set forces that prime's
    slopes to be units on the recurrent set. Then the isometric collapse of
    `ct-z-torsion-reduces-to-hyperbolic-primes` applies, and induction on the number of hyperbolic
    primes closes the argument.
  - Alternatively, show that affine boxes force squares in every minimal itinerary subshift.

## Lesson for general BH

**In ultrametric affine dynamics, recurrence is periodicity.**
- Two balls that meet are nested. So whenever a block of an itinerary recurs immediately (a square
  `ww`), the block's affine map has a nonempty invariant box. Its slope is then either `≠ 1`, a
  periodic itinerary of infinite order, or `1`, the identity in `CT(Z)` because `N_0` is preserved.
- The only way to avoid finite certificates is square-free recurrence.
- **Transferable principle.** For hosts built from affine maps of `Ẑ` (`CT_P`, `R_P`, `B`), dynamical
  finiteness questions reduce to combinatorics on itinerary words plus Lyapunov exponents. Uniform
  hardness can live only in square-free, zero-exponent minimal sets.
