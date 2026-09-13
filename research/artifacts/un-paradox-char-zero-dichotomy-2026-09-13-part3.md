# Characteristic zero: stable finiteness of the Steinberg algebra is exactly an invariant measure

Lane `un-paradox` (UN swarm, target U1), 2026-09-13. Part 3.
- Part 1 (`un-paradox-stable-infiniteness-2026-09-13.md`) is the ring theorem.
- Part 2 (`un-paradox-groupoid-tarski-2026-09-13-part2.md`) is the groupoid paradox side.

Status: complete proof, **unreviewed**. Two imports, each read verbatim from the arXiv PDF on
2026-09-13: Rainone–Sims arXiv:1707.04516v2, Theorem 6.5, and Sims arXiv:1710.10897, Corollary 3.3.4.

## 0. Statement

**Theorem D0.** Let `𝒢` be a minimal, ample, Hausdorff, second countable groupoid with compact unit
space `X`, and let `k` be a countable field of characteristic 0. The following are equivalent:

1. `A_k(𝒢)` is stably finite.
2. `X` carries a `𝒢`-invariant Borel probability measure.

If they fail, some `n` has `2n[1] <= n[1]` in `V(A_k(𝒢))`, and every homomorphism from
`EL_N(A_k(𝒢))` to an MF group is trivial for `N >= 2n` (Part 2).

**Reading for U1.**
- In characteristic 0, for minimal Hausdorff ample groupoids, the ring-level hypothesis of the
  one-sided transport mechanism (stable infiniteness, Part 1) holds exactly when there is no invariant
  measure: Tarski's paradox side.
- Positive characteristic (Part 2, Firewall K): the implication 2 ⇒ 1 for free minimal Cantor actions
  already contains Kaplansky's stable finiteness conjecture over `k`.
- Not claimed: that an invariant measure makes `EL_N(A_k(𝒢))` MF. Stable finiteness only switches off
  this particular mechanism. The measure side is lanes un-measure and un-converse.

## 1. Imports

**Import RS** (Rainone–Sims, Theorem 6.5, verbatim). "Let G be an étale groupoid with compact unit space
G(0). Consider the following properties. (i) The C∗-algebra C∗r(G) admits a faithful tracial state.
(ii) The C∗-algebra C∗r(G) is stably finite. (iii) G satisfies the coboundary condition. (iv) G is
completely non-paradoxical. The implications (i) ⇒ (ii) ⇒ (iii) ⇒ (iv) always hold. If G is minimal,
then (iv) ⇒ (i) and all properties are equivalent."

In the proof of (iii) ⇒ (iv), "not completely non-paradoxical" means: there are a non-empty clopen
`A ⊆ G(0)`, integers `k > l > 0` and compact open bisections `E_1, …, E_n` with
`k 1_A <= sum 1_(s(E_i))` and `sum 1_(r(E_i)) <= l 1_A`.

**Import S** (Sims, Corollary 3.3.4, verbatim, first sentence). "Suppose that G is a second-countable
locally compact Hausdorff étale groupoid. Then the homomorphisms πmax ∶ Cc(G) → C∗(G) and
⊕x πx ∶ Cc(G) → Cr∗(G) are both injective."

## 2. Proof of 2 ⇒ 1

1. **Full support.** Let `μ` be an invariant probability measure. Its support is closed, nonempty and
   invariant. By minimality it is `X`.
2. **Completely non-paradoxical.** Suppose `k 1_A <= sum 1_(s(E_i))` and `sum 1_(r(E_i)) <= l 1_A`
   with `A` non-empty clopen and `k > l`. Integrating against `μ`, and using `μ(s(E_i)) = μ(r(E_i))`,
   gives `k μ(A) <= l μ(A)`, so `μ(A) = 0`. That contradicts full support.
3. **Stably finite C*-algebra.** By Import RS with `G` minimal, `C*_r(𝒢)` is stably finite.
4. **Stably finite ring.** Let `B` be a unital C*-algebra in which every isometry of every `M_m(B)` is
   a unitary; this is C*-stable finiteness. If `ts = 1` in `M_m(B)`:
   - `s*s = s* t* t s >= ||t||^(-2)`, so `s*s` is invertible;
   - `v = s (s*s)^(-1/2)` is an isometry, hence a unitary;
   - so `s = v (s*s)^(1/2)` is invertible, `t = s^(-1)`, and `st = 1`.
   So `M_m(B)` is directly finite as a ring.
5. **Subring.** `k` is countable of characteristic 0, so it embeds in `C`. Then
   `A_k(𝒢) ⊆ A_C(𝒢) ⊆ C_c(𝒢)`, and by Import S, `C_c(𝒢) -> C*_r(𝒢)` is injective. So `A_k(𝒢)` is a
   unital subring of `C*_r(𝒢)`, and `M_m(A_k(𝒢)) ⊆ M_m(C*_r(𝒢))`. A one-sided inverse in the smaller
   ring is two-sided in the larger, hence in the smaller. QED

## 3. Proof of 1 ⇒ 2

This is the contrapositive of Part 2, Sections 1–3, valid for every field.
- With no invariant probability measure, some `n` has `2n[X] <= n[X]` in `S(𝒢)` (Tarski plus ABBL
  Lemma 2.3).
- Hence `2n[1] <= n[1]` in `V(A_k(𝒢))`.
- So `M_n(A_k(𝒢))` has a properly infinite unit (Part 1, Lemma 1) and is not directly finite
  (`w_0 v_0 = 1` with `v_0 w_0 != 1`, since `w_1 v_1 = 1` forces `v_1 != 0` with `(1 - v_0 w_0) v_1 = v_1`).
- So `A_k(𝒢)` is not stably finite. QED

## 4. Model tests

- **Minimal Z-subshift (Pestov 9.1 ring over a char-0 field).** An invariant measure exists, so the
  ring is stably finite. Consistent with LEF embeddings.
- **Cuntz groupoid and boundary actions of `F_d`.** No invariant measure, so not stably finite, with
  `n = 1`.
- **Nonminimal counter-test.** For a groupoid with a closed invariant subset carrying no measure while
  another part carries one, 2 ⇒ 1 can fail. Minimality is used in step 1.
