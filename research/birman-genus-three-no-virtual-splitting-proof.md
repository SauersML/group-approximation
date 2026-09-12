---
rg: 2
id: birman-genus-three-no-virtual-splitting-proof
kind: route
title: Run Chen--Salter's handle-pushing argument on the genus-two side, with mapping-class-group rank bounds and a one-sided Euler-class lemma
target: birman-sequence-genus-three-does-not-virtually-split
requires: []
artifacts:
  - research/artifacts/bh-birman-genus3-section-2026-09-12.md
---

Direct proof. It adapts L. Chen and N. Salter, arXiv:1804.11235v1: Section 2 and
the proof of Theorem A in Section 3, read in full from the PDF on MSI. Their
Propositions 2.2--2.7 and Lemma 2.8 hold in any `Mod(S)`. Their Lemmas 3.3 and
3.5--3.8 and Section 3.4 are arguments in `π1(Σ_p)` needing only `p ≥ 2`. All of
these are used as written. Every place that needs `g ≥ 4` is replaced as follows.
The artifact, §3, has the full text.

**Setting.** Suppose `L ≤ Mod(Σ_3)` has finite index and `σ: L → Mod(Σ_3, ∗)`
satisfies `p∘σ = id`. Then `σ` is injective, and it may be restricted to
finite-index subgroups at will.

**Tools.**
- **Compatibility (F).** For `f` fixing a multicurve `M̃` and its complementary
  components, restriction then forgetting `∗` on a component equals restriction of
  `p(f)` on its projection.
- **Rank (R).**
  - A pants decomposition supplies `Z^6 ≤ L` of twist powers.
  - A class that is pseudo-Anosov on `j` components, with CRS `M̃`, and whose other
    components have finite pure mapping class group modulo boundary twists, has a
    centralizer that is virtually abelian of rank `≤ |M̃| + j`.

**Lemma A (bounding pairs).** Chen--Salter's Lemma 2.9(1) holds in genus 3 for
`x = T_a T_b^{-1}`.
- **Step 1.** Use a crossing curve `δ` disjoint from `a ∪ b`.
- **Step 2.** An empty CRS, or a CRS isotopic to one of `a, b` only, gives a
  centralizer of rank `≤ 3`, against `Z^6`.
- **Step 3.**
  - Suppose `ρ_{C̃}(σ(x^k))` is pseudo-Anosov over a side `S`. McCarthy gives
    `ρ_{C̃}(σ(T_δ^r))^j = ρ_{C̃}(σ(x^k))^i`.
  - Forgetting `∗` and using (F) gives `T_δ^{rj} = 1` in `Mod(S^)`, which is false.

**Lemma B (separating twists).** Every essential separating curve `c` of `Σ_3`
bounds a one-holed torus. Running the same three steps gives
`σ(T_c^k) = T_{c'}^{k-n} T_{c''}^{n}`, with `c'` and `c''` isotopic to `c`.

**Lemma C (single lift).** The CRS of `σ(T_c^k)` is a single curve.
- **Setup.** Suppose it is `{c_T, c_R}`, with the once-punctured annulus between them.
  Let `D'' ≤ π1(UT Σ_2) ∩ L`, the disk-pushing group of the genus-2 side, have finite
  index.
- **Splitting.** (F) and the cutting sequence put `σ(D'')` in
  `Mod(R̃) × ⟨T_{c_T}⟩`. The second coordinate is a homomorphism `ν: D'' → Z`
  with `ν(T_c^{kN}) ≠ 0`.
- **Contradiction.** `D''` is a central extension of a closed surface group with
  nonzero rational Euler class, since `χ(Σ_2) ≠ 0`. So its center dies in
  `H_1(D''; Q)`, and `ν(T_c^{kN}) = 0`.

**Lemma D (marked point).** Take disjoint separating curves `c_1, c_2` bounding
disjoint one-holed tori. Their lifts bound disjoint tori, so for one `i` the marked
point lies on the genus-2 side of `c̃_i`.

**Section 3 with `p = 2` and `c = c_i`.**
- **Support.** By (F), `σ(Mod(R) ∩ L)` is supported on `R̃ = Σ̃_{2,1,∗}`.
- **Diagram and Lemma 3.1.** Diagram (6) and Lemma 3.1 follow, using Lemma C.
- **Lemma 3.2 for all simple `α`.**
  - Nonseparating `α` use Lemma A.
  - Separating `α` use Lemma C. It gives `s(α^k) ∈ {1, α^{±k}}` directly.
- **Rest of Section 3.** Lemma 3.3, Corollary 3.4 and Lemmas 3.5--3.8 go through as
  written.
- **Contradiction.** Section 3.4 gives `(i × s)^∗[Δ] = 0`, while it equals
  `χ(Σ_2)[H̄] ≠ 0` in Case (A) and `[H̄] ≠ 0` in Case (B). `∎`

**Not re-read from source:** Farb--Margalit Prop. 3.20 and Thm. 3.18, and McCarthy's
theorem. There is no Lean counterpart.
