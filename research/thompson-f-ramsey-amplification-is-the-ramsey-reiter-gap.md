---
rg: 2
id: thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap
kind: claim
title: In Thompson's F, the amplification problem ¬AMP is sandwiched between two Ramsey–Reiter gaps, one with a single and one with a double composition of the Ramsey function, so precision amplification is free and only the set-to-measure quantifier swap at precision 1/2 can be costly
distinct_from:
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is ¬AMP, stated with the fine Ramsey function R̃; this proves ¬AMP ⇒ RGAP₁ and RGAP₂ ⇒ ¬AMP, where both gaps compare R with the coarse Reiter radius CR and do not mention R̃ or any precision below 1/2.
  thompson-f-ramsey-function-iterates-reach-towers: that proves the tower transfer and the fork AMP(D) ⇒ R not elementary; this identifies what AMP(D) says up to elementary overhead, and gives a second proof of the fork.
  coarse-ball-invariance-gives-fine-reiter-measures: that is the group-independent smoothing lemma; this is its consequence for Moore's Ramsey functions of F.
---

**ESTABLISHED** by `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap-proof`. It is a direct proof from
`coarse-ball-invariance-gives-fine-reiter-measures` and the definitions and Proposition 3.1 quoted in
`moore-ramsey-criterion-for-amenability`. It has not been independently reviewed.

**Setting.** `S = {x_0, x_1}`, balls are taken in the word metric of `S ∪ S⁻¹`, and `R = R_{F,S}`, `R̃ = R̃_{F,S}`,
`F(m, ε) = F_{F,S}(m, ε)` are as in Moore's Section 3. All values are in `[0, ∞]`, with `exp_D(∞) = ∞`. Define the
*coarse Reiter radius*

`CR(M) = min{ r : some probability ν supported in B_r has ‖gν − ν‖_{ℓ¹} ≤ 1 for all g ∈ B_M }`.

It is nondecreasing in `M`, and it is finite for all `M` iff `F` is amenable.

**Theorem (sandwich).** For all integers `m, u, M ≥ 1`:
- (a) `R(m) ≤ CR(2m) + m`.
- (b) `R̃(m, 1/u) ≤ F(m, 1/u) ≤ CR(2K) + K + m`, where `K = K_{m,u} = ⌊200 ln 2 · m² · 25^m · u²⌋ + 1`,
  and `2K ≤ exp_3(m+u)`.
- (c) `CR(M) ≤ F(1, 1/M) ≤ R̃(1, 1/(4M), 2) ≤ R̃(R̃(1, 1/(4M)), 1/(4M))`.

**Corollary 1 (coarse control gives AMP).** Say that *CRE(E)* holds if `CR(N) ≤ exp_E(R(exp_E(N)))` for all `N ≥ 1`.
Then CRE(E) implies AMP(E+3).

**Corollary 2 (AMP gives double control).** If AMP(D) holds, then for every `M ≥ 1`

`CR(M) ≤ exp_D(R(exp_D(A_M + 4M)) + 4M)`, where `A_M = exp_D(R(exp_D(4M + 1)) + 4M)`.

**Corollary 3 (the sandwich for the open hole).** Write RGAP₁ for "for every `E` there is `N` with
`CR(N) > exp_E(R(exp_E(N)))`", and RGAP₂ for "for every `D` there is `M` with CR(M) larger than the right side
of Corollary 2". Then

RGAP₂ ⟹ ¬AMP ⟹ RGAP₁,

where ¬AMP is `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead`. Each strict inequality has a
finite right side, so each of the three statements implies that `F` is amenable.

**Why it matters.**
- *Precision is not where the cost is.* Corollary 1 kills every attempt to prove ¬AMP by showing that going from
  error 1/2 to error 1/u is expensive, whether by majority votes, product trials or nested Ramsey sets. For
  *measures*, (b) gives that step at elementary overhead. So ¬AMP is true only if `R` is non-elementarily smaller
  than `CR`, that is, only if "for every coloring `E ⊆ B_n` some `ν` balances it" is far cheaper than "one `ν` is
  coarsely `B_M`-invariant". Here both are at precision 1/2.
- *The dying step is a minimax with too many functions.* To go from Ramsey sets to one measure,
  Towsner's Proposition 3.1 needs `|S|` simultaneous test functions and pays one `R̃`-composition per function.
  Coarse `B_M`-invariance read off directly would need `|B_M| ≈ 5^M` of them, which is a tower of height `5^M`.
  Clause (c) avoids this by going through fine invariance under the two generators. That costs exactly one extra
  composition, and this composition is the whole difference between RGAP₁ and RGAP₂.
- *A second proof of Proposition D (remark, not part of the established statement).* It uses the same
  Følner-convention matching as `thompson-f-ramsey-function-iterates-reach-towers-proof`. By (b) with `m = 1` and Moore–Towsner's `Føl(k) ≤ 5^{F(1,1/k)}`, `CR` is not
  elementary, because `Føl_F` exceeds every tower (`thompson-f-folner-function-exceeds-every-tower`).
  Corollary 2 then forces `R` to be non-elementary under AMP.
- *What is still open.* It is open whether `R_F` is non-elementarily below `CR_F` at all (RGAP₁). If it is not, the
  route `thompson-f-amenable-via-costly-ramsey-amplification` is dead. Moore's hope of an elementary Ramsey radius
  for F is then equivalent to an elementary coarse Reiter radius, which contradicts the Følner tower. So in that case
  it fails outright.
