---
rg: 2
id: thompson-f-ramsey-radii-in-the-elementary-degree-order
kind: claim
title: In Thompson's F, up to bounded towers, the fine Ramsey radius with two or more test functions equals the coarse Reiter radius, the one-function radius sits between the Ramsey radius and the coarse Reiter radius, and RGAP₁ holds exactly when ¬AMP or the second-test-function gap holds
distinct_from:
  thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap: that is the sandwich RGAP₂ ⇒ ¬AMP ⇒ RGAP₁ with explicit windows; this places R, the one-function radius ψ, the l-function radii and CR in one preorder, proves CR ≈ ψ_l for every l ≥ 2, and replaces the double composition of RGAP₂ by the separate hypothesis CR ≼ ψ.
  ramsey-functions-are-pairwise-reiter-radii: that is the pair identity at a fixed window; this uses it only to name ψ as the fine one-pair radius and works modulo bounded towers.
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is ¬AMP, which is open; this proves ¬AMP ⇔ ψ ⋠ R, an equivalence rather than the claim.
  thompson-f-second-test-function-costs-more-than-any-tower: that is the open gap SFG; this proves that SFG is one of the two disjuncts of RGAP₁.
---

**ESTABLISHED** by `thompson-f-ramsey-radii-in-the-elementary-degree-order-proof`. It is a direct deduction from
`thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`, `ramsey-functions-are-pairwise-reiter-radii` and the
definitions quoted in `moore-ramsey-criterion-for-amenability`. It has not been independently reviewed. Clause (1)
is elementary and is probably folklore; the ¬AMP node already quotes the case `l = 1` from Moore's Section 3.

**Setting.** Notation is as in `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`: `S = {x_0, x_1}`,
`R = R_{F,S}`, `R̃ = R̃_{F,S}`, `F(m, ε) = F_{F,S}(m, ε)`, and `CR` is the coarse Reiter radius. Values lie in
`[0, ∞]`, with `exp_E(∞) = ∞` and `φ(∞) = ∞` for every function below. Put

- `ψ(t) = R̃(t, 1/t)`, the fine Ramsey radius with **one** test function (diagonalized);
- `ψ_l(t) = R̃(t, 1/t, l)`, the same with `l` test functions, so `ψ = ψ_1`.

By clause (B) of `ramsey-functions-are-pairwise-reiter-radii`, `ψ(t) = PR_{2/t}(t)` is the fine **one-pair** Reiter
radius: the least `n` such that every pair `α, β ∈ P(B_t)` admits `ν ∈ N_{t,n}` with `‖αν − βν‖₁ < 2/t`.

**The elementary degree order.** For nondecreasing `φ, χ : ℕ_{≥1} → [0, ∞]`, write `φ ≼ χ` if some `E` has
`φ(x) ≤ exp_E(χ(exp_E(x)))` for all `x ≥ 1`. Write `φ ≈ χ` if `φ ≼ χ` and `χ ≼ φ`, and `φ ⋠ χ` for the negation of
`φ ≼ χ`. The relation `≼` is reflexive and transitive.

**Theorem.**
1. **(l-collapse, every group.)** `R̃(m, ε, l) ≤ F(m, ε)` for all `m, l ≥ 1` and `ε > 0`.
2. **(Two test functions are coarse Reiter.)** For all `M ≥ 1` and `l ≥ 2`,
   `CR(M) ≤ R̃(1, 1/(4M), 2) ≤ R̃(1, 1/(4M), l) ≤ CR(2K) + K + 1`, with `K = K_{1,4M} ≤ 55453 M²`.
   Hence `ψ_l ≈ CR` for every `l ≥ 2`.
3. **(The chain.)** `R ≼ ψ ≼ CR ≼ ψ∘ψ`. Concretely, `R(t) ≤ ψ(2t)`, `ψ(t) ≤ exp_4(CR(exp_4(t)))` and
   `CR(M) ≤ ψ(ψ(4M))` for all `t, M ≥ 1`.
4. **(Dictionary.)**
   - AMP(D) for some `D` ⇔ `ψ ≼ R`. So ¬AMP ⇔ `ψ ⋠ R`.
   - CRE(E) for some `E` ⇔ `CR ≼ R`. So RGAP₁ ⇔ `CR ⋠ R`.
   - If AMP(D) holds, then `CR ≼ ψ∘ψ` gives `CR(M) ≤ exp_{D+1}(R(exp_{2D+2}(R(exp_{D+3}(M)))))` for all
     `M ≥ 1`. This is a double composition of the same shape as Corollary 2 of the sandwich.
5. **(The split.)** Put SFC ("second function cheap") for `CR ≼ ψ`, and SFG for its negation `CR ⋠ ψ`. Then
   - RGAP₁ ⇔ ¬AMP ∨ SFG;
   - RGAP₁ ∧ SFC ⇒ ¬AMP;
   - SFG ⇒ RGAP₁, and SFG implies that `F` is amenable;
   - SFC ⇔ `ψ ≈ CR` ⇔ `ψ ≈ ψ_2`.
   - SFC holds vacuously when `F` is not amenable.
   - With the same definitions in any infinite finitely generated group, SFC holds whenever the coarse Reiter
     radius is bounded by a fixed tower. So SFG, like ¬AMP, can hold only where `CR` is non-elementary.

**What it does to RGAP₂.** RGAP₂ carries a second composition of `R`. Clause (2) and clause (5) locate that
composition exactly: it is the cost of the second test function, `ψ_2` against `ψ_1`. RGAP₂ may therefore be
traded for RGAP₁ together with SFC, a statement about fine Ramsey radii that does not mention `R`. SFC can fail
on its own (that is SFG), and RGAP₁ can fail on its own (that is CRE).

**What it does to the root.** RGAP₁ already implies amenability (Corollary 3 of the sandwich). By (5) it is
exactly the disjunction of two statements, each of which implies amenability:
- ¬AMP, one-pair precision amplification is expensive, `ψ ⋠ R`;
- SFG, the second test function is expensive, `CR ⋠ ψ`.

A proof of either suffices for `thompson-f-is-amenable`. A refutation of RGAP₁ (CRE) kills both at once, and with
them RGAP₂ and the route `thompson-f-amenable-via-costly-ramsey-amplification`.

**In pair language.** By clause (B) of the pair identity, the chain reads `R ≼ PR_1 ≼ PR_{2/t}(t) ≼ CR`.
- ¬AMP says the gap `R ≺ CR` occurs below the fine one-pair radius.
- SFG says it occurs above: "every single pair of measures on `B_t` can be brought within `2/t`" is reached
  non-elementarily earlier than "one measure is moved by at most 1 by all of `B_M`".
- `SFG ⇒ PGAP_1` holds because `PR_1(t) ≤ ψ(t)` for `t ≥ 2`. So SFG is the vanishing-threshold strengthening of
  PGAP_1.
