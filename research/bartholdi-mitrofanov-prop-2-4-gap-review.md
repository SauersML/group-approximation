---
rg: 2
id: bartholdi-mitrofanov-prop-2-4-gap-review
kind: claim
title: Referee review of the Bartholdi–Mitrofanov Proposition 2.4 question (8a7ca6bacd, f0e160599c, 3e2cc67b22) — the gap is real; read in the arXiv LaTeX of v1 and v4, [g,u] ≠ 1 for EVERY Minsky machine, so Prop 2.4 and the printed proofs of Theorems A and A″ fail; bh-birget's partner p (supported on 0*1A^ω) repairs both directions and restores A″; the survival lemma and (c) for G_1 and G′_1 hold, but 3e2cc67b22's "s_† is finitary" misreads a §3 rule, so the loop image is D_12, not Z/2
distinct_from:
  birget-question-via-decidable-bartholdi-mitrofanov-hosts: that is the lane node; this checks its Prop 2.4 gap note, its repair Prop 2.4′, the survival lemma and the tests on (c).
  finite-recursion-gives-no-computable-depth-bound: that imports Theorem A″; this says A″ as printed has a gap and is restored by the repair.
---

**ESTABLISHED (referee bh-ref-f, 2026-09-19).** No code was run. The arXiv LaTeX sources of 1710.10109v1 and
v4 were fetched to MSI (`refs/bm1710/`) and read there with sed and grep. The v1 and v4 texts of §2.1 and of
Proposition 2.4 agree. The published version (Groups Geom. Dyn., 2020) is paywalled and was **not** checked for
an erratum.

## 1. The rules, verbatim from the v4 LaTeX (§2.1)

- **Default:** "Whenever a value of Φ_M is unspecified, we take it to mean Φ_M(a,s)=(s,a)."
- **The listed rules:** Φ(0,s_†)=(ε,†₁); Φ(†₁,s_†)=(ε,0); Φ(†₂,s_†)=(ε,†₂); Φ(†ᵢ,x)=(ε,†ᵢ); Φ(†ᵢ,y)=(ε,†ᵢ);
  Φ(†₁,t)=(ε,†₂); Φ(†₂,t)=(ε,†₁); Φ(0,u)=(u,1); Φ(1,u)=(u,0).
- **Walls:** "for all g∈S∖{u} we put Φ_M(1,g)=(ϵ,1), and for all a∈A∖{0,1} we put Φ_M(a,u)=(ϵ,a)."
- **No marker rule for the states.** No rule is given for any machine state (s_i, a_i or b_i) at †₁ or †₂. By the
  default, they pass the markers with themselves as section. The paper's own dual Moore diagram (Figure 1) shows
  exactly this: it has no state edge at †₁ or †₂ other than those of s_†, t, x and y.
- **The proof of Prop. 2.4, verbatim:** "The element u acts on A^ω as follows: it scans X∈A^ω for its longest
  prefix in {0,1}*, and exchanges all 0 and 1 in that prefix. … Assume first that M does not halt; then g in fact
  also fixes {0,1}^∞, so the supports of g and u are disjoint and [g,u]=1 in ⟨Φ_M⟩."
- **Convention:** the action is on the right, "(a₁…aₙ)^g = a₁′(a₂…aₙ)^{g′}", and "a·g = g′·a′" means
  Φ(a,g) = (g′,a′).

## 2. The gap: [g,u] ≠ 1 for every machine

Put g = h t h⁻¹ with h = s_* x y. There are two cases.

- **Case 1: the first instruction from s_* has type I.** Then 0·h = s_j x² y·𝐢₁ (from the paper's (2.1)).
  - For X = 0 †₁ w:
    - h takes 0 to 𝐢₁ with section s_j x² y;
    - that section passes †₁ as s_j, since x and y give ε there;
    - t passes 𝐢₁ and turns †₁ into †₂;
    - the paper's reverse identity 𝐢₁·(s_*xy)⁻¹ = (s_jx²y)⁻¹·0 restores 0, and (s_jx²y)⁻¹ passes †₂ as s_j⁻¹.
  - So X^g = 0 †₂ w.
  - Also X^u = 1 †₁ w. Every word in S ∖ {u} fixes words beginning with 1, so (1†₁w)^g = 1†₁w, while
    (0†₂w)^u = 1†₂w.
  - Hence X^{gu} = 1†₂w ≠ 1†₁w = X^{ug}.
- **Case 2: the first instruction has type IX or VI, or the machine halts at once.**
  - Types IX and VI: the section of g at 0 is again h′ t h′⁻¹, where h′ is a word in states and x, y. All states
    pass †₁ and x, y stop there, so the section maps †₁ to †₂.
  - Halting at once (s_* = s_†): X^g = †₂†₁w, while X^{ug} = 1†₁w.
  - Either way g and u do not commute.
- **The error.** The support of u is the open set of words beginning with 0 or 1, not {0,1}^∞. So "g fixes
  {0,1}^∞" does not give disjoint supports.
- **What fails, and what is unaffected.**
  - The non-halting half of Prop. 2.4 is false for every non-halting M.
  - The printed proofs of Theorem A and Theorem A″ fail with it: every test word [g_n,u] is nontrivial, so the set
    of trivial ones is recursive.
  - Prop. 2.3, and with it the fixed-ray Theorem A′, is unaffected.
  - §3 (the order problem for automata groups) uses a different construction and was not checked here.
- **No misreading on our side.** The claim does not depend on how the states treat the markers. It needs only
  that t reaches the first † after the trace, which the halting direction already requires. This confirms
  bh-birget's computation (8a7ca6bacd, f0e160599c).

## 3. The repair Prop. 2.4′ (3e2cc67b22): PASS

The repair replaces u by p, where Φ(0,p)=(p,0), Φ(1,p)=(p′,1) and Φ(a,p)=(ε,a) otherwise, and p′ flips 0↔1 with
trivial section.
- **p is well defined.**
  - p is finite-state, with states {p, p′, 1}.
  - p and p′ are involutions.
  - supp(p) ⊆ 0*1A^ω.
  - u occurs in no other section of BM's table, and §2.2 says u is used only in Prop. 2.4. So Prop. 2.3 is
    unchanged, and so is the rest of the construction.
- **Non-halting ⇒ [g,p] = 1: correct.**
  - Every section of g is a word in S ∖ {u}, since no generator other than u has u as a section.
  - Such words fix the letter 1 with trivial section.
  - When M never halts, g fixes every 0^m (Prop. 2.3). So g fixes 0*1A^ω pointwise.
  - supp(g) and supp(p) are then disjoint and invariant, so g and p commute.
- **Halting ⇒ [g,p] ≠ 1: correct.**
  - The paper's computation gives (0^{K+1}Y)^g = 0^K†₂Y, with trivial section after the †₂.
  - For X = 0^m10Z with m ≥ K+1: p fixes X^g, whose first non-0 letter is †₂, while (X^p)^g = 0^K†₂0^{m−K−1}11Z.
- **A″ transfers.**
  - The family ⟨Φ_M, p, p′⟩ is functionally recursive, and faithful on the regular tree A*.
  - For the universal machine, the set of words [g_n,p] is recursive, but its subset of trivial words is not.
  - So Theorem A″ holds for the repaired table.

## 4. The survival lemma and (c) for the increment loop: PASS with one correction

- **The lemma is correct.** In a self-or-trivial recursion, a section of w at z is the subword of letters that
  survive at z.
  - If at every z some letter dies, all first-level sections are shorter. Use induction on free length, with M
    normal to handle cyclic reduction, and then lift closure.
  - If at some z nothing dies, w labels a closed path of the survival graph Σ, so w lies in π₁(Σ,z) ∩ N ⊆ ⟨⟨R⟩⟩.
  - The weighted version also holds: p weighs 2 and every other generator 1; weight strictly drops unless every
    letter survives unchanged.
- **Correction: s_† is not finitary.** 3e2cc67b22's quoted rule "for all a∈A we have Φ_M(a,s_†)=(ϵ,a)" is at line
  1252 of the v4 source. It sits inside the §3 construction for the order problem, not in §2.1.
  - In §2.1, s_† at 𝐢₁ is unspecified, so b = s_† = (0 †₁)(1,1,1,1,b), and b loops at 𝐢₁ in Σ.
  - f0e160599c had this right: the loop image at 𝐢₁ is ⟨t,b⟩ ≅ D₁₂, checked in e733763d78.
  - The image at 0 is α⟨t,b⟩α⁻¹, using [α,t] = 1, checked here: α never changes a marker, and t never changes a
    digit.
  - The image at † is ⟨α⟩ ≅ Z.
- **(c) holds for G_1**, with R made of t², u², b², (bt)⁶ and [α,t] (conjugated as needed). This agrees with
  f0e160599c.
- **(c) holds for G′_1 = ⟨α,b,t,p,p′⟩** as well, but the loop image at 0 is ⟨p⟩ × α⟨t,b⟩α⁻¹ ≅ Z/2 × D₁₂, not
  (Z/2)².
  - p commutes with αbα⁻¹, because their supports are disjoint: supp(αbα⁻¹) = {0^k𝐢₁W, 0^k†₁W} and
    supp(p) ⊆ 0*1A^ω.
  - Add b², (bt)⁶ and [p, αbα⁻¹] to R.
  - The conclusion stands.

## 5. Nodes on main that depend on A″ or Prop. 2.4

**Load-bearing: survive with the repaired table, and should cite this review.**
- `finite-recursion-gives-no-computable-depth-bound` (e6f7e2b3d7) and its review (14b9c876b6). It needs only some
  faithful functionally recursive group with non-recursive word problem.
- `nonrecursive-a2-kernel-from-abstract-rover-nekrashevych-groups`, `some-a2-action-has-a-nonrecursive-kernel`,
  and the recursion used at line 87 of `abstract-rover-nekrashevych-groups-are-finitely-presented`. They need the
  repaired table, in which the recursion includes p and p′.
- `birget-question-via-decidable-bartholdi-mitrofanov-hosts`:
  - item (a) now uses G′_M;
  - Test 3 needs A″, which holds for the repaired table;
  - the reviews 03514e0598 and ab22b01462 were written before the gap was found.

**Citation only, unaffected.**
- `computable-tree-groups-embed-in-{decidable-fg,fp}-self-similar-groups` quote the abstract. It remains true via
  the repair.
- `kourovka-15-19a-some-grigorchuk-groups-are-not-finite-state` cites it only in `distinct_from`.
- `self-similar-higman-routes-meet-krull-dimension-two` only mentions it.
- `local-boone-higman-conjecture` uses Theorems B2 and C, which rest on the separate §3 construction and are not
  affected by this gap.

## 6. Attribution

- The gap and the repair partner p are bh-birget's.
- This review confirms both from the LaTeX source, identifies the source of the "s_† finitary" misreading, and
  lists the dependents.
- It would be worth asking the authors whether the published version corrects this. That is the user's decision,
  since it means contacting them.
