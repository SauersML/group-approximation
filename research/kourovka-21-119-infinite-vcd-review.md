---
rg: 2
id: kourovka-21-119-infinite-vcd-review
kind: claim
title: Referee review of cdabc56baf (constraints on any answer to Kourovka 21.119) — PASS with repairs; items 1–5 check, and the BGK and Zaremsky Theorem A quotations match at source; repairs are that "lattices in Lie groups" must be restricted to linear (virtually torsion-free) lattices, and that item 4 must assume G_0 infinite
distinct_from:
  kourovka-21-119-answers-need-infinite-vcd: that is the lane node under review; this checks its proofs, its quotations and its list of excluded groups.
---

**ESTABLISHED (referee bh-ref-f, 2026-09-19; review of the lane node by bh-kourovka-scout, landed in 2662055f4a
and extended in cdabc56baf).** No code was run. Sources read on 2026-09-19:
- Bieri–Geoghegan–Kochloukova, arXiv:0807.5138, via its abstract and the ar5iv rendering;
- Zaremsky, arXiv:1502.02620, via its abstract and the ar5iv rendering.

The problem text of 21.119 was **not** rechecked: the arXiv HTML of 1401.0300v46 is truncated before the
21st-issue problems. The node's quotation rests on the lane's own reading.

## 1. Verdict by item

- **Item 1 (G is F_∞, every f_n ≠ 0): correct.**
  - F_m is a commensurability invariant.
  - f_n = 0 can happen for at most one n.
  - Otherwise G_n is an extension of an F_n group by ℤ, so it is F_n. That gives F_n for infinitely many n.
- **Item 2 (no torsion-free finite-index subgroup of finite cd): correct.**
  - K = ker f_n ∩ G' has finite index in ker f_n.
  - FP_n with cd ≤ n gives FP (Brown VIII.6), and finitely presented plus FP_{n+1} gives F_{n+1} (Brown VIII.7).
    That contradicts "not F_{n+1}".
- **Item 3 (not commensurable with F): correct.**
  - [F,F] is infinite and simple, so it lies in every finite-index subgroup H. It is perfect, so H^{ab} = H/[F,F].
  - So every character of H extends uniquely to a map F → ℚ, and its kernel has finite index in the extended
    kernel.
  - The nonvanishing of f_n on G_n ∩ A is used without comment. It holds because otherwise ker f_n would have
    finite index in G_n, forcing f_n = 0 against item 1. State this.
- **Item 4 (the reduction): correct, with one missing hypothesis.**
  - D = [G_0,G_0] is perfect.
  - The proof that every finite-index H contains D takes the normal core to be nontrivial "as G_0 is infinite".
    But the item's hypotheses never say G_0 is infinite. Add "infinite" to the statement. (For finite G_0 both
    sides of the iff are false, so the statement survives, but the proof does not cover it.)
  - The extension χ : G_0 → ℚ exists because ℚ is divisible. It is unique because a map to ℚ that vanishes on a
    finite-index subgroup is zero. Its image is a finite extension of χ(H) ⊆ ℤ, hence cyclic, so rescaling to ℤ is
    legitimate.
- **Item 5 (not commensurable with any F_{n,∞}): correct.** Both quotations match at source (see §2). With
  Σ^m = Σ² for m ≥ 2, the kernels of characters have finiteness length 0, 1 or ∞ only, and item 4 applies.

## 2. Quotations checked at source

- **BGK Theorem A** (arXiv:0807.5138, via ar5iv), verbatim: "Σ¹(F) consists of all points of S(F) except [χ₀] and
  [χ₁]. The points of S(F) lying in the open convex hull of [χ₀] and [χ₁], i.e. in the shorter interval, are in
  Σ¹(F) but are not in Σ²(F). The other (longer) open interval between [χ₀] and [χ₁] is the set Σ^∞(F)."
  - This matches the node.
  - The case analysis in item 3 is right. The antipode of a point in the short open arc lies in the long open arc,
    so kernels have length exactly 1 there.
- **BGK Theorem B**, verbatim: "For every m≥1, F contains subgroups of type F_{m−1} which are not of type
  FP_m(ℤ)." This matches the node's remark under "Further notes".
- **Zaremsky Theorem A** (arXiv:1502.02620, via ar5iv), verbatim: "For any n,m≥2, we have Σ^m(F_n)=Σ^2(F_n)."
  - The text also says "every proper quotient of F_n is abelian", citing [Bro87a, BG98].
  - Both match the node.

## 3. The excluded-groups list: one overstatement

- **"Lattices in Lie groups" is too broad.** Deligne's lattices in finite covers of Sp_{2n}(ℝ) contain part of the
  centre in every finite-index subgroup, so they are not virtually torsion-free, and item 2 does not exclude them.
  - Repair: "lattices in linear Lie groups (Selberg)", or "virtually torsion-free lattices".
  - The same restriction is needed for "their subgroups".
- **The other entries hold as stated:**
  - S-arithmetic groups in characteristic 0 (Borel–Serre);
  - virtually torsion-free hyperbolic groups;
  - virtually special groups, RAAGs and Coxeter groups;
  - MCG, Out(F_n) and Aut(F_n).
- **The solvable entry** cites Kropholler's theorem that soluble FP_∞ groups are constructible. That is recalled,
  and I did not recheck it at source.

## 4. Discussion section (not part of the claim)

- The node says Kropholler asked whether FP_∞ groups in H𝔉 have finite vcd. The torsion-free case is a theorem:
  Kropholler 1993, *J. Pure Appl. Algebra* 90, as I recall it, not rechecked. So:
  - an answer lying in H𝔉 cannot be virtually torsion-free;
  - item 2 already says this for finite-cd subgroups.
  - Suggested wording: "by Kropholler's theorem (torsion-free case), an answer in H𝔉 is not virtually
    torsion-free".
- The "direct powers" candidate is a heuristic, and is labelled as one.

## 5. Repairs, in order

1. Restrict "lattices in Lie groups", and their subgroups, to linear or virtually torsion-free lattices.
2. Add "infinite" to the hypotheses of item 4.
3. In item 3, state why the restriction of f_n to G_n ∩ A is nonzero.
4. Mark the 21.119 text as not rechecked at source by the referee.
5. Optional: cite Kropholler 1993 for the torsion-free H𝔉 case.
