
## bh-pal-scope recommended theorem list (09-18, research/artifacts/gq-bh-pal-scope.md, 59be3f175)
Tier 1 (put in the challenge now):
- T1 `explicit_fp_overgroup_of_all_gl_n_q`: Kourovka 14.10(c) / BBMZ 2.7. St_10(R_L) is f.p. and every GL_n(Q) injects (inline R_L := RingQuot of FreeAlgebra ℤ (Fin 6), SteinbergGroup := PresentedGroup).
- T2 `fp_metabelian_embeds`, `fg_metabelian_embeds`: BBMZ 5.3(7) and BHM l.272. Reuse the metabelian pair verbatim.
- T3 `fg_linear_embeds`: every f.g. subgroup of GL (Fin n) K, any field K (T3 of Statement/Basic.lean, verbatim).
- T4 `exists_fp_infinite_simple`: lean-eval higman_infinite_simple form. A formalization first; the math is Hyde–Lodha's.
- T5 `kourovka_17_59`: CT(Z) = RCWA⁺(Z) (inline class transpositions and RCWA⁺, ~40 lines).
Tier 2 (add the statements now as WIP, prove later):
- T6: exceptional spherical Artin E_6–E_8, F_4, H_3, H_4 (CoxeterMatrix literals).
- T7: BFFHZ Q3.1, graph products of PBH groups are PBH (inline type (A) and graph product).
- T8: Kourovka 17.61, CT_P(Z) simple and f.p. for finite P.
Excluded by the scope rule: B̃/C̃ Artin, forest Artin, BS(1,3) ≤ 3V, the Juschenko–Monod group in 2V, surface-by-free, ascending HNN of free groups, Lodha S/circle-PL type (A) instances, 17.60 partial, Kac–Moody PBH.
- Also excluded (bh-free-03, no printed question found): substitution-subshift full groups (d51ff3576), quadratic-rotation IET groups (05eb153bc), product-substitution full groups and quadratic rectangle exchanges (37306810d). Revisit only if a printed source turns up.

## bh-pal-kourovka59 (09-18): T5 (Kourovka 17.59) is NOT Lean-ready
- The answer on main (`ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers`) still rests on
  `ct-p-z-is-a-one-vertex-k-graph-full-group` item 3, i.e. on the groupoid generation theorem
  (Matui/Li). The elementary replacement is OPEN: `piecewise-canonical-permutations-are-transposition-products`
  (18ebf78dc) proves two lemmas and states the exact remaining gap.
- So do NOT put T5 in the megachallenge as an elementary result of ours yet. Either leave it out,
  or state it with the groupoid inputs as explicit hypotheses and label them.
- The same coherence gap blocks T8 (Kourovka 17.61 via a finite presentation), per
  `class-transposition-relations-present-ct-p-z` Attempts.

## bh-pal-surface status (09-18 ~09:50, lane)
Direction: Palomar BH megasurface: challenge + solution skeleton + model tests + config + drivers + gate + yaml (WIP).
- Challenge theorems (namespace BooneHigman): explicit_fp_overgroup_of_all_gl_n_q (T1), finitely_presented_/finitely_generated_metabelian_embeds_in_finitely_presented_simple (T2), finitely_generated_linear_embeds_in_finitely_presented_simple (T3), finitely_generated_linear_embeds_in_finitely_presented_self_similar (LISW Q1.11), exists_finitely_presented_infinite_simple (T4, PROVED outright from Hyde–Lodha Q₂ closed theorem), kourovka_17_59 (T5, owed statement kept as an explicit hypothesis per bh-pal-kourovka59), exists_fp_simple_with_mixed_identities_not_finitely_normally_generated (BFFHZ Q3.3).
- Solution `_of` hypotheses: T2/T3 take GroupApproximation.BooneHigman.Finitely{Generated{Metabelian,Linear}}Statement; others take named Owed props. Swap to bh-pal-wire's FrontierFour `_of` forms when it lands.
- Deferred (docstring only): T6–T8, Kourovka 17.60, Zaremsky Oberwolfach Q110.
- Gate: BH + metabelian configs in PALOMAR_PENDING_CONFIGS; METADATA = BH (pending); new rule: no main_results row for a pending config; calibrations updated (55 pass on MSI with conda python3).
