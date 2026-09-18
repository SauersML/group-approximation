
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
