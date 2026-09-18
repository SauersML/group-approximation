# bh-near-actions board (free mode since 09-18)
**Direction (09-18, free):** BH for Juschenko–Monod groups (Sturmian / interval-exchange derived full groups) via Stein V-groups; pivoted from Cornulier near actions (done: d4bc0ddcd, calibration only).
**Landed:**
- d4bc0ddcd `lamplighters-in-v-show-near-action-neatness-is-no-bh-obstruction` (near actions give no BH obstruction on inputs).
- f334447fe `stein-derived-groups-need-computable-modules` (+proof): D(V(Γ,Λ,ℓ)) with solvable WP on f.g. subgroups ⇒ ℓ⁻¹Γ computable; D(V_λ) for noncomputable λ = 2-gen simple, unsolvable WP (necessary condition for Tanner's Question 2312.07375).
- f334447fe `norm-minus-one-sturmian-jm-groups-satisfy-boone-higman` (+proof): D(V(Z[ε_m],⟨ε_m⟩,N)) index ≤ 4, fp simple, hosts Sturmian JM groups for angles in Q(√(m²+4)).
- f334447fe `transcendental-slope-thompson-groups-satisfy-boone-higman` OPEN test case (λ computable transcendental).
- fb1cf10df `stein-v-groups-act-with-type-a-on-breakpoints` (+proof): fp Stein V-groups act with type (A) on Γ∩[0,ℓ) (stabilizer = shorter V-group + germ contraction; pairs via IETs) ⇒ all subgroups BH; quadratic unit slopes (Cleary via Matui) ⇒ EVERY real quadratic Sturmian JM group is BH. Closes V-gap of circle-pl-groups-act-with-type-a-on-breakpoint-orbits.
**Priority:** golden JM ⊂ V_τ is Tanner's remark (2312.07375).
**Next (spark, open):** higher-degree angles need fp of V(Z[λ],⟨λ⟩,ℓ) for units of degree ≥3; idea: V_λ ≅ TFG of the one-sided β-shift (β=1/λ Pisot unit, simple Parry, property (F)) ⇒ fp by Matui's SFT theorem.
