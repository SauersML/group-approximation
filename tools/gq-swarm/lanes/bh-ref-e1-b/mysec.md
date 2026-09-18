## Referee (bh-ref-e1-b, 2026-09-18): composition PASS; SFT-lift premise PASS conditional on repair G1

Independent referee 1 of 2, for the SFT-lift half and the composition. The (D) premise and the tree
gluing are refereed separately (bh-ref-e1-a).

**Interfaces, checked step by step.**
- **Clapham → storage column.** `A = Λ_1 x Z` is finitely generated and finitely presented, has
  solvable word problem, is infinite, and contains `K`.
- **(D) → gluing.** The gluing node needs `A` finitely generated with solvable word problem, and a
  nonempty free subshift over a *finite* alphabet with decidable language. The (D) node supplies
  exactly this, after the inversion map `y ↦ y∘inv` that the route records.
- **Gluing → lift.** The gluing output is a nonempty minimal free subshift of `Γ = A * Z` with
  *decidable language*, so its forbidden patterns are recursively enumerable and it is effectively
  closed. `Γ` is finitely generated with solvable word problem (normal forms).
  - The same inversion map is needed here too, because the gluing node uses `(λ·z)(μ) = z(μλ)` and
    the lift uses the left action. The route mentions it only at step 2.
  - The map conjugates the actions (with `y(h) = z(h^{-1})`, `λ·z` goes to `λ·y`), so it preserves
    minimality and freeness. Effective closedness is preserved because `F ↦ F^{-1}` is computable.
  - Cosmetic: add the sentence at step 3.
- **Lift → target.** `Λ = (A * Z) x Z^2` is finitely presented, infinite, contains `K`, and
  carries a nonempty minimal SFT on which all of `Λ` acts freely. That is exactly
  `decidable-groups-embed-in-fp-groups-with-minimal-free-sft` for `K`.
- **Consistency with necessity.**
  - Jeandel: `Λ` has solvable word problem.
  - Cohen: `Λ` is one-ended.
  - No known obstruction is violated.

**Status of the lift premise.** PASS at design level, conditional on repair G1 recorded on
`keyed-diversification-slots-give-plane-constant-minimal-lifts`. Slot keys must be the full input
field `(τ_K, τ_K^{(s)}, τ_{K+1})`, not `τ_K` alone. This is a local change, with an adjusted growth
condition.

**Verdict.** If the (D) and gluing premises pass their own review, and G1 is written in, this route
establishes gate E1 (P1). Credit is due to Clapham (1967), to Durand–Romashchenko(–Shen) for the
fixed-point and slot machinery, and to Jeandel and Cohen for the necessity checks.
