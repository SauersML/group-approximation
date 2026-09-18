# Referee report (gq-referee-a, proof-gap lens): resolvent elementary groups are not finitely presented

**Reviewed:** `resolvent-elementary-groups-are-not-fp` and its `-proof` (lane gq-k2-q, e27bd0bd3), read on origin/main
(db7acc3f9).

**Verdict: PASS.** Steps 1–5 hold, given `resolvent-ring-corner-symbols-survive-in-k2`, which passes in my second
review, and the symbol lemma. There are two nits.

## Checks
- **The input actually used from the symbol lemma.** Step 2 uses only the first assertion of part 1 of
  `infinitely-generated-symbols-block-fp-elementary-groups`: if `E_N(R)` is finitely presented, then
  `ι(K_2(N,R)) ⊆ K_2(R)` is finitely generated.
  - It does not use "contains `Sym(R)`". That matters, because the corner symbols are not symbols of commuting units
    of `R_l`: `θ(λ)` is a unit of `eR_le`, not of `R_l`.
  - The route is written this way, correctly.
- **Step 3.** `c(λ,μ) = St_N(θ)({λ,μ}_N)` lies in `K_2(N,R_l)`, and `ι(c(λ,μ)) = θ_*{λ,μ}`. These generate a subgroup
  that is not finitely generated. Both facts are in the corner-symbols node, and I checked them in the second
  review. ✓
- **Step 4.** Subgroups of finitely generated abelian groups are finitely generated. ✓
- **Step 5.** In `1 → C → E_N → E_N/C → 1` with `C` finite, a finitely presented `E_N/C` would make `E_N` finitely
  presented (P. Hall). ✓

## Nits
- **N1 (step 1).** "`R_l` is a finitely generated ring, so the symbol lemma applies" can drop the hypothesis. The
  lemma holds for every unital ring.
- **N2 (step 2).** Say explicitly that only the finite-generation half of part 1 is used, for the reason above.
