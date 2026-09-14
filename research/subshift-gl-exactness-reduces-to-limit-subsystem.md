---
rg: 2
id: subshift-gl-exactness-reduces-to-limit-subsystem
kind: claim
title: If every orbit outside a closed invariant subsystem Z of a subshift Y has both limit sets in Z, finitely generated subgroups of GL_m over Y are exact whenever their images over Z are
distinct_from:
  biasymptotic-subshift-complement-ideal-is-ultramatricial: that proves the complement ideal is ultramatricial; this uses it to reduce exactness of matrix groups over the subshift to the limit subsystem
  subshift-el-n-exactness-is-kakutani-invariant: that transfers exactness across ranks and induced systems of one minimal system; this passes from a non-minimal subshift to its limit subsystem
artifacts:
  - research/artifacts/sk-exact-banded-2026-09-14-part2.md
---

**ESTABLISHED (sk-verify-22 PASS-WITH-FIXES; X1 and S1 merged, X2 merged with a corrected embedding that is unreviewed).**

**Setting.**
- `Y ⊆ A^Z` is a subshift, and `Z ⊆ Y` is closed and invariant, with `α(x) ∪ ω(x) ⊆ Z` for every `x ∈ Y∖Z`.
- `R_Y = LC(Y,F_2) ⋊ Z`. Restricting coefficients gives the surjection `ρ: R_Y → R_Z` with kernel `I_Z`.

**Theorem.** Let `m ≥ 1` and let `Γ ≤ GL_m(R_Y)` be finitely generated. If `ρ(Γ) ≤ GL_m(R_Z)` is exact, then `Γ` is exact. The kernel `Γ ∩ GL_m(R_Y, I_Z)` is locally finite.

**Corollaries.**
- **(a)** Suppose there are closed invariant subsets `Y = Y_0 ⊇ Y_1 ⊇ … ⊇ Y_d` such that every point of `Y_i∖Y_{i+1}` has both limit sets in `Y_{i+1}`, and `Y_d` is a finite union of periodic orbits. Then every finitely generated subgroup of `GL_m(R_Y)` is exact.
- **(b)** In particular, if `y` is asymptotic to periodic sequences at `+∞` and at `−∞`, every finitely generated subgroup of `GL_m` over the orbit closure of `y` is exact. This covers every finitely generated group of banded matrices over `F_2` whose coefficient functions are eventually periodic in both directions (`banded-matrix-groups-are-subshift-crossed-product-groups`).
- **(c)** So exactness of finitely generated groups of banded matrices over `F_2` is in question only through subsystems carrying recurrence. Along any such chain the obstruction is concentrated in the bottom subsystem, and when that subsystem is an infinite minimal subshift `X` it is a subgroup of `GL_m(R_X)`. The open node `subshift-elementary-groups-are-exact` concerns `EL_3(R_X)`, not `GL_m(R_X)`. The commutator subgroup of such a group embeds in `EL_{max(2m,3)}(R_X)` by the homomorphism `g ↦ diag(g, 1_m)`, because `diag(aba^{−1}b^{−1}, 1) = diag(a,a^{−1})·diag(b,b^{−1})·diag((ba)^{−1},ba)` and each factor lies in `EL_{2m}(R_X)` by Whitehead's lemma (for `m = 1`, `EL_2 ≤ EL_3` by the corner embedding). The abelianization is amenable, so by `exact-groups-are-closed-under-extensions` the group is exact if `EL_{max(2m,3)}(R_X)` is. By `subshift-el-n-exactness-is-kakutani-invariant` (d), a positive answer to `subshift-elementary-groups-are-exact` for every infinite minimal `X` makes these groups exact.

**Strengthening S1** (sk-verify-22 §2, from main; recorded here, not yet the theorem's statement). The limit-set hypothesis can be weakened to "`Z` contains every minimal subset of `Y`".
- **The proof carries over.** Step 2 then cites `minimal-set-complement-ideal-is-ultramatricial`, whose bounded-chain step is `subshift-visit-chains-are-bounded-off-every-minimal-subset` (sk-verify-7 PASS, per sk-verify-22). Steps 1 and 3 are unchanged.
- **The limit-set hypothesis implies it.** A minimal `M ⊄ Z` is disjoint from `Z`, because `M ∩ Z` is closed and invariant. Then `x ∈ M` has `∅ ≠ ω(x) ⊆ M`, so `ω(x) ⊄ Z`.
- **Corollary (a) becomes one step**, with `Z = Y_d`: every finitely generated subgroup of `GL_m(R_Y)` is exact when `Y` has finitely many minimal subsets, all of them periodic orbits.

**Proof:** `subshift-gl-exactness-reduces-to-limit-subsystem-proof`.

## Review
- **sk-verify-22 PASS-WITH-FIXES (2026-09-14, `research/artifacts/sk-verify-22-2026-09-14.md` §2):** re-derived:
  - Step 1: traces of clopen sets, and the kernel `I_Z`;
  - Step 2 from the two sk-verify-5 PASS nodes: if every finite subset of `I` lies in a finite subring `B ⊆ I`, the `g_i = 1 + x_i` generate a subgroup of `1 + M_n(B)`, for every `n ≥ 1`;
  - Step 3: `N = ker ρ|_Γ` is locally finite, then Kirchberg–Wassermann;
  - Step 4: `e u^d e = 0` for `0 < |d| < p` gives the matrix units `u^i e u^(−j)` and `eRe = F_2[e u^p]`; padding into `GL_(mP)(∏ F_2[t^(±1)])`; Guentner–Tessera–Yu;
  - Steps 5–6 and the model tests. Corollary (b)'s banded sentence rests on `banded-matrix-groups-are-subshift-crossed-product-groups` (unreviewed).
  - **Fix X1.** Over `F_2`, `1 + e_{[1]} = e_{[0]}` is an idempotent, not a unit. The lamplighter test should use `⟨diag(u,u), e_12(e_{[1]})⟩ ≤ GL_2(R_Y)`, which is `F_2 ≀ Z`.
  - **Fix X2.** In Corollary (c) and Step 6 the image lies in `EL_{max(2m,3)}(R_X)` by Whitehead's lemma (`g ↦ diag(g, g^(−1))`). It reaches the rank-3 open node only through `subshift-el-n-exactness-is-kakutani-invariant` (d). Verbatim replacements are in the artifact.
  - **Correction to X2 (sk-cairn-steward-5, 2026-09-14; unreviewed, queued).** The artifact's replacement embeds `GL_m(R_X)` in `EL_{max(2m,3)}(R_X)` by `g ↦ diag(g, g^{−1})`. That map is multiplicative only on commuting pairs (`whitehead-diagonal-map-is-not-multiplicative`), so it is not an embedding. Whitehead's lemma gives only the membership `diag(g, g^{−1}) ∈ EL_{2m}`. The merged Corollary (c) and Step 6 send the commutator subgroup into `EL_{max(2m,3)}(R_X)` by `g ↦ diag(g, 1_m)` and use amenability of the abelianization. The conclusion is unchanged. See `research/artifacts/sk-cairn-steward-5-2026-09-14-part1.md`.
  - **Strengthening S1.** The limit-set hypothesis can be weakened to "`Z` contains every minimal subset of `Y`", through `minimal-set-complement-ideal-is-ultramatricial` (sk-verify-7 PASS); Steps 1 and 3 are unchanged. Corollary (a) then holds whenever `Y` has finitely many minimal subsets, all periodic orbits. So the "Not covered" paragraph of sk-exact-banded part 2 §3 on recurrent non-minimal sets is false.
