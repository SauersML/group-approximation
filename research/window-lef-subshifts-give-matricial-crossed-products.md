---
rg: 2
id: window-lef-subshifts-give-matricial-crossed-products
kind: claim
title: A free subshift with partial finite models exact on windows has a matricial crossed product, a LEF acting group, and LEF general linear groups over finite fields
distinct_from:
  residually-finite-actions-give-matricial-crossed-products: that uses genuine finite actions, which exist only over residually finite groups; this uses partial actions exact on balls, which is the hypothesis that can reach LEF acting groups that are not RF, and it coincides with that theorem for finitely presented groups.
  minimal-subshift-algebra-is-simple-lef-ring: that is the case of Z, through return words.
artifacts:
  - research/artifacts/sk-general-actions-b-converse-map-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; route `window-lef-subshifts-give-matricial-crossed-products-proof`, artifact §2).**

**Definition.** Let `Γ` be finitely generated, with word balls `B_r`. A subshift `X ⊆ A^Γ`, with `(g·x)(h) = x(g^(-1)h)`, is *window-LEF* if for every `r` there are:
- a finite set `E` and a colouring `c : E -> A`;
- permutations `β(s)`, `s ∈ B_(4r)`, with `β(e) = id` and `β(st) = β(s)β(t)` whenever `s, t, st ∈ B_(4r)`;

such that the patterns `c_z(λ) = c(β(λ^(-1))z)`, for `λ ∈ B_r` and `z ∈ E`, are exactly `L_(B_r)(X)`.

**Theorem.** Let `X ⊆ A^Γ` be a free window-LEF subshift, `k` a field and `R = LC(X,k) ⋊ Γ`.
1. `Γ` is LEF.
2. `R` embeds unitally and injectively in `∏_ω M_(N_n)(k)`, with `N_n = |E_n|`. The map is `Σ f_g u_g ↦ Σ D(f_g) P_(β(g))`.
3. If `k = F_q`, every finitely generated subgroup of every `GL_M(R)` is LEF.
4. If `Γ` is finitely presented, then window-LEF, window-periodic and Kerr–Nowak residually finite are equivalent.

**Why it matters.**
- By `free-rf-actions-force-residually-finite-groups`, no free subshift over a non-RF group is window-periodic, so over such groups this is the only form of finite models that can work.
- If `X` is also minimal, `EL_N(R)/Z` is infinite, simple and Kazhdan, and it is LEF by item 3.
- Existence of free minimal window-LEF subshifts over LEF groups that are not RF is not settled here.

**Model tests.**
- Every infinite minimal `Z`-subshift is window-periodic, so it is window-LEF.
- Labbé's shift over `Z^2` is not window-LEF: `Z^2` is finitely presented, so item 4 would make it window-periodic, which an SFT without periodic points excludes.
