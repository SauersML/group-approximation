---
rg: 2
id: gl-3-z-in-no-nv-via-cnd-transversal
kind: route
title: The transversal half of the Haagerup program for nV alone excludes GL_3(Z) from every nV
target: some-gl-n-z-embeds-in-no-brin-thompson-group
requires:
  - brin-thompson-nv-cnd-proper-modulo-triangular-subgroup
  - triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z
  - elementary-groups-over-fg-rings-have-property-t
  - thompson-v-has-no-heisenberg-subgroup
artifacts:
  - research/artifacts/gq-gq-nv-obstruct-verdict.md
---

Lane gq-nv-obstruct, 2026-09-17. Not independently reviewed.

This route needs only the transversal function `ψ_1` of
`brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`. It does not need the
properness on `T_n` (`brin-thompson-nv-cnd-proper-on-triangular-subgroup`) that
the Haagerup route `brin-thompson-nv-a-t-menable-via-triangular-split` also
needs. So that transversal claim alone settles Zaremsky 2.19(c) and 2.19(d)
negatively, with `n = 3` as the witness. It also closes the plain `nV` family
for `gl-n-q-embeds-in-fp-simple-group`, `n >= 3`, through item 3 of
`rational-stepping-stones-in-nv-need-bs12-or-heisenberg`.

**m = 1.** `GL_3(Z)` contains `H_3(Z)` (upper unitriangular matrices), and `V`
contains no `H_3(Z)` (`thompson-v-has-no-heisenberg-subgroup`).

**m >= 2.** Suppose `ι: GL_3(Z) -> mV` is injective, and put `K = ι(SL_3(Z))`.
1. `SL_3(Z) = EL_3(Z)` has property (T)
   (`elementary-groups-over-fg-rings-have-property-t`, `R = Z`, `n = 3`), and so
   does its isomorphic image `K`.
2. Let `ψ_1` be the function of `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup`
   on `mV`. Its restriction to `K` is conditionally negative definite. A group
   with property (T) has property (FH), so every conditionally negative definite
   function on it is bounded. This is the Delorme–Guichardet theorem, together
   with the correspondence `ψ(g) = ‖b(g)‖²` between such functions and affine
   isometric actions (Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*,
   Theorem 2.12.4, and §2.10 with Appendix C for the correspondence). So `K ⊆ {ψ_1 <= R}` for some
   `R`.
3. By the choice of `ψ_1`, `{ψ_1 <= R} ⊆ g_1 T_m ∪ ⋯ ∪ g_r T_m` for finitely many
   `g_i`. If `K ∩ g_i T_m` contains some `k_i`, then `g_i T_m = k_i T_m`, and so
   `K ∩ g_i T_m = k_i (K ∩ T_m)`. Hence `K` is a union of at most `r` left cosets
   of `K ∩ T_m`, and `[K : K ∩ T_m] <= r`.
4. A subgroup of finite index contains a nontrivial power of every element. So
   `ι(e_12)^N ∈ T_m` for some `N >= 1`, where `e_12` is the elementary root
   element.
5. This contradicts item 3 of `triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z`
   with `f = 1`: for any embedding of `SL_d(Z)` or `GL_d(Z)` into `mV`, `d >= 3`,
   no nontrivial power of a root element lies in any conjugate of `T_m`.

So `GL_3(Z)` embeds in no `mV`, and `n = 3` witnesses the target. ∎

**Remark.** Steps 1–4 use only property (T). They show that every Kazhdan
subgroup of `nV` has a finite-index subgroup inside `T_n`, given `ψ_1`. Step 5 is
the only place where `SL_3(Z)` is used.

**Review.** gq-referee-a, proof-gap lens: PASS as a conditional route (report
landed d89c65d4d). gq-referee-b, citation and hypothesis lens: PASS as a
conditional route (0c5ef12bf). The referee noted that given `ψ_1`,
`kazhdan-finiteness-in-nv-via-cnd-transversal` already makes `SL_3(Z)` finite
inside `nV`, which is absurd. So step 5 and its unreviewed input
`triangular-subgroups-of-nv-contain-no-heisenberg-or-sl3z` are not needed for
Zaremsky 2.19(c)/(d). That shorter chain is recorded in the other route. This
route is kept because it uses only one conjugate of `T_n`.
