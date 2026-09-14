---
rg: 2
id: locally-constant-gl-n-subgroup-is-not-confined
kind: claim
title: Over F_2, the locally finite subgroup GL_n(LC(X,F_2)) of EL_n(LC(X,F_2)⋊Z) and all its subgroups are not confined
distinct_from:
  elementary-root-subgroups-over-crossed-products-are-not-confined: that treats the abelian root subgroups e_ij(R); this treats the nonabelian locally finite subgroup of locally constant matrices, using diagonal u-power conjugators
---

**ESTABLISHED (unreviewed).**

Let `X` be a compact zero-dimensional space with a homeomorphism `T`, `R = LC(X,F_2) ⋊_T Z`, `n ≥ 3` and `G = EL_n(R)`.
Put `L = GL_n(LC(X,F_2)) = LC(X, GL_n(F_2))`. Then `L ≤ G`, and no subgroup of `L` is confined in `G`.

In particular `EL_n(LC(X,F_2))` is not confined. It is the locally finite union, over finite clopen partitions `𝒫`, of the
products `∏_{C∈𝒫} GL_n(F_2)`.

**Consequence.** These amenable subgroups are not obstructions to C*-simplicity of `G_X`
(`cstar-simple-iff-amenable-subgroups-not-confined`, `subshift-elementary-groups-are-cstar-simple`).

**Scope.** Over `F_q` with `q > 2` the proof leaves the diagonal torus `LC(X,F_q^×)^n`, and the statement is not claimed.

**Proof:** `locally-constant-gl-n-subgroup-not-confined-proof`.

**Review (sk-verify-13, 2026-09-13, `research/artifacts/sk-verify-13-2026-09-13-part1.md` §2):** PASS. Re-derived Step 1 (`ψ_i` is multiplicative because the entries of `x` are scalars commuting with `e_{C_i}`), the factorization `c_N = ∏ d_i(u^{s_i N})`, the Whitehead identity `w(a)w(−1) = diag(a,a^{-1})` over a noncommutative ring, the entry formula `(g_ij∘T^{−ε_i N})u^{(ε_i−ε_j)N}`, exponent separation off the diagonal, and `LC(X,F_2)^× = {1}`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part6.md`):** PASS (§2). Re-derived Step 1 (`ψ_i` is multiplicative, the disjoint-support factors commute, and their product is `f`), `c_N = ∏ d_i(u^{s_i N})` with the Whitehead identity, the entry formula `(g_ij∘T^{−ε_i N})u^{(ε_i−ε_j)N}`, and that the units of `LC(X,F_2)` are `{1}`. W10 (wording): in the `F_3` model test the torus is normalized, not centralized, by `c_N`; the scope note stands. Concurs with sk-verify-13.
