---
rg: 2
id: bounded-width-subgroups-of-subshift-gl-locally-finite-proof
kind: route
title: Uniformly bounded width confines every orbit of a basis vector to a bounded window, so the group embeds in a product of boundedly many finite groups
target: bounded-width-subgroups-of-subshift-gl-are-locally-finite
requires: []
artifacts:
  - research/artifacts/sk-exact-gx-2026-09-13-part1.md
---

Notation as in the target. Put `p = sup_{γ∈Γ} w(γ)`.

**Step 1 (faithful banded representation).**
- Fix `y ∈ X`. Put `M = F_q^{(Z)} ⊗ F_q^m`, and let `π(fu^k)δ_t = f(T^{t+k}y)δ_{t+k}`, extended entrywise.
- `π` is a ring homomorphism on `M_m(R)`. It is faithful: if `π(r) = 0`, every coefficient of `r` vanishes on the orbit of `y`. That orbit is dense, and the coefficients are locally constant, so they vanish on `X`.
- An element of width `w` maps `span{δ_s : |s−t| ≤ a} ⊗ F_q^m` into `span{δ_s : |s−t| ≤ a+w} ⊗ F_q^m`.

**Step 2 (bounded invariant windows).**
- For `t ∈ Z` let `U_t = span{π(γ)(δ_t ⊗ e) : γ ∈ Γ, e ∈ F_q^m}`.
- `U_t ⊆ span{δ_s : |s−t| ≤ p} ⊗ F_q^m`, so `dim U_t ≤ m(2p+1)`.
- `U_t` is `π(Γ)`-invariant, because `π(γ′)π(γ) = π(γ′γ)` and `Γ` is a group.
- Every `δ_t ⊗ e` lies in `U_t`, so `Σ_t U_t = M`. Hence `γ ↦ (π(γ)|_{U_t})_t` is injective.

**Step 3 (finiteness).**
- Let `Δ = ⟨γ_1,…,γ_k⟩ ≤ Γ`. The image `Q_t` of `Δ` in `GL(U_t)` has order at most `c = |GL_{m(2p+1)}(F_q)|`.
- The kernel `N_t` of `F_k → Q_t` (through `γ_i`) is a normal subgroup of the free group `F_k` of index at most `c`. There are only finitely many such subgroups: a subgroup of index `≤ c` is determined by a transitive action of `F_k` on at most `c` points.
- So `{N_t : t ∈ Z}` is a finite set `{N_{t_1},…,N_{t_s}}`.
- By Step 2 the kernel of `F_k → Δ` is `⋂_t N_t = ⋂_{i≤s} N_{t_i}`, which has finite index. So `Δ` is finite. ∎

**Model tests.**
- `Γ = ⟨e_12(u)⟩ = {I, e_12(u)}` over `F_2` has width `1` and is finite ✓.
- `Γ = ⟨diag(u,u^{-1},1)⟩ ≅ Z` has unbounded width (`u^n`), and it is infinite: the hypothesis is needed.
- `Γ = SL_3(F_q[u])` has unbounded width and is infinite, not locally finite; the hypothesis fails as it must.
- `GL_m(LC(X,F_q))` has width `0` and is locally finite ✓. Its f.g. subgroups lie in `GL_m(F_q)^P` for a clopen partition `P`.
