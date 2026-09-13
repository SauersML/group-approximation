---
rg: 2
id: marked-subshift-elementary-group-determines-language-proof
kind: route
title: Nested Steinberg commutators spell cylinder indicators; the scalar centre detects exactly the empty cylinders
target: marked-subshift-elementary-group-determines-language
requires: [subshift-elementary-group-is-simple-modulo-centre, minimal-subshift-algebra-is-simple-lef-ring]
artifacts:
  - research/artifacts/un-open-5-marked-subshift-groups-2026-09-13.md
---

Artifact §§1–3.
1. `S_0` generates `R_X` as a ring (`minimal-subshift-algebra-is-simple-lef-ring`, item 1). By
   `e_ij(a)e_ij(b) = e_ij(a+b)` and `[e_ij(a), e_jk(b)] = e_ik(ab)`, the tuple `σ_X` generates `S_X`.
2. For a monomial `m` in the free ring `Z⟨U, V, C_a, Θ⟩`, define `ω_ik(m)` recursively by
   `ω_ik(s m') = [ω_ij(s), ω_jk(m')]` with `{i,j,k} = {1,2,3}`. By induction, it evaluates to `e_ik(ev(m))` in
   `EL_3` over any ring (Lemma 2.1).
3. Put `m_w = ∏_t V^t C_(w_t) U^t`. From `u f u^(-1) = f∘T^(-1)` we get `u^(-t) χ_a u^t = χ_[x_t=a]`, so
   `ev_X(m_w) = χ_[x_[0,n)=w]` (Lemma 2.2).
4. `Z(G_X) ⊆ F_q^× I_3` (`subshift-elementary-group-is-simple-modulo-centre`), and `e_12(f)` has `(1,2)` entry
   `f`. So `W_w(σ_X) = 1` iff `f = 0` in `R_X`. By injectivity of `LC(X) → R_X`, that holds iff the cylinder is
   empty. By shift invariance, that holds iff `w ∉ L(X)`.
5. A subshift equals the set of sequences all of whose finite subwords are legal, so `L(X)` determines `X`.
