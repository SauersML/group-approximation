---
rg: 2
id: pisot-stein-groups-with-commensurable-f-unit-slopes-are-fp-proof
kind: route
title: Run the Pisot finite-nucleus argument with real slope exponents in the c-shift, then group the c-shift into blocks of length a so that its canonical similarities have slopes in ⟨β⟩
target: pisot-stein-groups-with-commensurable-f-unit-slopes-are-fp
requires:
  - pisot-stein-groups-are-contracting-rsgs
  - pisot-unit-slope-stein-groups-are-finitely-presented
  - contracting-rsgs-embed-in-fp-simple-groups
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

Notation as in the target, and as in `pisot-stein-groups-are-contracting-rsgs-proof`, written for the coding base `c`:
- `X_c` is the `c`-shift, with Parry graph `Γ_c` and start state `s_0`;
- `len` is the length of finite greedy `c`-expansions;
- `ρ_σ = |σ(c)| < 1` for embeddings `σ ≠ id`, and `D = ⌊c⌋`;
- `G := V(Γ,⟨β⟩,1)` with `Γ = Z[c]`.

**Step 0 (β is a Pisot unit in the same field).**
- `β^b = c^a` gives `|σ(β)| = ρ_σ^{a/b} < 1` for every `σ ≠ id`.
- If some `σ ≠ id` fixed `β`, then `|σ(β)| = β > 1`, a contradiction. So `β` has `[Q(c):Q]` distinct conjugates, and
  `Q(β) = Q(c)`.
- `β` is a unit of `Γ`: `β^{-1} = β^{b-1} c^{-a} ∈ Γ`. So `Γ` is a `Z[⟨β⟩]`-module and `(Γ,⟨β⟩,ℓ)` is a Stein triple.

**Step 1 (G acts on the c-coding).**
- By (F) for `c`, `π : X_c → [0_+,1_−]` is the interval Cantorized at `Fin(c) ∩ (0,1) = Γ ∩ (0,1)` (step 1 of the cited
  proof).
- Elements of `G` are piecewise `x ↦ β^j x + t`, with `t ∈ Γ` and breakpoints in `Γ`. They send `Γ` to `Γ`, so they are
  homeomorphisms of `X_c`.
- Write `β^j = c^κ` with `κ = ja/b ∈ (1/b)Z`.

**Step 2 (finite nucleus in the c-coding).** Repeat steps 2–5 of `pisot-stein-groups-are-contracting-rsgs-proof` with the
integer exponent `k` replaced by the real exponent `κ`. The changes are:
- **Length lemma.** It holds for real `n`, because `ρ_σ^{-n} ≤ ρ_σ^{-⌈n⌉}`.
- **Slope defect.** `|σ(c^{-κ})| = |σ(β)|^{-j} = ρ_σ^{-κ}`, so the estimate
  `|σ(p)| ≤ C_c ρ_σ^{-(κ+L)}` is unchanged. Hence `|ō(w)| ≥ |w| − κ − L_c`, and also `|ō(w)| ≤ |w| − κ + log_c(ℓ_max/ℓ_min)`.
  So `e := κ + |ō(w)| − |w|` lies in a fixed bounded window. It also lies in `(1/b)Z`, so it takes finitely many values.
- **Offsets.** `d = c^{|ō(w)|}(β^j a_w + t − a_{ō(w)})` lies in `Γ ∩ [0, ℓ_max)`, since `β^j ∈ Γ`. Its conjugates are
  bounded by the same estimate, with `ρ_σ^{|ō|}·ρ_σ^{κ}·ρ_σ^{-|w|} = ρ_σ^{e}` bounded. So `d` takes finitely many values.
- **Conclusion.** The local action at a deep cone is `ω ↦ d + c^{e}ω`, determined by `(t(w), t(ō(w)), e, d)`. So every
  `f ∈ G` is rational on `X_c`, and all deep local actions lie in one finite set `𝒩` that does not depend on `f`.

**Step 3 (block recoding).**
- **The graph.** Let `Γ_c^{[a]}` have the paths of length `a` in `Γ_c` as edges. Its paths from `s_0` are those of `Γ_c`,
  read in blocks, so `X_c` is also its path space. Its cones are the `Γ_c`-cones of levels in `aZ`.
- **Strongly connected.** At `s_0` the digit `0 < ⌊c⌋` returns to `s_0`, so `Γ_c` is strongly connected with a loop,
  hence primitive. So `Γ_c^{[a]}` is strongly connected, and it is not a single cycle, since `X_c` has no isolated
  points.
- **Local actions.** Let `|w| ∈ aZ`, and let `C_{ō}` be the smallest `Γ_c`-cone containing `f(C_w)`. The cones
  containing `f(C_w)` form a chain, so the smallest block cone containing it is `C_{ō'}`, where `ō'` is the prefix of
  `ō` of length `a⌊|ō|/a⌋`. With `u` the remaining `< a` letters of `ō`, the block local action is `ω ↦ u·f|_w(ω)`.
- **So the nucleus stays finite.** The block local actions of deep cones lie in the finite set of pairs `(u, ψ)` with
  `|u| < a` and `ψ ∈ 𝒩`. Every `f ∈ G` is rational for `Γ_c^{[a]}`, and the nucleus of `G` there is finite.

**Step 4 (RSG and full).**
- **Canonical similarities.** For block cones `C_w`, `C_{w'}` of the same terminal state, with `|w| = an` and
  `|w'| = an'`, the canonical similarity is `x ↦ a_{w'} + c^{a(n−n')}(x − a_w)`. Its slope is `β^{b(n−n')} ∈ ⟨β⟩` and
  its offsets are in `Γ`. So the Thompson group `V_{Γ_c^{[a]}, C_{s_0}}` lies in `G`, and `G` is an RSG (BBMZ Prop.
  `RSGsAndV`). It is contracting by Step 3.
- **Full.** A homeomorphism that locally agrees with `G` agrees with it on finitely many clopen pieces. By (F) those are
  finite unions of intervals with endpoints in `Γ`, so the homeomorphism is a piecewise `x ↦ β^j x + t` bijection with
  breakpoints in `Γ`, and lies in `G`.
- **Finite presentation.** BBMZ Theorem A: a full contracting RSG is finitely presented. `contracting-rsgs-embed-in-fp-simple-groups`
  gives the embeddings.
- **General ℓ.** Conjugate by `x ↦ β^{-m}x` with `β^{-m}ℓ ≤ 1`, as in step 6 of the cited proof and step 1 of
  `pisot-unit-slope-stein-groups-are-finitely-presented`. On the clopen set `[0, β^{-m}ℓ)` the group is the full group of
  `G`-germs, again a full contracting RSG.

**Step 5 (abelianization, when `Z[β] = Z[c]`).** As in step 2 of `pisot-unit-slope-stein-groups-are-finitely-presented`,
with `A` = multiplication by `β` on `Γ ≅ Z^d`.
- **H_0.** `H_0 = Γ/(1−β)Γ` has order `|N(1−β)| ≠ 0`.
- **H_1.** `H_1 = H_2(Γ ⋊_A Z)` is an extension of `ker(1 − A) = 0` by `coker(1 − Λ²A)`, whose eigenvalues are the
  products `β_iβ_j`, `i < j`.
- **Degree ≥ 3.** No such product has modulus 1. If `|β_1β_j| = 1`, the remaining `d − 2 ≥ 1` conjugates, all of
  modulus `< 1`, would have product of modulus 1. Products of two small conjugates have modulus `< 1`.
- **Degree 2.** The single product is `N(β)`.
- **Conclusion.** With the AH sequence `H_0 ⊗ Z/2 → V^ab → H_1 → 0`, `V^ab` is finite exactly in the cases listed. If
  `d = 2` and `N(β) = +1`, then `H_1 ≅ Z` and `V^ab ↠ Z`. `D(V)` is simple by Tanner's theorem, and finite index gives
  finite presentation.

**Step 6 (the example).** `c = θ` has (F), `a = 3`, `b = 1`, and `Z[θ+1] = Z[θ]`. The orders of `H_0` and `H_1` are
computed in the target. Both are 1, so `V^ab = 0` and `V = D(V)` is simple. ∎
