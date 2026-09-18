---
rg: 2
id: type-f-normal-closure-lemma-is-the-whole-benign-problem-proof
kind: route
title: "Proof: benign subgroups of fp groups are r.e., finite presentations are normal closures of fg subgroups, and the diagonal of F x F conjugates C x 1 onto <<C>> x 1"
target: type-f-normal-closure-lemma-is-the-whole-benign-problem
requires:
  - two-occurrence-realizability-is-type-f-benignness
  - separable-benign-witness-forces-rf-quotient
---

Verification tier: proposed-established. Elementary, on top of the closure
properties (preimages, intersections, injective images) and the sandwich of
`two-occurrence-realizability-is-type-f-benignness` (Steps 4 and 5 of its
proof). Item 3 cites the full-subdirect finite-index theorem of
Bridson--Howie--Miller--Short (equivalently Baumslag--Roseblade for two
free factors).

## Step 1. Item 1

- **(a) ⇒ (b).** Let `C ≤ F` be `F_m`-benign with witness `(Λ, Σ)`, `m ≥ 2`.
  - `Λ` is finitely presented and `Σ` finitely generated, so membership in `Σ` is r.e. (enumerate products of generators and consequences of relators).
  - Hence `C = Σ ∩ F` is r.e., and so is `<<C>>`: enumerate products of conjugates `f c^{±1} f^{-1}`.
  - `<<C>>` is normal, so (a) applies.
- **(b) ⇒ (b').** Finitely generated subgroups of `F` are free of finite rank, hence type `F`, and `(F, C)` is a witness.
- **(b') ⇒ (c).** `N_P = <<R>> = <<C>>` with `C = <R>` finitely generated.
- **(c) ⇒ (a).** This is item 3 of `two-occurrence-realizability-is-type-f-benignness`: every r.e. `N ⊴ F(A)` is a preimage `h^{-1}(N_U)`, and preimages preserve `F_m`-benignness. ∎

## Step 2. Item 2

Let `C = <c_1, ..., c_r> ≤ F`, `N = <<C>>` and `J = <C × 1, ΔF> ≤ F × F`.

- **`J = (N × 1) · ΔF`.** `(f, f)(c, 1)(f, f)^{-1} = (f c f^{-1}, 1)`. So `J ⊇ <<C>> × 1 = N × 1`. `N × 1` is normalized by `ΔF`, so `(N × 1) ΔF` is a subgroup. It contains both generating sets, so it equals `J`.
- **`J = {(u, v) : u v^{-1} ∈ N}`.** `(n f, f)` has `u v^{-1} = n`. Conversely `(u, v) = (u v^{-1} · v, v)`.
- **`J ∩ (F × 1) = N × 1`.** `(u, 1) ∈ J` iff `u ∈ N`.
- **Reduction.** Assume (d). Then `J` is `F_m`-benign in `F × F`. `F × 1` is of type `F`, hence `F`-benign in `F × F` with witness `(F × F, F × 1)`. Intersections of `F_m`-benign subgroups are `F_m`-benign (diagonal trick). So `N × 1` is `F_m`-benign in `F × F`. It is the preimage of `J ∩ (F × 1)` under the injection `F -> F × F`, `f -> (f, 1)`, so `N` is `F_m`-benign in `F` by the preimage property. Applied to finitely presented `P`, this is (b'), hence (a) by Step 1.
- **A join lemma gives (d) for `J`.** `C × 1` and `ΔF` are finitely generated free subgroups, of type `F`, with witnesses `(F × F, C × 1)` and `(F × F, ΔF)`.
- **The free-group version.** Let `π : F * F -> F × F` be the natural map, with `F_1` the first free factor and `Δ' = <a^{(1)} a^{(2)} : a ∈ A>`.
  - `π` maps `<C_1, Δ'>` onto `J`, so `π^{-1}(J) = <C_1, Δ'> · ker π = <C_1, Δ', ker π>`.
  - `π^{-1}(J) ∩ F_1 = {w ∈ F_1 : (w, 1) ∈ J} = N`.
  - `ker π` is `F`-benign in `F * F`: its quotient `F × F` is of type `F` (item 4 of the cited claim, "embedding gives a triple", with the equivalence (i) ⇔ (iii)).
  - So a join lemma for `F_m`-benign subgroups of free groups, applied to `<C_1, Δ'>` (finitely generated) and `ker π`, followed by an intersection with `F_1`, also gives (a). ∎

## Step 3. Item 3

Take `Λ_A = Λ_B = K = F × F`, `Σ_A = C × 1`, `Σ_B = ΔF`. The classical join
witness is `<Σ_A, Σ_B>` in `Λ_A *_K Λ_B = K`, i.e. `J` itself.

- `J` is subdirect: both projections contain `p_i(ΔF) = F`.
- If `N ≠ 1`, then `J ∩ (F × 1) = N × 1 ≠ 1` and `J ∩ (1 × F) = 1 × N ≠ 1`. So `J` is full.
- The index `[F × F : J]` equals `|F/N| = |P|`, via the bijection `J(u, v) -> v^{-1} u N` on right cosets (`J(u, v) = J(u', v')` iff `u u'^{-1} v' v^{-1} ∈ N` iff `v^{-1} u N = v'^{-1} u' N`).
- If `J` were finitely presented, it would be of type `FP_2(Q)`, and by BHMS a full subdirect `FP_2(Q)` subgroup of a product of two nonabelian free groups has finite index. So `P` would be finite.

Hence for infinite `P` with `N ≠ 1` (for example every infinite finitely presented `P` on at least two generators with a nontrivial relator), the classical join witness is not finitely presented. ∎

## Step 4. Items 4 and 5

- **Item 4.** `J ∩ (F × 1) = N × 1`, so a witness `(Λ, Σ)` for `J ≤ F × F` is also a witness for `N × 1` (intersect with `F × 1` via the amalgam of Step 4 of the cited proof). Apply `separable-benign-witness-forces-rf-quotient` item 1 to `N × 1 ≤ F × 1`, with quotient `P`.
- **Item 5 (Goursat).** Let `S ≤ F × F` be finitely generated. Put `P_i = p_i(S)`, free of finite rank, and `L_i = S ∩ P_i ⊴ P_i`.
  - By Goursat there is an isomorphism `θ : P_1/L_1 -> P_2/L_2` with `S = {(u, v) : θ(u L_1) = v L_2}`.
  - Lift `θ` to a homomorphism `λ : P_1 -> P_2` on a free basis. Then `S = {(u, v) : v ∈ λ(u) L_2} = (1 × L_2) · Γ_λ`, and `Γ_λ = {(u, λ(u))}` normalizes `1 × L_2`.
  - `L_2 = S ∩ (1 × F)` is r.e. because `S` is finitely generated.
  - `S` is `F_m`-benign in `F × F` iff it is `F_m`-benign in `P_1 × P_2`: one direction is injective images, the other is intersection with the type `F` subgroup `P_1 × P_2`. ∎
