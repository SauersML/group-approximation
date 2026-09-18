---
rg: 2
id: deligne-class-dies-over-flag-varieties-iff-flag-has-lagrangian
kind: claim
title: Deligne's lattice lifts over a Cantor cover of a real flag variety of Sp_2n exactly when the flag type contains a Lagrangian; it never lifts over spaces with an invariant probability measure
distinct_from:
  deligne-extension-dies-on-lagrangian-cantor-covers: that gives the lift over covers of the Lagrangian Grassmannian; this classifies all real flag varieties of Sp_2n, adding the covers of flag varieties whose flags contain a Lagrangian and proving that every other flag type is excluded.
  deligne-class-survives-on-standard-rational-projective-hosts: that runs the Mackey-Moore argument on orbits in representation spheres; this runs it on the flag varieties themselves and pairs it with the positive direction, which gives a dichotomy.
  groupoid-lifts-of-central-extensions-need-no-invariant-measure: that is the invariant-measure obstruction, used here as item 3.
---

**ESTABLISHED.** Lane proof, not reviewed. It uses the landed nodes cited below and their
flagged textbook inputs. No priority is claimed.

## Setting

- `n ≥ 2`, `G = Sp_{2n}(R)`, `Γ = Sp_{2n}(Z)`.
- `Γ̃` is Deligne's lattice. It is the preimage of `Γ` in the universal cover of `G`, and
  `z` generates `ker(Γ̃ → Γ) ≅ Z`.
- For `I ⊆ {1, …, n}`, `X_I` is the real variety of isotropic flags of dimension type `I`,
  and `P_I` is the stabilizer of a rational flag of that type. So `X_I = G/P_I`.
- For a Cantor `Γ`-space `Y`, a **`Z`-lift over `Y`** is a locally constant cocycle
  `k : Γ̃ × Y → Z` such that `k(z^j γ̃, y) = k(γ̃, y) + d j` for some `d ≠ 0`.
  - It makes `Γ̃` act on `Y × Z` by `(y, m) ↦ (γy, m + k(γ̃, y))`, with `z` acting as
    `m ↦ m + d`.
  - Through `m ↦ t^m` for an infinite-order `t ∈ V`, it gives the embeddings of
    `deligne-lattice-in-fg-simple-lagrangian-brin-thompson-group`.

## Statement

1. **Flags containing a Lagrangian: the lift exists.** Suppose `n ∈ I`. Then every Cantor
   `Γ`-space `Y` with a continuous equivariant map `Y → X_I` carries a `Z`-lift, with
   `d = 2`.
   - Assume in addition that `Γ` acts faithfully on `Y`, modulo `{±I}` for odd `n` and with
     a factor such as `F_3^{2n} ∖ {0}` for even `n`, and minimally and topologically
     freely.
   - Then `Γ̃` embeds in the simple, acyclic group `[[(Γ ⋉ Y) × G_2]]`, which is finitely
     generated when the action is expansive. This combines
     `cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple` with Steps 4 and 5 of
     `deligne-lattice-lagrangian-brin-thompson-embedding-proof`.
2. **All other flag types: no lift.** Suppose `n ∉ I`. Let `Y` be a Cantor `Γ`-space with
   a continuous equivariant `π : Y → X_I` that is injective over a `Γ`-invariant Borel set
   `E` of full smooth measure, with Borel inverse on `E`. Then there is no `Z`-lift over
   `Y`.
3. **Invariant measures: no lift.** If `Y` carries a `Γ`-invariant probability measure,
   there is no `Z`-lift over `Y`. This covers every equicontinuous or profinite model,
   for example `Γ` acting 2-adically linearly on `Z_2^{2n}`, as in the host `W` of
   `twisted-integral-affine-full-group-is-finitely-presented`.

**The case n = 2.**
- The flag types are `I = {2}` (the Lagrangian Grassmannian `Λ_2 ≅ Ein^{1,2}`),
  `I = {1,2}` (full flags `G/B`), and `I = {1}` (`RP^3`).
- Only the first two host Deligne's lattice. The third is the flag variety behind the
  standard representation sphere, which is excluded, consistent with
  `deligne-class-survives-on-standard-rational-projective-hosts`.

## Proof

1. **Item 1.**
   - Forgetting all members of the flag except the Lagrangian gives a `G`-equivariant map
     `X_I → Λ_n(R)`. Compose it with `Y → X_I`.
   - Pull back the universal cover `Λ̃ → Λ_n(R)` along this map, and choose a continuous
     section over the Cantor set `Y`. This gives the cocycle `k` with `k(z, ·) = 2`, since
     `z` acts on `Λ̃` as `T^2`. This is Step 3 of
     `deligne-lattice-lagrangian-brin-thompson-embedding-proof`, which uses only the
     continuous equivariant map to `Λ_n(R)`.
   - The embedding clause is Steps 4 and 5 of that route, with `Y` in place of `Y_u`. The
     host is simple and acyclic by `cuntz-stabilized-minimal-full-groups-are-acyclic-and-simple`.
2. **Item 2.**
   - Let `V_r` be the largest member of the flag, so `r = dim V_r < n`. Let
     `W ⊂ V_r^{⊥ω}` be a symplectic complement of `V_r` in `V_r^{⊥ω}`. Then `dim W = 2(n−r) ≥ 2`.
   - `Sp(W)`, acting trivially on `W^{⊥ω} ⊇ V_r`, fixes every member of the flag. So
     `Sp(W)(R) ≤ P_I`.
   - `X_I = G/P_I` is a single `G`-orbit carrying the smooth measure class, and `E` is
     conull there.
   - Suppose a `Z`-lift `k` exists. Then `κ(γ, x) = k(γ̃, π^{-1} x)` on `Γ × E` is a
     bounded Borel trivialization of `d·ε`.
   - The proof of `deligne-class-survives-on-standard-rational-projective-hosts`, run with
     `O = G/P_I` and the block `Sp(W) ≤ P_I`, applies verbatim. Its three steps are
     Mackey–Moore induction, integration over `Γ\G`, and restriction to `Sp(W)`. It never
     uses linearity of `O`.
   - It gives `d · res^G_{Sp(W)} [ε_G]_R = 0` in `H^2_c(Sp(W)(R); R)`. But `Sp(W) ⊂ G` is an
     isomorphism on `π_1`, and the Kähler class is nonzero. This is a contradiction.
3. **Item 3.** This is `groupoid-lifts-of-central-extensions-need-no-invariant-measure`.
   The class `ε` is nonzero in `H^2(Γ; R)`, so every `d ε` is nonzero. ∎

## Lesson for general BH

- Among the natural Cantor models of arithmetic actions of `Sp_{2n}(Z)`, Deligne's lattice
  can be hosted by the lift mechanism only over flag varieties whose flags contain a
  Lagrangian (Siegel type).
  - Projective spaces and spheres are excluded; they are the setting of `𝒯_m` for the
    mapping class groups.
  - Profinite spaces are excluded; they are the setting of `W` for `GL_n(Z)`.
- A single "Cantorized arithmetic action ⇒ finitely presented full group" theorem that is
  to reach Deligne's lattice must therefore cover Siegel-type flag varieties.
- `maslov-cantorizations-have-no-finite-dissection-type` shows that at `n = 2` the
  standard diagram engine cannot do that.
