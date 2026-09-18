---
rg: 2
id: fully-self-replicating-tree-groups-give-fg-tits-hosts
kind: claim
title: Every finitely generated self-similar group R with psi(Stab_R(1)) = R^d and root image A_d gives a finitely generated simple Tits-(P) amalgam (R wr A_(d+1)) *_(R x R) (R wr A_(d+1)) with finitely generated edge groups and finite-state elements, finitely presented iff R is
artifacts:
  - experiments/finite-state-tits-hosts-2026-09-17/verify_full_wreath_recursion.py
  - experiments/finite-state-tits-hosts-2026-09-17/verify_full_wreath_recursion.out
distinct_from:
  tits-independence-vertex-groups-are-branch-type: that shows the vertex groups of a locally finite (P)-host are branch-type, and are finitely presented when the host and edge groups are; this goes the other way, building a (P)-host from any fully self-replicating group and transferring finite presentation both ways.
  micro-supported-tree-actions-self-embed-rigid-stabilizers: that finds infinite direct sums inside rigid stabilizers of every micro-supported tree action; this realizes rigid stabilizers isomorphic to a prescribed finitely generated self-replicating group.
  self-similar-spinal-groups-not-fp-torsion-quotients: that is about finitely presented covers of spinal groups; this uses one spinal group, R = <A_5, b>, only as a certified instance of full self-replication.
---

**ESTABLISHED (unreviewed).** Proof: `fully-self-replicating-tree-groups-give-fg-tits-hosts-proof`.
The instance in item 5 is certified by the attached script.

**Setting.** Let `d ≥ 3` and `X = {0, ..., d−1}`. `Aut(X*)` is the automorphism group of the
rooted `d`-ary tree. For `s ∈ Aut(X*)` and `x ∈ X`, `s = π_s · (s|_x)_x`, where `π_s ∈ Sym(X)` is
the root permutation and `s|_x` the section. A subgroup `R ≤ Aut(X*)` is **fully
self-replicating with root image `A_d`** if:

- **(S)** `s|_x ∈ R` for all `s ∈ R` and `x ∈ X`;
- **(B)** for every `r ∈ R` and `x ∈ X`, the element `r@x` (section `r` at `x`, identity at the
  other letters, trivial root permutation) lies in `R`;
- **(A)** `{π_s : s ∈ R} = A_d`.

Then `R ≅ R ≀_X A_d` through the section map.

**The host.** Let `T = T_{d+1}` with a legal edge colouring by `C = {0, ..., d}`. Let
`G ≅ *_{c ∈ C} Z/2` be the group of colour-preserving automorphisms. `G` is **edge-free**:
only `1` fixes two adjacent vertices, and `G` is simply transitive on vertices. Colour
relabellings `λ_c : C∖{c} → X` identify each half-tree `Y_f` with `X*`. This gives sections
`s_f(g) ∈ Aut(X*)` of any `g ∈ Aut(T)` at every oriented edge `f`, with
`s_f(gh) = s_{hf}(g) s_f(h)`, and every `s_f(k) = 1` for `k ∈ G`. Put

`Γ_R = {g ∈ Aut(T) : s_f(g) ∈ R for every oriented edge f}`.

**Theorem.** Let `R` be fully self-replicating with root image `A_d`. Then:

1. **Group and core.** `Γ_R` is a subgroup of `Aut(T)` containing `G`. It acts
   vertex-transitively, fixes no end, and `T` is not a line.
2. **Tits' property (P)** holds: `Γ_f = R_Γ(Y_f) · R_Γ(Y_{f̄})`. The map `s_f` is an
   isomorphism `R_Γ(Y_f) ≅ R`, so `Γ_f ≅ R × R`.
3. **Vertex groups.** `Γ_v ≅ R ≀_{C} A_{d+1}`, with local action `A_{d+1}` at every vertex.
4. **Simplicity and presentation.** `Γ⁺ = ⟨Γ_f⟩` is the type-preserving subgroup, of index 2.
   It is the amalgam
   `Γ⁺ = Γ_v *_{Γ_f} Γ_{v'}  ≅  (R ≀ A_{d+1}) *_{R × R} (R ≀ A_{d+1})`
   for adjacent `v, v'`. It is simple by Tits' theorem. If `R` is finitely generated, then
   `Γ_R` and `Γ⁺` are finitely generated and have nontrivial finitely generated edge groups.
   `Γ_R` is finitely presented iff `Γ⁺` is iff `R` is.
5. **Instance.** Let `d = 5`, `α = (0 1 2 3 4)`, `β = (0 1 2)` and `b = (b, α, β, 1, 1)`
   (trivial root permutation). Then `R = ⟨A_5, b⟩` satisfies (S), (B) and (A). All its
   elements are finite-state. So `Γ_R` is a finitely generated group of finite-state
   automorphisms of `T_6` over the edge-free core `G`, with (P) and edge groups `R × R`.
6. **No finite-state obstruction.** Call `g ∈ Aut(T)` **finite-state over `G`** if for some
   (equivalently every) vertex `v`, the sections of `g` at the edges pointing away from `v`
   form a finite set. These elements form a group `FS(G)` containing
   `Γ(G, 1)` of `finitely-singular-tree-hosts-have-no-fg-stabilizers`. The analogue of that
   node's item 5 for `FS(G)` is **false**. Let `D` be any function on `Γ_f` that is finite
   on a finite generating set and satisfies `D(gh) ≤ max(D(g), D(h))` and
   `D(g^{-1}) = D(g)`. Then `D` is bounded on `Γ_f`, so it cannot tend to infinity on deep
   rigid stabilizers. So neither natural candidate works.
   - **Number of away-states** is only submultiplicative, not ultrametric.
   - **Depth of the first non-core section** stays bounded on deep rigid elements, because
     the pieces `b@w` sit on the path to the support.

**What this says about the Tits route of `boone-higman-conjecture` (Attempt 8).**

- Attempt 8 asks for some finitely presented group acting faithfully and minimally on a
  tree, with (P) and a nontrivial finitely generated edge group, and suggests that
  infinite valence might be forced. Valence need not be infinite: item 5 is locally finite.
  **Finite generation is free. What remains is finite presentation**, and within the
  section-closed hosts `Γ_R` it is exactly finite presentation of a fully
  self-replicating `R`.
- Such an `R` is a level-transitive regular branch group over itself. Item 4 is therefore
  a two-directional reduction:
  **a finitely presented simple Tits-(P) amalgam of this shape exists iff a finitely
  presented fully self-replicating group with root image `A_d` exists.**
  The latter would be a finitely presented branch group, which is the open question of
  Bartholdi--Grigorchuk--Šunić. This agrees with item 6 of
  `tits-independence-vertex-groups-are-branch-type`.
- **Contracting instances fail.** A contracting regular branch group is not finitely
  presented (Bartholdi, "Endomorphic presentations of branch groups", J. Algebra 268
  (2003); cited, not re-proved here). The instance `R = ⟨A_5, b⟩` is generated by a
  bounded automaton, so it is contracting (Bondarenko--Nekrashevych), and its host is not
  finitely presented. A finitely presented `Γ_R` needs a non-contracting fully
  self-replicating `R`.

**Calibration.**

- `R = Aut_{A_d}(X*)`, the full iterated wreath product (uncountable). It satisfies (S),
  (B) and (A), and `Γ_R` is the Burger--Mozes group `U(A_{d+1})`. This
  recovers the familiar splitting `U(A_{d+1})_f = R(Y_f) × R(Y_{f̄})`.
- `R = Fin(A_d)`, the finitary elements. It is (S), (B), (A), locally finite and not
  finitely generated. `Γ_R` is Le Boudec's `G(1, A_{d+1})`, and its edge groups are not
  finitely generated, as `finitely-singular-tree-hosts-have-no-fg-stabilizers` predicts.
- `R = ⟨A_5, b⟩` sits strictly between the two, and item 5 shows it is finitely generated.
