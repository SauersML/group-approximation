---
rg: 2
id: just-infinite-over-simple-subgroup-gives-fp-simple-host-proof
kind: route
title: Pass to the finite residual of the normal closure, split it along conjugates of a maximal normal subgroup, and retract
target: just-infinite-over-simple-subgroup-gives-fp-simple-host
requires: []
---

Notation is as in the claim: `S ≤ Γ` is infinite simple, `N = <<S>>^Γ`, and every
nontrivial normal subgroup of `Γ` inside `N` has finite index in `Γ`. We use two
standard facts about abstract groups:

- **(F1)** A finite-index subgroup of a group `Γ` is finitely generated (resp.
  finitely presented) iff `Γ` is.
- **(F2)** A retract of a finitely presented group is finitely presented.

**Step 1.** `N` is normal and nontrivial, since it contains `S`. So `N` has finite
index in `Γ`.

**Step 2.** An infinite simple group has no proper finite-index subgroup. A proper
finite-index subgroup would have a normal core of finite index; the core is proper,
so it is trivial, and then `S` is finite. Hence `S` lies in every finite-index
subgroup of `N`, that is, in the finite residual `R` of `N` (the intersection of
all finite-index subgroups of `N`). In particular `R ≠ 1`.

**Step 3.** `R` is characteristic in `N` and `N ◁ Γ`, so `R ◁ Γ`. Also `R ≤ N` and
`R ≠ 1`, so `R` has finite index in `Γ`. Every finite-index subgroup of `R` has
finite index in `N` and therefore contains `R`. So `R` has no proper finite-index
subgroup.

**Step 4.** `Γ` is finitely generated, so by (F1) `R` is finitely generated, and it
is nontrivial. By Zorn's lemma `R` has a maximal proper normal subgroup `M`. The
union of a chain of proper normal subgroups is proper, since otherwise it contains
the finitely many generators and hence some member of the chain does. Then `R/M`
is simple, and it is infinite by Step 3. `T := R/M` is finitely generated.

**Step 5.** `R` normalizes `M` and has finite index in `Γ`, so `M` has finitely many
`Γ`-conjugates `M_1, …, M_m`, each a maximal normal subgroup of `R` (conjugation by
`γ ∈ Γ` is an automorphism of `R`). Hence each `R/M_i ≅ R/M =: T`. Put
`D = ∩ M_i`. Then `D ◁ Γ` and `D ≤ R ≤ N`. If `D ≠ 1`, then `D` has finite index in
`Γ`, so `R/D` is finite, so `D = R` by Step 3; but `D ≤ M ≠ R`. Hence `D = 1`.

**Step 6.** Choose `J ⊆ {1, …, m}` minimal with `∩_{i∈J} M_i = 1`, and for `j ∈ J`
put `L_j = ∩_{i∈J∖{j}} M_i`.

- `L_j ◁ R`, and `L_j ≠ 1` by minimality.
- `L_j ∩ M_j = 1`, so `L_j` maps injectively into `R/M_j ≅ T`. Its image is a
  nontrivial normal subgroup of the simple group `T`, hence all of `T`.
  So `L_j ≅ T`.
- For `k ≠ j`, `L_k ≤ M_j`. So the natural map `φ : R → ∏_{j∈J} R/M_j` sends
  `L_j` onto the `j`-th factor and trivially to every other factor. Thus
  `φ(∏ L_j)` is the whole product, while `φ` is injective because `∩_J M_i = 1`.
  So `φ` is an isomorphism and `R ≅ T^k` with `k = |J|`.

**Step 7.** `S ≤ R` and `S ≠ 1`, so some coordinate of `φ` is nontrivial on `S`.
Its kernel on `S` is a proper normal subgroup of the simple group `S`, hence
trivial. So `S` embeds in `T`.

**Step 8 (clause 3).** A coordinate `T` is a retract of `R ≅ T^k`: include it as a
factor and project. If `Γ` is finitely presented, then `R` is finitely presented by
(F1), and `T` is finitely presented by (F2). Conversely, if `T` is finitely
presented then so is `T^k`, being an iterated direct product, and hence so is `Γ` by (F1).

This proves clauses 1 through 3. ∎

**Scope note.** Finite generation is used only in Step 4, to get `M`. The claim is
consumed for finitely presented `Γ` (in `boone-higman-iff-fp-just-infinite-hosts`)
and for uniform lattices in compactly generated groups, which are finitely
generated (in `boone-higman-via-bader-shalom-lattice-hosts`).
