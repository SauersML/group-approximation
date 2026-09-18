---
rg: 2
id: kropholler-dim-two-generating-class-descent-proof
kind: route
title: Transfinite induction on the extension-union hierarchy; a finitely generated subgroup either meets the kernel, and the EA-radical theorem makes it BS(1,m), or embeds one level lower
target: kropholler-dim-two-counterexamples-live-in-generating-classes
requires:
  - amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical
---

Notation as in the target; `X` is nonempty. EA is closed under subgroups, extensions and directed unions, and
contains all groups of `cd <= 1` that are amenable: by Stallings–Swan such a group is free, and
an amenable free group is `1` or `Z`.

## Import

- **(R)** `amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical`, item 2. A finitely
  generated amenable group `F` with `cd F = 2` and a nontrivial EA normal subgroup is
  `BS(1,m)` for some `m ≠ 0`, hence EA. Together with the `cd <= 1` case: **every finitely
  generated amenable group of `cd <= 2` with a nontrivial EA normal subgroup is EA.**

## Item 1: the hierarchy

*Monotone.* `L_α ⊆ L_{α+1}`, since `H` is an extension of `H` by the trivial group, `1 ∈ X`
(closed under subgroups), and a group is a directed union of itself. So `L_α ⊆ L_β` for
`α <= β`.

*Subgroups.* Induction on `α`. `L_0 = X` is subgroup-closed. Let `G ∈ L_{α+1}`, so
`G = ∪_i G_i` directed with `N_i ⊴ G_i` and `N_i, G_i/N_i ∈ L_α`. For `S ≤ G`,
`S = ∪_i (S ∩ G_i)` is directed. Also `S ∩ N_i ⊴ S ∩ G_i`, `S ∩ N_i ≤ N_i` lies in `L_α`, and
`(S ∩ G_i)/(S ∩ N_i) ≅ (S ∩ G_i)N_i/N_i ≤ G_i/N_i` lies in `L_α`. So `S ∈ L_{α+1}`. Limits are
unions.

*Quotients* (when `X` is quotient-closed). For `M ⊴ G` as above,
`G/M = ∪_i G_iM/M` is directed, and `G_iM/M ≅ G_i/(G_i ∩ M)` is an extension of
`N_i/(N_i ∩ M)` by a quotient of `G_i/N_i`. Both lie in `L_α` by induction.

*Closure.* If `N ∈ L_α` and `Q ∈ L_β`, any extension of `N` by `Q` lies in `L_{γ+1}` for
`γ = max(α, β)`. A directed union of groups `G_j ∈ L_{α_j}` lies in `L_{γ+1}` for
`γ = sup α_j`, since each `G_j ∈ L_γ` and `L_γ ⊆ L_{γ+1}`. So `∪_α L_α` is closed under
extensions and directed unions, contains `X`, and is contained in every class with these
properties. It is therefore `ED(X)`, and it inherits subgroup- (and quotient-) closure.

## Item 2: descent

Fix `G ∈ ED(X)` with `cd G <= 2` such that every subgroup of `G` lying in `X` is EA. All
subgroups of `G` are amenable and have `cd <= 2`. We prove by induction on `α`:

> `S(α)`: every subgroup `H ≤ G` with `H ∈ L_α` is EA.

`S(0)` is the hypothesis. `S(λ)` for a limit `λ` follows from `S(α)`, `α < λ`.

*`S(α) ⇒ S(α+1)`.* Let `H ≤ G`, `H ∈ L_{α+1}`, `H = ∪_i H_i` directed, `N_i ⊴ H_i`,
`N_i, H_i/N_i ∈ L_α`. Since EA is closed under directed unions, it suffices that every finitely
generated `F ≤ H` is EA. Such an `F` lies in some `H_i`. Put `M = F ∩ N_i ⊴ F`.

- `M ∈ L_α` (subgroup of `N_i`) and `M ≤ G`, so `M` is EA by `S(α)`.
- If `M ≠ 1`, then `F` is finitely generated, amenable, of `cd <= 2`, with the nontrivial EA
  normal subgroup `M`. So `F` is EA by (R).
- If `M = 1`, then `F ≅ FN_i/N_i ≤ H_i/N_i`, so `F ∈ L_α` (subgroup-closed, isomorphism-closed).
  Also `F ≤ G`, so `F` is EA by `S(α)`.

So `S(α+1)` holds. Since `G ∈ L_α` for some `α`, `G` is EA.

Note what was *not* needed: no cohomological dimension bound on the quotients `H_i/N_i`, and no
amenability-specific property of `L_α` beyond amenability of `G`. The quotient enters only
through subgroups `F ≤ G` embedded in it, and those inherit `cd <= 2` from `G`.

## Item 3

Let `G ∈ ED(X)` be a two-dimensional counterexample. By item 2, some subgroup `H_0 ≤ G` with
`H_0 ∈ X` is not EA. Because EA is closed under directed unions, some finitely generated
`H ≤ H_0` is not EA. Then `H ∈ X` (subgroup-closed), `cd H <= 2`, and `H` is amenable. So `H` is
a finitely generated two-dimensional counterexample in `X`. ∎

## Calibration

- `X` = {finite groups} ∪ {abelian groups} gives `ED(X)` = EA (the hierarchy `L_α` is a
  variant of Chou's). Item 3 says that no two-dimensional counterexample is EA, which is trivially true. The
  descent reproduces the known answer and proves nothing false.
- The descent does not claim that `ED(X)`-groups of cd 2 are EA outright. Take `X` = all amenable
  groups. Then item 3 is the tautology "a counterexample contains itself".
