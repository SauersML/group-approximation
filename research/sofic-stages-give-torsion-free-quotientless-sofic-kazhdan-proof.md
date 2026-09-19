---
rg: 2
id: sofic-stages-give-torsion-free-quotientless-sofic-kazhdan-proof
kind: route
title: Finite balls of the torsion-free Tarski monster are balls of a hyperbolic stage, and soficity is closed in the space of marked groups
target: sofic-stages-give-torsion-free-quotientless-sofic-kazhdan
requires:
  - kazhdan-torsion-free-tarski-monster-satisfies-kk
  - local-approximation-properties-are-marked-closed
  - tarski-monster-tori-evade-compression-and-stage-lifts
---

## 0. Imports

- **(M1)–(M4)** as in section 0 of `hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan-proof`,
  all from `kazhdan-torsion-free-tarski-monster-satisfies-kk`:
  - (M1) the stages `G(j)` are torsion-free hyperbolic quotients of `Γ`;
  - (M2) `Q = F(S)/N` with `N = ∪_j N_j` an increasing union;
  - (M3) `Q` is infinite, non-abelian and torsion-free, and all its proper subgroups are cyclic;
  - (M4) `Q` is Kazhdan.
- **(C)** `local-approximation-properties-are-marked-closed`: for every local approximation property
  `P_M`, including soficity and hyperlinearity, a group `G` satisfies `P_M` as soon as, for every
  finite `F ⊆ G`, the table `tab_G(F)` is isomorphic to a table `tab_H(F')` in some group `H`
  with `P_M`. This is the closedness statement in its table form. It is also the definition of
  `P_M` applied to `tab_G(F)`, because `M` depends only on the table.
- **(ES)** Elek--Szabó: an extension of a sofic group by an amenable group is sofic.

## 1. Quotientless, torsion-free, Kazhdan, simple (unconditional)

The first three are section 1 of `hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan-proof`
together with (M3) and (M4).

**Simple.** This is item (i) of `tarski-monster-tori-evade-compression-and-stage-lifts`, which is
unconditional. In short, let `M` be a proper nontrivial normal subgroup. Then `M = ⟨m⟩` is cyclic
by (M3), and `C_Q(m)` has index at most 2, so `C_Q(m) = Q` because `Q` is quotientless. So
`⟨m⟩ ≤ Z(Q)`, and centrelessness (item (i) there) forces `m = 1`.

## 2. Sofic under (S_Γ)

Let `F ⊆ Q` be finite. Choose `r` such that every element of `F` is a word of length at most `r`
in `S`.

By Step 1 of section 2 of `hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan-proof`, which
uses only (M2), some stage `G(j)` satisfies the following for all words `u, v, x` of length at
most `r`:
- `u = v` in `Q` iff `u = v` in `G(j)`;
- `uv = x` in `Q` iff `uv = x` in `G(j)`.

Let `F'` be the image in `G(j)` of the chosen words. Then `u ↦ u` induces an isomorphism of tables
`tab_Q(F) ≅ tab_{G(j)}(F')`, including the products `F·F`, which are words of length at most `2r`.

`G(j)` is a torsion-free hyperbolic quotient of `Γ`, by (M1). So it is sofic by (S_Γ). By (C), `Q`
is sofic. The same argument applies to hyperlinearity, or to any `P_M`, under the corresponding
hypothesis on the stages.

## 3. Mapping tori

Let `ψ ∈ Aut(Q)` and `P = Q ⋊_ψ Z`. `P` is torsion-free: an element `(q, k)` with `k ≠ 0` maps to
`k ≠ 0` in `Z`, and `Q` is torsion-free. Under (S_Γ), `P` is sofic by section 2 and (ES).

## 4. `Q` is not finitely presented (unconditional)

Suppose `Q` were finitely presented. Then `N = ker(F(S) → Q)` is the normal closure of finitely
many elements. By (M2) they all lie in one `N_j`, so `N ⊆ N_j ⊆ N`, and `Q = G(j)` is hyperbolic by
(M1). It is non-elementary, because it is infinite, Kazhdan and so not virtually cyclic. So it
contains a free subgroup of rank 2. That subgroup is not cyclic, and it is proper because `F_2` is
not Kazhdan. This contradicts (M3).

## 5. The contrapositive

Suppose `torsion-free-sofic-kazhdan-group-without-finite-quotients` fails. Fix a torsion-free
cocompact lattice `Γ ≤ Sp(n,1)`, `n ≥ 2`. Such lattices exist by Selberg's lemma, as in the
Corollary of `kazhdan-torsion-free-tarski-monster-satisfies-kk`. By section 1, `Q` is nontrivial,
torsion-free, Kazhdan and quotientless, so it is not sofic. By section 2, (S_Γ) fails: some
torsion-free hyperbolic quotient `G(j)` of `Γ` is not sofic.

## Checked against

- **Nothing about MF is claimed.** MF is not known to be closed in the space of marked groups. The
  norm separation of a nontrivial element can shrink along the stages. So (C) gives nothing for MF,
  and `Rad_MF(Q)` is left open.
- **No hyperbolic-group soficity is claimed.** (S_Γ) is open. It is implied by `(RF_Γ)`.
