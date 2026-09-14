---
rg: 2
id: separable-factors-hold-countably-many-subshift-groups
kind: claim
title: A separable II_1 factor contains the simple Kazhdan subshift group G_X in its unitary group for only countably many X, so the (T) factors L(G_X) realize continuum many isomorphism classes
distinct_from:
  continuum-many-simple-kazhdan-lef-groups: that counts pairwise nonisomorphic groups G_X; this counts their group von Neumann algebras, and shows no separable factor holds uncountably many of the groups.
  simple-kazhdan-group-gives-property-t-factor-in-r-omega: that shows each L(G_X) is a (T) factor inside R^omega; this shows the factors fall into continuum many classes, with countable fibres.
artifacts:
  - research/artifacts/sk-strong-7-operator-algebras-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Fix a finite alphabet `A` and a prime power `q`. For an infinite minimal subshift `X ⊆ A^Z`, let `S_X = EL_3(LC(X,F_q) ⋊ Z)/Z`. For `q = 2` the centre is trivial and `S_X = G_X`, the group of `simple_kazhdan_sofic_group.tex`. Let `M` be a II_1 factor with separable predual.

1. The set of infinite minimal subshifts `X ⊆ A^Z` such that `U(M)` contains a subgroup isomorphic to `S_X` is at most countable.
2. For every `X`, `L(S_Y) ≅ L(S_X)` holds for only countably many `Y ⊆ A^Z`. The factors `L(G_X)`, `X ⊆ {0,1}^Z`:
   - have property (T);
   - embed in `R^ω`;
   - fall into continuum many isomorphism classes.
   So Connes's rigidity conjecture ("an ICC Kazhdan group is determined by its group von Neumann algebra") holds for this family modulo countable sets, as Ozawa showed for Gromov's groups.
3. No separable II_1 factor contains every `L(G_X)`. The stronger fact that no separable II_1 factor contains every `R^ω`-embeddable separable II_1 factor is due to Nicoara–Popa–Sasyk (J. Funct. Anal. 242 (2007), 230–246, doi:10.1016/j.jfa.2006.05.015), cited through Peterson arXiv:2605.16669, l.77; primary not read. Item 3 gives a hyperlinear simple-group witness for it.

**Why it matters.** Ozawa's non-universality theorem used Gromov–Olshanskii quotients of a hyperbolic Kazhdan group, and Ozawa asked in print whether they embed in `U(R^ω)` (artifact §2). Here a family of simple Kazhdan quotients of a single Kazhdan group is hyperlinear, even LEF. So the argument now runs inside the Connes-embeddable world, and it applies to the note's groups. The group-level count ("continuum many pairwise nonisomorphic `G_X`") becomes a count of factors.

**Proof route:** `separable-factors-hold-countably-many-subshift-groups-proof`. It is a direct application of `kazhdan-simple-quotients-countable-in-separable-factors`:
- `Λ = EL_3(F_q⟨t_+, t_-, t_a : a ∈ A⟩)` has (T) (EJZ);
- each `S_X` is a simple quotient;
- `e_12(∏_{t<n} t_-^t t_{v_t} t_+^t)` maps to a central element of `S_X` iff `v ∉ L(X)`, so different subshifts give different kernels.

## Attempts
- **Exact rigidity** (`L(G_X) ≅ L(G_Y) ⇒ X = Y` or flip conjugate) is not claimed. The separability argument gives only countable fibres. Deformation/rigidity (Popa) or an intrinsic reconstruction would be needed; see the open node `subshift-elementary-group-isomorphism-forces-orbit-equivalence` for the group-level question.
