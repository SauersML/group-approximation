---
rg: 2
id: simple-groups-on-trees-b1-zero-proof
kind: route
title: Simplicity rules out acylindrical hyperbolicity, so every two vertices have an infinite common stabilizer; Peterson-Thom then kills the first L2-Betti number
target: simple-groups-on-trees-with-fg-edge-groups-have-b1-zero
requires: []
---

Notation as in the target.

**Cited results (read at source 2026-09-18).**
- **Minasyan–Osin**, arXiv:1310.6289, TeX `acyl-trees-Dec-2017-revised.tex` l.206–210 (Theorem `main-1`): "Let
  G be a group acting minimally on a simplicial tree T. Suppose that G does not fix any point of ∂T and there
  exist vertices u,v of T such that the pointwise stabilizer Pst_G{u,v} is finite. Then G is either virtually
  cyclic or acylindrically hyperbolic." At l.241–242 they note: "simple groups are never acylindrically
  hyperbolic". This is from their Theorem `thm:elem-prop-ah`(e): acylindrically hyperbolic groups are
  SQ-universal.
- **Peterson–Thom**, arXiv:0708.4327, source l.850–853 (Theorem `main2`): "Let G be a countable discrete group
  and suppose H is an infinite index, infinite ws-normal subgroup. If β_1^(2)(H) < ∞, then β_1^(2)(G) = 0."
  Here s-normal means `gHg^(-1) ∩ H` infinite for all `g` (l.714), and s-normal implies ws-normal (l.721).

**Step 1: the minimal subtree and no fixed end.**
- `G` is finitely generated and fixes no vertex. So some element is hyperbolic: by Serre, a finitely generated
  group of elliptic automorphisms fixes a vertex. Hence there is a unique minimal invariant subtree `𝒯_0`.
- If `G` fixed an end `ξ`, the Busemann character `G → Z` at `ξ` would be a homomorphism. It is trivial, since
  `G` is simple and nonabelian. But hyperbolic elements fixing `ξ` have nonzero character, a contradiction.
- The action on `𝒯_0` is minimal.

**Step 2: item 1.**
- `G` is infinite and simple, so it is not virtually cyclic: the core of a finite-index infinite cyclic
  subgroup would be a nontrivial proper normal subgroup, or `G ≅ Z`.
- `G` is not acylindrically hyperbolic.
- By Minasyan–Osin applied to `𝒯_0`, `Pst_G{u, v}` is infinite for all vertices `u, v` of `𝒯_0`.

**Step 3: item 2.**
- For an edge `e` of `𝒯_0` and `g ∈ G`, `G_e ∩ g G_e g^(-1) = G_e ∩ G_(ge)` is the pointwise stabilizer of
  `e ∪ ge`, since there are no inversions.
- In a tree this equals the pointwise stabilizer of the geodesic spanned by `e ∪ ge`, which is `Pst_G{x, y}`
  for its two extreme vertices `x, y`. This is infinite by Step 2. So `G_e` is s-normal, and in particular
  infinite.
- If `[G : G_e] < ∞`, the normal core of `G_e` would have finite index, so it would equal `G`. Then `G` would
  fix `e`, which is excluded. So the index is infinite.

**Step 4: item 3.** Peterson–Thom `main2` applies to `H = G_e`.

**Step 5: item 4.**
- `Γ` acts properly and cocompactly on the connected, locally finite complex `T_1 × T_2`, so it is finitely
  generated (Švarc–Milnor).
- Replace `T_1` by its barycentric subdivision, so that `Γ` acts without inversions. `Γ` fixes no vertex `x` of
  `T_1`. Otherwise `Γ` would preserve each set `{y : d(x, y) = m} × T_2`, and cocompactness would bound `T_1`.
- For an edge `e` of `T_1`, the stabilizer `Γ_e` acts on `T_2`. The stabilizer of a vertex `v` of `T_2` in it
  fixes the cell `e × v`, so it is finite by properness.
- `Γ` has finitely many orbits of cells of `T_1 × T_2`. An element carrying `e × σ` to `e × σ'` fixes `e`,
  so `Γ_e` has finitely many orbits on `e × T_2`.
- So `Γ_e` acts properly and cocompactly on the tree `T_2`. It is finitely generated and virtually free, and
  `β_1^(2)(Γ_e) < ∞`. Item 3 gives `β_1^(2)(Γ) = 0`.

*Consistency remark.* For `Γ` a Burger–Mozes group, `Γ_e` is free of finite rank, with `β_1^(2)(Γ_e) > 0`. So
the vanishing is not inherited from the edge group, and the Cheeger–Gromov criterion (infinite normal amenable
subgroup) does not apply either, `Γ` being simple and nonamenable. The input is s-normality alone.
