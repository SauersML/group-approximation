---
rg: 2
id: free-product-finite-factor-contracting-rsg-proof
kind: route
title: Atoms beyond a finite-factor letter are cones of one type, and translating by that letter plants every atom inside such a cone, so the type graph has an irreducible core
target: free-products-with-a-finite-factor-are-contracting-rsgs
requires:
  - hyperbolic-groups-embed-in-contracting-rsgs
artifacts:
  - research/artifacts/gq-bh-bh-free-23-rsg-q11.md
---

Lane `bh-free-23`, 2026-09-18. Lane proof, elementary, not reviewed. Source: BBMZ,
arXiv:2309.06224v3, TeX read at `gq/src/bh-free-03/bbmz2-2309.06224.tex`. Labels below are TeX
labels.

**Setting.** `K = G * F`, `S = S_G ∪ (F\{1})`, `G` nontrivial hyperbolic, `F` nontrivial finite,
not both of order 2. Word length is additive over normal-form syllables (a `G`-syllable `g`
costs `|g|_{S_G}`, an `F`-syllable costs 1). The Cayley graph is a tree of copies of
`Cay(G, S_G)` and of cliques `K_{|F|}` (the `F`-cosets), glued at single vertices. So every
vertex is a cut vertex separating its `G`-branch from its `F`-clique. `K` is hyperbolic, and
non-elementary because `(|G|,|F|) ≠ (2,2)`.

**Step 1 (F-cones are atoms of one type).** For `w` whose normal form ends in an `F`-syllable,
put `C(w) = {wh : h = 1 or the normal form of h starts with a G-syllable}`, the `G`-branch at
`w`. Let `n = |w|` and write `w = w'f` with `f ∈ F\{1}`.
- The whole clique `w'F` lies in `B_n`, and `C(w) ∩ B_n = {w}`.
- Every geodesic from `C(w)` to `B_n` passes through `w`, so all points of `C(w)` have the
  profile `d(·,w) + d(w,·)` on `B_n`, and `C(w)` lies in one atom `A`.
- Conversely, if `x` has that profile, then `d(x,w) < d(x, w'f')` for every other clique vertex
  `w'f'`. So `x` projects to `w` in the clique, and `x ∈ C(w)`. Hence `A = C(w) ∈ 𝒜_n(K)`.
- For two such words `w, w_2`, left multiplication by `w_2 w^{-1}` is an isometry
  `C(w) → C(w_2)` with `|w_2 w^{-1} x| = |x| − |w| + |w_2|`, and it maps descendant atoms to
  descendant atoms. The argument is BBMZ `lem:ConesAreAtoms` verbatim, which uses only this
  cut-vertex geometry. So all these atoms have one type `τ`.

**Step 2 (every atom contains a τ-descendant).** Let `A ∈ 𝒜_n(K)` with `n ≥ 1`, and pick
`a ∈ A` with `|a| ≥ n` (`A` is infinite).
- If `a` ends in a `G`-syllable or `a = 1`, take `f ∈ F\{1}`.
- If `a` ends in an `F`-syllable, take `g ∈ G\{1}` and use `ag` in place of `a`.

In either case the branch beyond `a` meets `B_n` only in `a`, and all its geodesics to `B_n` pass
through `a`. So `C(af)` (respectively `C(agf)`) lies in `A`, and it is a descendant atom of
type `τ` by Step 1.

**Step 3 (a τ-cone contains a copy of every type).** Let `D = {h : h = 1 or h starts with a
G-syllable}`. Each atom of level `≥ 1` lies in `D` or in one `C(f')`, `f' ∈ F\{1}`. Each
`C(f')` is itself a level-1 atom of type `τ`. Fix `f ∈ F\{1}`.
- **Setup.** Left multiplication by `f` is an isometry `D → C(f)` with
  `f(D ∩ B_n) = C(f) ∩ B_{n+1}`. Every geodesic from `C(f)` to its complement passes through `f`.
- **The image of an atom lies in one atom.** For an atom `A ⊆ D` of level `n ≥ 1` and `a ∈ A`:
  `d_{fa}(p) = d_a(f^{-1}p)` on `C(f) ∩ B_{n+1}`, and `d_{fa}(p) = d_{fa}(f) + d(f,p)` off `C(f)`.
  So `fA` lies in one atom `A' ∈ 𝒜_{n+1}`.
- **That atom is exactly `fA`.**
  - For `y ∈ C(f)`, `d(y,f) = d(y,1) − 1`.
  - For `x ∈ D`, `d(x,f) = d(x,1) + 1`.
  - For `x ∈ C(f'')` with `f'' ≠ f`, `d(x,f) = d(x,1)`.

  So every `x ∈ A'` lies in `C(f)`. Its translate `f^{-1}x ∈ D` has the profile of `A` on
  `B_n ∩ D`, and also on `B_n \ D`, where both paths pass through `1`. So `x ∈ fA`.
- **Conclusion.** The same holds for all descendants, so `f` is a morphism `A → fA`
  (BBMZ `def:morphisms`). This is BBMZ `lem:atoms_in_atoms` with `t` replaced by `f` and
  `C(t^{-1})` replaced by the `F`-branches at `1`.
- **Atoms outside `D`.** Atoms inside another `C(f'')` have copies in `C(f)` via the type-`τ`
  morphism `f f''^{-1}`.

So every non-root type occurs among the descendants of a `τ`-atom.

**Step 4 (the four conclusions).**
1. *No isolated points.* By Step 2 every atom contains a `τ`-atom. A `τ`-atom `C(f)` contains two
   disjoint infinite atoms: `C(fgf_1), C(fgf_2)` with `f_1 ≠ f_2` in `F\{1}` if `|F| ≥ 3`, and
   `C(fgf_1), C(fg'f_1)` with `g ≠ g'` in `G\{1}` if `|G| ≥ 3`. One of these holds, since not
   both orders are 2.
2. *Faithfulness.* A finite normal subgroup of `A * B` (both factors nontrivial) is conjugate
   into a factor, and conjugation by an element of the other factor moves it off that
   conjugate. So `K` has no nontrivial finite normal subgroup. BBMZ `rmk:horofunction_problems`,
   using Webster--Winchester, then gives a faithful action on `∂_h K`.
3. *Irreducible core.* By Steps 2 and 3, every node reaches `τ`, and `τ` reaches every non-root
   node, and also the root node if the root type recurs. So the core `Γ_0` (all nodes reachable
   from `τ`) is strongly connected. It is not a single cycle because `∂_h K` is infinite without
   isolated points. Only the root can lie outside `Γ_0`, and it has no incoming edges in that
   case. This gives conditions (i)–(iii) of the irreducible core definition (BBMZ, after
   `thm:ClassesVGammaE`).
4. *Contracting RSG.*
   - `K` is hyperbolic, so it has finitely many atom types (`prop:fin_many_types`).
   - With no isolated points, the induced action on `C_r` is rational (`thrm:BBM`), and its
     image is an RSG (`prop:hyp_similarities`).
   - The image has finite nucleus (`thrm:contracting`).
   - With the irreducible core it is contracting (`def:contracting`). By faithfulness it is
     isomorphic to `K`. ∎
