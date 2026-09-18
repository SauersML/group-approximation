---
rg: 2
id: a2-lattices-carry-finite-type-seeds
kind: claim
title: Every lattice acting simply transitively on the vertices of a thick Ã2 building carries a finite-type seed, the origin-projection SFT; seed idempotents are classical in every quantum family, and its rigidity would contain that of the chamber-boundary shift
requires:
  - tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts
distinct_from:
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that defines SFT compactifications (seeds) and glues them over free products, with members only finite groups, Z and their products and free products; this produces one over a one-ended Kazhdan lattice, where no splitting exists.
  euclidean-building-boundary-shifts-are-quantum-rigid: that is the open rigidity of the chamber-boundary shift X_Ω; this shows X_Ω is a subshift of the seed, so a rigid seed of this shape would prove it.
  a2-busemann-transplants-preserve-quantum-rigidity: that decorates a boundary skeleton over chambers at infinity, which has no isolated point; this codes a vertex field, whose origin is an isolated point with trivial stabilizer.
  a2-lattice-boundary-skew-shifts-are-quantum-rigid: that gives a rigid topologically free SFT (the boundary skew product P); this gives the seed axioms (isolated dense orbit, trivial stabilizer), with rigidity left open.
---

**ESTABLISHED** (lane proof, bh-emitter-b, 2026-09-18; elementary building geometry; not reviewed; no
priority claimed). Items 1–4 are proved. Rigidity of the seed is open:
`a2-lattice-phase-seeds-are-quantum-rigid`.

## Setting

- **Building and lattice.** `Δ` is a locally finite thick Ã2 building of order `q`, and
  `Γ ≤ Aut(Δ)` acts simply transitively on its vertex set `V`. Examples are the CMSZ groups: they
  are type rotating, finitely presented, one-ended and Kazhdan.
  - Identify `V` with `Γ`. The finite set `S` of `s` with `s·1` adjacent to `1` generates `Γ`, and the
    Cayley graph is the 1-skeleton.
  - Neighbours of `x` of relative type `+1` are the *points* of the projective plane `Lk(x)`, and
    those of relative type `−1` are its *lines*. Type-rotating automorphisms preserve relative type,
    so `γ^(-1)` identifies `Lk(γ)` with `Lk(1)`.
- **Vector distance.** For `o, x ∈ V`, `σ(o, x) = (m, n) ∈ N²`: in any apartment containing both,
  `x = o + mω_1 + nω_2`. Here `ε_1, ε_2, ε_3` (summing to 0) are the type `+1` steps,
  `ω_1 = ε_1` and `ω_2 = −ε_3`. Graph distance is `d = m + n`.
- **The label.** `a_o(x)` is the simplex of `Lk(x)` whose relative interior contains the germ of the
  geodesic `[x, o]`, and `a_o(o) = *`. It is:
  - a flag `(p_0, ℓ_0)` iff `m, n >= 1`;
  - the line `ℓ_0 = x − ε_1` iff `n = 0 < m`;
  - the point `p_0 = x + ε_3` iff `m = 0 < n`.

  The *genuine field* of `o` is `y_o(γ) = γ^(-1)·a_o(γ)`. The alphabet `𝒜` is `{*}` together with
  the simplices of `Lk(1)`.
- **The SFT.** `Y_Γ ⊆ 𝒜^Γ` is the set of configurations whose pattern on every star `γ·B_1` occurs in
  some genuine field. Then `y_* = y_1`, the seed pattern is `*` at `1`, and `(g.y)(h) = y(g^(-1)h)`.

## Theorem

1. **(S1), (S2).** The only `y ∈ Y_Γ` with `y(1) = *` is `y_1`, and `Stab(y_1) = 1`. So `Γ·y_1` is
   open and discrete.
2. **(S3).** `Y_Γ` is the orbit closure of `y_1`. So `(Y_Γ, *)` is an SFT compactification (a seed) of
   `Γ` in the sense of `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`.
3. **Seeds are classical.** In every `D`-quantum family (`D >= 1`, any field) for `Y_Γ`, put
   `S_e = E_*(e)`. Then `S_e ≤ E_(y_e(u))(u)` for every `u`. So each `S_e` commutes with every letter,
   and `S_e S_(e') = 0` for `e ≠ e'`.
4. **Refinements.** The phase seed `Y_Γ^(N)` is defined in the same way from the labels
   `(a_o(x), σ(o, x) mod N)`, for `N >= 1`. It is also a seed, and it factors onto `Y_Γ`.
5. **What rigidity would contain (hand remark).**
   - For subshifts `Z ⊆ Y` over the same alphabet, every `D`-quantum family for `Z` is one for `Y`,
     since patterns missing from `Y` are missing from `Z`. So `Y` being `D`-rigid makes every
     subshift `D`-rigid.
   - `X_Ω ⊆ Y_Γ` (Step 6). So `D`-rigidity of `Y_Γ` implies
     `euclidean-building-boundary-shifts-are-quantum-rigid` for these lattices, which is open.
   - Similarly `Y_Γ^(N)` contains the phase-coded boundary `Ω × (Z/N)²`. For the `N` of
     `a2-lattice-boundary-skew-shifts-are-quantum-rigid`, its minimal pieces are phase translates of
     the rigid `P` (the lag conventions there were not re-checked).

## Proof

**Step 0 (local tables).** Let `x ≠ o`, and let `A` be an apartment containing `o` and `x`. Use the
retraction `ρ` onto `A` centred at a chamber of `A` containing `o`. It preserves `σ(o, ·)` and maps
`Lk(x)` onto the hexagon `Lk_A(x)` by the retraction of the projective plane centred at a chamber
through `a_o(x)`. Computing in `A` gives the change `σ(o, y) − σ(o, x)` for each neighbour `y`,
which depends only on `a = a_o(x)`:
- **`a = (p_0, ℓ_0)` (regular).**
  - Points: `p_0` gives `(0,−1)`; the other points on `ℓ_0` give `(−1,+1)`; points off `ℓ_0` give
    `(+1,0)`.
  - Lines: `ℓ_0` gives `(−1,0)`; the other lines through `p_0` give `(+1,−1)`; lines not through
    `p_0` give `(0,+1)`.
- **`a = ℓ_0` (`n = 0`).** Points on `ℓ_0` give `(−1,+1)` and points off it `(+1,0)`; `ℓ_0` gives
  `(−1,0)` and the other lines `(0,+1)`. The case `a = p_0` is dual.

Call a neighbour **outward**, **sideways** or **inward** according as `d` changes by `+1`, `0` or `−1`.
The inward neighbours are exactly the vertices of `a`.

**Step 1 (outward determination).** For outward `y`, the label `a_o(y)` is a function of `a` and `y`.
- Its type comes from `σ(o, y) = σ(o, x) + change`. It is regular, except that for `a = ℓ_0` a point
  off `ℓ_0` stays on the wall (dually for `a = p_0`).
- Its vertex set is the set of inward neighbours of `y`. That is `x`, together with, when `y` is
  regular, the unique `z` adjacent to both `x` and `y` that is sideways for `x`. Concretely:
  - `y` a point off `ℓ_0`: `z` is the line `p_0 y`;
  - `y` a line not through `p_0`: `z` is the point `y ∩ ℓ_0`;
  - wall case `a = ℓ_0`, `y` a line `≠ ℓ_0`: `z` is the point `y ∩ ℓ_0`;
  - wall case, `y` a point off `ℓ_0`: `y` is again of wall type, with label `x`.
- Two points span one line and two lines meet in one point, so `z` is unique. At `*` every
  neighbour is outward, with a wall label pointing back. So for `η ∈ Y_Γ` and a site `x` with label
  `a`: the outward neighbours (read off `a`) carry forced labels.
- Changes along an edge are antisymmetric, because both labels lie in one genuine star. Hence `y` is
  outward from `x` iff `x` is inward from `y`.

**Step 2 (S1).** Let `η(1) = *`. The star of `1` is genuine for a field whose label at `1` is `*`,
i.e. for `y_1`. Every vertex `w` lies on a graph geodesic from `1`, and each step of that geodesic is
outward in `y_1`. By induction along the geodesic with Step 1, `η(w) = y_1(w)`. Since `Γ` acts freely
on `V`, `Stab(y_1) = 1`.

**Step 3 (descents).** Write `w -> w'` if `w'` is a vertex of `η(w)`, i.e. `w'` is inward. Let
`U(w) = {v : w ->* v}` and let `Out(z)` be the set reached by outward steps.
- By Step 1, `w ∈ Out(z)` iff `z ∈ U(w)`.
- By Step 1 again, `η|_(Out(z))` is a function of `η(z)` alone.
- **Diamond.** If `x -> p_0` and `x -> ℓ_0`, the star of `p_0` is genuine for some `y_o''`, and `y_o''`
  agrees with `η` on `x`, `p_0` and `ℓ_0`. In `y_o''` the vertex `u = x − ω_1 − ω_2` (computed in an
  apartment through `[x, o'']`) is adjacent to both and inward from both. It lies in the star of
  `p_0`, so `p_0 -> u` and `ℓ_0 -> u` in `η`. By the diamond lemma, `->*` is confluent.
- **Adjacent pairs.** Adjacent `w, w'` have a common descendant. Either one is inward from the other,
  or `w'` is sideways. In the sideways case, `ℓ_0` (for points on `ℓ_0`) or `p_0` (for lines through
  `p_0`) is inward from both, read off the star of `w`.

**Step 4 (S3).** Let `η ∈ Y_Γ` have no `*`, and fix `R`.
- **A common descendant.** List `B_R(1)` so that each vertex is adjacent to an earlier one. Adjacent
  common descendants and confluence give, by induction, one `z ∈ ⋂_(w ∈ B_R(1)) U(w)`. So
  `B_R(1) ⊆ Out(z)`.
- **A matching field.** Every label occurs in a genuine field at every site: realize a flag or wall
  simplex at `z` inside an apartment and put `o` at `σ = (1,1)`, `(1,0)` or `(0,1)`. So choose `o`
  with `y_o(z) = η(z)`.
- **Agreement.** By Step 3, `y_o` and `η` agree on `Out(z) ⊇ B_R(1)`. So `η` is a limit of
  translates of `y_1`. With Step 2, `Y_Γ = closure(Γ·y_1)`.

**Step 5 (seeds are classical).** Let `v'` be outward from `v` for the label `a`, and let `b` differ
from the forced label. Then every `D`-pattern on `B_D(v)` with `a` at `v` and `b` at `v'` is missing
from `Y_Γ`. Summing (Q3) over extensions (all letters of the ball commute) gives
`E_a(v) E_b(v') = 0`, so `E_a(v) ≤ E_(forced)(v')`.
- Along a geodesic from `e` to `u`, every step is outward in `y_e`. Transitivity of `≤` (as in
  `free-group-boundary-shift-is-quantum-rigid`, Step 2) gives `S_e ≤ E_(y_e(u))(u)`.
- Hence `E_b(u) S_e = S_e E_b(u)`, which is `S_e` or `0`.
- `y_e(e') ≠ *` gives `S_e ⊥ S_(e')`.

**Step 6 (X_Ω inside).** Let `c ∈ Ω` and `x ∈ V`. The sectors `Q(w, c)`, for `w` in the star of
`x`, contain a common subsector. Take `o` deep inside it, away from its walls. For each such `w`,
`o − w` lies in the open cone of an apartment containing `Q(w, c)`, so
`a_o(w) = germ_w Q(w, c) = x_c(w)`. So every star pattern of `x_c` is genuine, and `x_c ∈ Y_Γ`.
**Step 7 (phases).** For `Y_Γ^(N)` the phase change along an edge is the change of Step 0 mod `N`.
- Steps 1–5 go through verbatim.
- In Step 4, choose `o` deeper in the same apartment, at `σ(o, z)` in the prescribed residue classes.
  A wall label forces residue `0` in its zero coordinate, and the alphabet is by definition the
  set of labels that occur.
- In Step 6, choose `o` in the common subsector with prescribed residues of `σ(o, x)`. `∎`

## Consequences

- **Tree gluing without rigidity (hand check).** Items 1–2 (minimality, topological freeness) of
  `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts` use only (C1), (C2) and branching.
  So `Γ * Z` carries a minimal, topologically free SFT for every such `Γ`. That is the minimality
  and topological-freeness half of (★′) over a Kazhdan vertex group. Rigidity of that SFT is item 3 there, which needs a rigid seed.
- **Where the difficulty is.** Seed idempotents are central (item 3), so noncommutativity of any
  quantum family lives on the seedless part `∂Y = Y ∖ Γ·y_1`. That part is an SFT: forbid `*`.
  Its strata (a description, not proved) are:
  - the chamber stratum `X_Ω` (or its phase cover);
  - two wall strata, fields toward a vertex at infinity with one finite coordinate.

## Lesson for general BH

Finite-type seeds are a link-local phenomenon. Outward labels are forced by projective-plane
incidence (two points span a line, two lines meet), and descents form a confluent diamond system. So a
one-ended Kazhdan lattice has an isolated, dense, trivially stabilized orbit in an SFT. Kazhdan
geometry does not obstruct (IE′); the only open part of rung 1d is rigidity. Rigidity there is
exactly a boundary problem: seeds are automatically classical, and a rigid seed makes every subshift
rigid, including `X_Ω`. So the seed should carry the phase `σ mod N`, whose chamber stratum is the
already rigid `P`, and the remaining work is the two wall strata.

## Referee (bh-ref-kourovka-b, 2026-09-18): PASS

**Verdict: PASS** for items 1–4, and for item 5 as stated. Lane bh-emitter-b's construction is correct
and uses only link geometry. It applies to the CMSZ groups (Cartwright–Mantero–Steger–Zappa).
- **Step 0.** I recomputed the tables in an apartment, including the wall case via the `A_2` Weyl
  reflection, for example `mω_1 − ω_2 ↦ (m−1)ω_1 + ω_2`. They are correct. So is the retraction
  centred at a chamber containing `o`, which preserves `σ(o, ·)` and restricts to the plane
  retraction centred at the flag.
- **Step 1.** The forced outward labels come from unique point–line incidence (`z = p_0 y` or
  `y ∩ ℓ_0`, both sideways). Antisymmetry holds via one genuine star. Correct.
- **Steps 2–4.**
  - The diamond (`u = x − ω_1 − ω_2`, read in the field matching the star of `p_0`) is a one-step
    diamond, so confluence needs no termination argument.
  - BFS gives a common descendant for all of `B_R(1)`.
  - Every label occurs as `y_o(z)` for a suitable `o`.
  - So `Y_Γ` is the orbit closure of `y_1`, and `y_1` has a trivial stabilizer.

  Correct.
- **Step 5.** Chains of projection inequalities `E_a(v) ≤ E_forced(v')` make each `S_e` central,
  with `S_e ⊥ S_{e'}`. Correct.
- **Step 6.** `o` deep in a common subsector gives `x_c ∈ Y_Γ`. Correct.
- **Note.** The Setting's appeal to type-rotation is only notational. Every step is equivariant
  under all of `Aut(Δ)`, since `g·y_o = y_{go}`. So the title's "every lattice acting simply
  transitively on vertices" is fine.
