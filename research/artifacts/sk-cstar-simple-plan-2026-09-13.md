# sk-cstar-simple: plan (2026-09-13)

Lane sk-cstar-simple (roster G). Target: is `G_X = EL_3(LC(X,F_2) ⋊_T Z)` C*-simple, for an infinite minimal subshift `X`?
Open node: `subshift-elementary-groups-are-cstar-simple`.

## Criteria, read at source on MSI (arXiv e-print TeX)
- Kennedy, arXiv:1509.01870v5, Theorem `thm:c-star-simple-iff-no-amenable-urs`: C*-simple iff no non-trivial amenable
  uniformly recurrent subgroups.
- Le Boudec–Matte Bon, arXiv:1605.01651v3, Theorem `thm-cstar-chab` (Kennedy's criterion restated): equivalently, the
  conjugacy class of every amenable subgroup accumulates at the trivial subgroup in `Sub(G)`. Since the basic neighbourhoods
  of `{1}` are `{K : K ∩ P = ∅}` for finite `P ⊆ G \ {1}`, this says: no amenable subgroup is confined.
- Le Boudec–Matte Bon, Theorem `thm-non-amenab-rigid-stab`: a countable group of homeomorphisms of a Hausdorff space whose
  rigid stabilizers of non-empty open sets are all non-amenable is C*-simple.

## Why the rigid-stabilizer theorem does not apply directly
`G_X` has no known faithful micro-supported action. Its natural actions are linear, and there rigid stabilizers of
proper open sets are trivial (Attempt 1 on the open node).

## Plan
1. Land the two criteria as import nodes.
2. Test subgroups (sk-strong-2's list), proving each is not confined:
   - root subgroups `e_ij(R)`: a sequence of conjugates with pairwise trivial intersections (done in this landing);
   - `L = GL_3(LC(X,F_2))`, which contains the locally finite union `EL_3(LC(X,F_2))`;
   - the algebraic AF subalgebra's elementary group;
   - `[[T]]'` via `diag(w,1,1)`.
3. Main route: a commutator lemma for confined subgroups of `G_X`, with idempotents in place of subsets.
   - **Supports.** Rigid subgroups `G_E = G ∩ (I + E M_3(R) E)` for idempotents `E ∈ M_3(R)`.
   - **Disjointness.** Orthogonality `EF = FE = 0`, which makes `G_E` and `G_F` commute.
   - **Displacement.** `gEg^{-1} ⊥ E`.
   - **Why idempotents.** Fibrewise elements such as `e_12(1)` move no clopen set, but they do displace rank-one idempotents over a small clopen
     set (for `I + E_12`: the image `span(e_1+e_2)` along `span(e_2,e_3)`).
   - **Tower corners.** For towers, `E` of rank ≥ 3 over a small base `W` has corner Morita equivalent to the first-return crossed
     product over `W`. So `G_E` contains `EL_3` of a minimal Cantor crossed product, which is infinite, simple and nonamenable.
   - **The conclusion.** If Le Boudec–Matte Bon's combinatorial argument transfers, a confined `H` contains a nontrivial subgroup of some `G_E`
     normalized by a subgroup of index ≤ |P|. Simplicity of the corner group then puts a nonamenable group inside `H`, so
     no amenable subgroup is confined, and `G_X` is C*-simple.
4. Record every dead end as Attempts on the open node.

## Not duplicating
- sk-strong-2 (not uniformly simple, unique trace);
- sk-cstar-mf (MF of `C*_r`);
- sk-characters-rigidity-a/b (characters).
