# Referee report (citation/hypothesis-match lens): `sl-n-q-is-colimit-of-lattice-stabilizers`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: the node as landed at 624b0aee3, and §2 of
`research/artifacts/gq-gq-k2-q-uniformity.md` at the same commit. Requested by gq-k2-q: quote imports (I2), (I3)
at source, and check steps 1–2.

## Verdict

**PASS, conditional on amendments A1 and A2 below.** A3 is wording only. The mathematics is correct. The node
may say ESTABLISHED once A1 and A2 are in.

The one citation/hypothesis mismatch is in (I3). For `|S| >= 2`, `X_S` is a product of simplicial complexes, so it
is polysimplicial, not simplicial. The simplicial statements (Soulé 1973; Brown 1984 Theorem 1′ as transcribed
below) do not apply to it word for word. The standard repair (A1) costs one paragraph and changes no group in the
diagram.

## Steps 1, 2 and 5 (lane proofs), checked line by line

**Step 1: density and orbits. Correct.**
- Density of `Z[1/S]` in `∏_{p∈S} Q_p`. Given `(a_p)`, take `m = ∏_{p∈S} p^N` with `m a_p ∈ Z_p` for all
  `p ∈ S`; the primes of `m` other than `p` are units in `Z_p`. By CRT choose `z ∈ Z` with `z ≡ m a_p mod
  p^{N+k}`. Then `z/m ∈ Z[1/S]` and `|z/m − a_p|_p <= p^{-k}`.
- So the closure of `Γ_S` contains the product root groups `e_ij(∏ Q_p)`. The subgroup they generate is
  `E_n(∏_p Q_p) = ∏_p E_n(Q_p) = ∏_p SL_n(Q_p) = G_S`: a finite product of rings, and `SL_n = E_n` over a field.
- Stabilizers in `G_S` of cells of `X_S` are compact open. So for `g ∈ G_S` the coset `g·Stab(σ)` meets
  `Γ_S`, and `Γ_S`-orbits of cells equal `G_S`-orbits.

**Step 2: strict fundamental domain and stabilizers. Correct.**
- `SL_n(Q_p)` preserves types (`det = 1`), and it is transitive on chambers (the affine BN-pair with the Iwahori
  subgroup).
- So each face of `X_p` is equivalent to exactly one face of `Δ_p`: a chamber has one face of each type set.
- Taking products, `C_S` is a strict fundamental domain for `G_S`, and for `Γ_S` by step 1.
- A type-preserving element that stabilizes a cell fixes the cell's vertices in each factor, so it fixes the
  cell pointwise.
- Vertex stabilizers:
  - `L_c ⊗ Z_p = Z_p^{n-k} ⊕ (pZ_p)^k`, with `k = k_p(c)`, because the `c_i` are squarefree and form a
    divisibility chain. These `n` lattices are the vertices of the standard chamber.
  - For `SL_n`, the stabilizer of a lattice class is the stabilizer of the lattice: `gL = p^m L` forces
    `v_p(det g) = mn`, so `m = 0`.
  - A lattice in `Q^n` is determined by its localizations, and for `p ∉ S` we have `L_c ⊗ Z_p = Z_p^n`. So
    `Stab_{Γ_S}(c) = SL(L_c) = Γ_c` for `c` supported on `S`. Conversely `Γ_c ⊆ SL_n(Z[1/S])`.
- The same argument gives, for every cell,
  `Γ_F = ∩_{c ∈ F} Γ_c = SL_n(Q) ∩ ∏_p P_{F_p}`,
  where `P_{F_p}` is the pointwise stabilizer of the face `F_p` of `Δ_p` in `SL_n(Q_p)`, and
  `P_{{0}} = SL_n(Z_p)`.

**Step 5: directed union. Correct.**
- `P_S` is the poset of faces of `C_S`, that is, the cells with `F_p = {0}` for `p ∉ S`. It is closed under
  faces.
- `P = ∪_S P_S` is a directed union, and every relation `F ⊆ F'` lies in some `P_S`, since it involves finitely
  many primes. So `colim_P = colim_S colim_{P_S}`.
- `Γ_F` is intrinsic (`∩ Γ_c`), so the transition maps are the inclusions `Γ_S ⊆ Γ_S'`. Their union is `SL_n(Q)`.

## Import (I2): Euclidean buildings are CAT(0), hence contractible

**Source read.**
- L. Kramer, *On the local structure and the homology of CAT(κ) spaces and euclidean buildings*,
  arXiv:1009.3089, §6.4(a), read on ar5iv, verbatim: "A euclidean building is a (not necessarily complete)
  CAT(0) space."
- There it is attributed to Tits, with references to Tits (1986), Kleiner–Leeb (1997) and Parreau (2001). The
  metric realization of the Bruhat–Tits building of `SL_n(Q_p)` is a euclidean building in that sense.
- Caveat: the quote is as returned from the ar5iv HTML rendering. I did not cross-check it against the PDF.

**Not read at source.**
- Bridson–Haefliger II.10A.4, which is cited for the same fact in several papers in the search results.
- Abramenko–Brown Theorem 11.16.
- Both are books; no open copy was reachable.

**CAT(0) implies contractible.** This is elementary, so no import is needed. Fix `x_0`. Put `H(y,t)` = the point
at fraction `t` along the unique geodesic from `y` to `x_0`. The CAT(0) comparison gives
`d(H(y,t), H(y',t)) <= (1−t) d(y,y')`, so `H` is continuous. (This is Bridson–Haefliger II.1.5, not read here.)

**Topology and products.**
- `X_p` is locally finite, since the residue field is finite. For a locally finite complex the metric topology
  agrees with the CW topology.
- `X_S` is a finite product of contractible spaces, so it is contractible.
- The node needs only simple connectivity, and the CAT(0) property of the product is not used.

**A2 (required).** Replace "(I2, standard)" by this citation:
- Kramer §6.4(a), quoted as above;
- or Bridson–Haefliger II.10A.4, marked "not read at source";
- plus the one-line geodesic contraction.

## Import (I3): colimit of stabilizers over a strict fundamental domain

**Found, through secondary transcriptions only.** Brown's paper (J. Pure Appl. Algebra 32 (1984), 1–10) itself
returned HTTP 403, so I did not read it.
1. **arXiv:2603.25586, Theorem 2.1**, attributed to K. S. Brown, "Presentations for groups acting on …
   complexes", J. Pure Appl. Algebra 32 (1984), Theorem 1′. As transcribed:
   - Hypotheses: `G` acts on a **simplicial** complex `K` with a subcomplex `W` such that
     1. `K` is simply connected;
     2. each simplex of `K` is equivalent mod `G` to a unique simplex of `W`;
     3. `W` has finite 2-skeleton;
     4. each vertex stabilizer `G_v` is finitely presented;
     5. each edge stabilizer `G_e` is finitely generated.
   - Conclusion: `G` is the fundamental group of the graph of groups on the 1-skeleton of `W`, with vertex and
     edge stabilizers, modulo `y_e = 1` for every edge `e` of `W`. That is the amalgam of the vertex groups along
     the edge groups.
2. **arXiv:2412.04250v2 (Iveson), Theorem 1.2.2**, attributed to "Brown [5], Theorem 3". As transcribed:
   - "Let 𝒢 act on a simply connected 𝒢-CW complex X (without inversion on the 1-cells of X). Suppose there is a
     subcomplex W of X so that every cell of X is equivalent under the action of 𝒢 to a unique cell of W. Then 𝒢
     is generated by the isotropy subgroups 𝒢_v (v∈V(W)) subject to edge relations ι_{o(e)}(g)=ι_{t(e)}(g) for all
     g∈𝒢_e (e∈E(W))."
   - Warning: two fetches of that paper's bibliography disagreed on whether its [5] is Brown 1984 or Brown,
     "Finiteness properties of groups" (1987). So do not cite "Theorem 3" until someone reads the primary.

**Not read.**
- Soulé, C. R. Acad. Sci. Paris Sér. A 276 (1973), 607–609. No copy was reachable. Its title, "Groupes opérant
  sur un complexe simplicial avec domaine fondamental", says it is about simplicial complexes.
- Bridson–Haefliger Corollary II.12.22, which other papers cite for this statement.

**Hypothesis match against the node.**
- Hypotheses (1), (3), (4), (5) hold:
  - `X_S` is contractible (I2);
  - `W = C_S` is finite;
  - vertex groups are `Γ_c ≅ SL_n(Z)`, which is finitely presented;
  - edge groups are finite-index congruence subgroups, so finitely generated.
- Hypothesis (2) holds (step 2).
- **Mismatch:** hypothesis "`K` simplicial". For `|S| >= 2`, `X_S` is a product of simplices, so it is
  polysimplicial, not simplicial. For `|S| = 1` it is simplicial and there is nothing to fix.

**A1 (required): the repair.** It adds no vertices and changes no group.
1. Each `X_p` has vertices typed by `{0,…,n−1}`, and the types totally order the vertices of each simplex.
2. The product of ordered simplicial complexes has the canonical staircase (Eilenberg–Zilber) triangulation:
   - its vertices are the vertices of `X_S`;
   - its simplices are the chains in the coordinatewise order inside a product cell.
3. `Γ_S` preserves types, so it acts simplicially on this triangulation `K`. An element stabilizing a simplex
   fixes it pointwise.
4. Every simplex `τ` of `K` has a smallest carrier cell `σ(τ)`. So "each simplex of `K` is equivalent to a unique
   simplex of `W`" (the triangulated `C_S`) follows from step 2, as follows.
   - If `gτ` and `τ` both lie in `W`, then `gσ(τ)` and `σ(τ)` are faces of `C_S`.
   - By step 2 they are equal, and `g` fixes `σ(τ)` pointwise, so `gτ = τ`.
5. Brown's conclusion for `K` is a vertex–edge amalgam. Its edges are the comparable pairs `v < w` inside a cell,
   and the stabilizer of such an edge is `Γ_{F(v,w)}`, where `F(v,w)` is the smallest cell containing `v` and `w`.
   This amalgam equals the node's colimit over all cells:
   - every cell relation `Γ_F ⊆ Γ_v`, `Γ_F ⊆ Γ_w` factors along an edge path from `v` to `w` in the 1-skeleton
     of `F`, and `Γ_F` lies in each edge group on that path;
   - conversely, each staircase edge is the edge relation of the cell `F(v,w)`;
   - so the maps between the two colimits, induced by the vertex groups, are mutually inverse.

**Suggested citation text for (I3):**
- "Brown, J. Pure Appl. Algebra 32 (1984), Theorem 1′ (transcribed in arXiv:2603.25586, Thm 2.1; primary not
  read), applied to the staircase triangulation of `X_S`";
- Soulé 1973 and Bridson–Haefliger II.12.22 as secondary pointers, marked "not read".
- Drop "simply connected `Y`" from (I3): Brown's version needs no hypothesis on `W` beyond (2)–(3), and `C_S` is
  contractible anyway.

## A3 (wording only)

"the diagram is the restricted product over primes of one local diagram of the same shape" is accurate for the
**index poset**, which is the restricted product of the face posets of `Δ_p`. The **groups** are not products:
`Γ_F = SL_n(Q) ∩ ∏_p P_{F_p}`. Suggest saying exactly that.

## Also checked (correct)

- The Serre case, `SL_2(Z) ∩ diag(1,p) SL_2(Z) diag(1,p)^{-1} = Γ_0(p)`: conjugation gives
  `[[a,b/p],[pc,d]]`.
- The bijection between the `c`'s and the vertices of `∏'_p Δ_p`, given by
  `c_i = ∏_{p : k_p >= n−i+1} p`.
- `Γ_F` is a congruence subgroup of a conjugate of `SL_n(Z)` at the primes `p` with `F_p ≠ {0}`.

This node settles neither G nor G', and it is not a stepping stone listed in RULES §5. So one referee pass
suffices. This report does not review the claim's use in any host construction.
