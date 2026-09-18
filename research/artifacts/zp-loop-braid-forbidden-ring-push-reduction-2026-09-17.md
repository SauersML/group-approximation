# Loop braid descending links: forbidden-ring family and reduction to one coning statement

swarm-0917-w8-w8-z-last1, 2026-09-17. Unreviewed notes.

Target: `loop-braid-descending-links-are-increasingly-connected`, i.e. connectivity of
`X_n := L_n(LB_*)` goes to infinity (WZ Prop. 5.9 input for Zaremsky 2.12).

Conventions follow `zp-loop-braid-descending-links-model-2026-09-13.md` (§1–2) and
`pure-loop-braid-group-is-colimit-of-cabling-stabilizers-proof.md`:
- `P = PLB_n`, and `Q ≅ OM(K_n)` is the strict fundamental domain;
- the type map `t: X_n → Q` is the simplicial retraction `[g,Γ] ↦ [s_g,Γ]`;
- a vertex of `Q` is an ordered pair `(a,b)` of distinct rings in `[n]`.

## 0. Summary

1. **Family.** For `F ⊂ [n]`, let `X_n(F) := t^{-1}(OM(K_{[n]∖F}))`.
   - This is the P-invariant full subcomplex on vertices whose type avoids `F`.
   - Its free count is `N := n − |F|`, and `X_n = X_n(∅)`.
2. **Link Lemma (§2, proved).** For every simplex σ of `X_n(F)` with m edges,
   `lk_{X_n(F)}(σ) ≅ X_{n−m}(F' ∪ Fus_σ)`, where `F'` is the image of F and `Fus_σ` is the set of m
   fused rings. The free count drops by 2m.
3. **Base cases (§3, proved from established results).**
   - `X_n(F)` is connected for `N ≥ 5`.
   - `X_n(F)` is simply connected for `N ≥ 8`.
   - Both hold for every `n` and every `F`.
4. **Reduction (§4, proved).** Fix distinct free rings `v, w`, and let `Y = Y_n(F; v, w)` be the full
   subcomplex of `X_n(F)` on vertices whose type meets `{v, w}` in `∅` or in all of `{v, w}`. Put
   `η(N) := ⌊(N − 5)/3⌋`. Then:

   **the Coning Statement "`Y_n(F; v, w)` is `η(N)`-connected for all `n, F, v, w` with `N ≥ 11`"**

   implies that `X_n(F)` is `η(N)`-connected for all `N ≥ 5`, and hence closes the target.
   Only the single degree `j = η(N)` with `η(N − 2) < η(N)` is actually needed (§4.4).
5. **How CS relates to the Push Lemma (§5).** The Push Lemma PL says the inclusion
   `X_n(F ∪ {v, w}) ↪ X_n(F)` kills `π_j`.
   - CS implies PL.
   - PL is equivalent to the target (given §2–§4), so PL alone is only a restatement.
   - CS is strictly more structured and can fail on its own. At the key degree it says the push
     already happens at the `q = 3` stage.
6. **Computation (§6).** Abelianized colimits of the stabilizers were computed for n ≤ 9.
   - They reproduce the established colimit theorem for N = 7, 8.
   - They show `H_1(colim_{Q_Y}) = Z^{n(n−1)} ⊕ (3-torsion of rank 2)` at N = 7, for every n.
   - Hence `π_1(Y) ≠ 0` at N = 7, and `X_n(F)` is **not simply connected at free count 5** (every n ≥ 7).
   - So the base values `c(5) = 0` and `η(7) = 0` are sharp in degree 1. CS(8), CS(9) pass the H_1
     test.
7. **Structure of Y (§5).** `Y` has strict fundamental domain `Σ OM(K_{N−2})`, the suspension with
   the two cone points `(v, w)` and `(w, v)`.
   - A nerve-lemma criterion reduces the Coning Statement to connectivity of the intersections
     `lk(b_0) ∩ … ∩ lk(b_p)` of links of type-`{v, w}` vertices. This is the exact analogue of the
     BFMWZ Thm 3.10 step `lk(α) ∩ lk(α')`.
   - §7 records the geometric step that has no 2D analogue.

## 1. Facts used (all established in the graph)

- (F1) **Strict fundamental domain, all n.** `P` acts on `X_n` with strict fundamental domain `Q`.
  - `t(p·τ) = t(τ)`, and `t` restricts to the identity on `Q`.
  - `Stab_P([1,Γ]) = (PLB_{n−m})κ_Γ`. It fixes the simplex pointwise, and `κ_Γ` is injective.
  - Sources: model artifact §2; colimit proof, step 1.
- (F2) **Cabling composes.** `κ_{Γ ⊔ Δ} = κ_{Δ̄} ∘ κ_Γ`, where `Δ̄` is the matching of `L_{n−m}` that
  Δ becomes after contracting the edges of Γ. For matchings, WZ define `κ_Γ` as the iterated
  composite of the `κ_k`, and (CS2) makes the order irrelevant.
- (F3) **Dangling bijection (V-level).** `lk_Q([1,Γ])` is the set of `[s,Γ ⊔ Δ]` faces complementary
  to `[1,Γ]`. It is identified with `Q_{n−m}(Fus_Γ) = OM(K_{R_Γ ∖ Fus_Γ})`, where:
  - `R_Γ` is the ring set at level `n − m`: the unfused rings, plus one fused ring per edge of Γ;
  - `λ_Γ` is the ring relabelling that carries unfused rings bijectively to the non-fused rings of
    level `n − m`.

  This is the symmetric-group statement for Thompson's V: the link of an m-simplex in `OM(K_n)` is
  `OM(K_{n−2m})`, on the complementary rings.
- (F4) **McCool / colimit ingredients.** Colimit proof steps 2–4: the relators, Lemma 5.1, (C1)
  and (C3).
- (F5) **Morse lemma** (BFMWZ Lemma 2.5 / Cor. 2.6, Bestvina–Brady). Suppose:
  - `X^0 ⊂ X` is a full subcomplex;
  - every vertex outside `X^0` gets a height, with vertices of equal height non-adjacent;
  - each descending link `lk(u) ∩ X_{<u}` is `(k−1)`-connected, where `X_{<u}` is the full
    subcomplex on `X^0` together with the lower vertices.

  Then `(X, X^0)` is k-connected.

## 2. Link Lemma

**Lemma 2.1.** Let `σ = [1,Γ] ∈ Q` have m edges. Then:
- `lk_{X_n}(σ) = Stab_P(σ) · lk_Q(σ)`;
- there is a `κ_Γ`-equivariant simplicial isomorphism `lk_{X_n}(σ) ≅ X_{n−m}(Fus_Γ)` that carries
  types to types via `λ_Γ`.

For a general simplex `g·[s,Γ]`, transport by `g s`: s normalizes `P`, and types are relabelled by
`ρ(s)`. Consequently, for `σ ⊂ X_n(F)`:

  `lk_{X_n(F)}(σ) ≅ X_{n−m}(λ_Γ(F) ∪ Fus_Γ)`,  with free count `N − 2m`.

*Proof.*

1. **The link is `P_σ · lk_Q(σ)`.** Let `τ'` be a simplex of `lk_X(σ)`. By (F1), `σ ∪ τ' = p·ω` for
   a unique `ω ∈ Q` and some `p ∈ P`.
   - Then `p^{-1}σ` is a face of `ω`, so it lies in Q (Q is a subcomplex).
   - Since `p^{-1}σ` and `σ` are P-equivalent simplices of Q, strictness gives `p^{-1}σ = σ`, so
     `p ∈ P_σ`.
   - Hence `τ' = p·τ` with `τ := ω ∖ σ ∈ lk_Q(σ)`.
2. **The link is the development of a complex of groups.** Pointwise fixing and strictness,
   applied inside the P_σ-set `lk_X(σ)`, give
   `lk_X(σ) = (⊔_{τ ∈ lk_Q σ} P_σ/P_{σ∪τ} × τ)/~`, with the obvious face identifications.
   - This is the basic construction D(lk_Q σ, P_{σ∪·}) of Bridson–Haefliger II.12.18 for a simple
     complex of groups.
   - It is determined up to equivariant isomorphism by the poset `lk_Q σ` and its family of
     subgroups `P_{σ∪τ}` of `P_σ`.
3. **Identify the data at level `n − m`.** `X_{n−m}(Fus_Γ)` is the development of
   `Q_{n−m}(Fus_Γ)` with groups `P'_{τ̄} ⊂ P' = PLB_{n−m}`. This is (F1) at level `n − m`,
   restricted to the invariant subcomplex. Then:
   - (F3) gives `lk_Q σ ≅ Q_{n−m}(Fus_Γ)` via `τ ↦ τ̄`;
   - `κ_Γ: P' → P_σ` is an isomorphism, by (F1);
   - for `τ = [1, Γ ⊔ Δ]` (the s-part is handled as in (F1)), (F2) gives
     `P_{σ∪τ} = (PLB_{n−m−|Δ|})κ_{Γ⊔Δ} = ((PLB_{n−m−|Δ|})κ_{Δ̄})κ_Γ = (P'_{τ̄})κ_Γ`.
4. **Conclude.** The isomorphic data give isomorphic developments. Types match because both sides
   are the P- or P'-invariant extension of `λ_Γ` on the fundamental domains. Restricting to type
   avoiding F gives the `X(F)` statement. ∎

**Remark.** This is the statement the model artifact needed for "links of simplices are of the same
kind", which a Morse or induction argument uses. The family is closed under links, and only the
free count matters for the bounds below.

(In step 3, when `τ = [s, Γ ⊔ Δ]` with a nontrivial permutation braid `s = (s̄)κ_Γ`, conjugate using
the transport rule `(w g w^{-1})κ = (w)κ (g)κ ((w)κ)^{-1}` from colimit proof step 3. The cabling
map is a homomorphism on pure elements.)

## 3. Base cases for the family

**Lemma 3.1.** `X_n(F)` is connected whenever `N = n − |F| ≥ 5`.

*Proof.* `X_n(F) = P · Q_F`, where `Q_F = OM(K_{[n]∖F})`, is connected for `N ≥ 5`: `M(K_5)` is
connected, and the 2-point fibres are joined through any disjoint pair. It is standard that `P·Q_F`
is connected when `Q_F` is connected and `P` is generated by vertex stabilizers of `Q_F`.
- Every McCool generator `A_ij` lies in `P_{(a,b)}` for some pair `(a,b)` of free rings avoiding
  `{i, j}`, by (C1) with `w` omitted (colimit proof step 4, first bullet).
- Such a pair exists when `N − 2 ≥ 2`. ∎

**Lemma 3.2.** `X_n(F)` is simply connected whenever `N ≥ 8`.

*Proof.* Rerun colimit proof step 5 with `Q_F` in place of `Q`. Only vertices of `Q_F` are used as
receptacles, and the bounds involve only N:
- `φ(A_ij) := ι_v(A_ij)` for a free pair v avoiding `{i, j}`.
  - The free pairs avoiding `{i, j}` span `OM(K_{N'})` with `N' ≥ N − 2 ≥ 5`, which is connected.
  - (C1) makes consecutive choices agree, so φ is independent of v.
  - Indices of `{i, j}` lying in F only help.
- Each relator involves at most 4 indices, so a free pair avoiding them exists (`N − 4 ≥ 2`). Hence
  φ is a homomorphism `P → colim_{Q_F}`, and it is left inverse to ψ.
- Onto: for each generator h of `P_v` (v a free pair), take a free w avoiding `{a, b} ∪ S(h)`.
  Since `|S(h)| ≤ 2`, this needs `N ≥ 6`. Then (C3) applies verbatim.

So `colim_{Q_F} P_σ = P` for `N ≥ 7`. `Q_F ≅ OM(K_N)` is simply connected for `N ≥ 8`, as used in
the established n ≥ 8 result. The covering criterion (artifact Prop. 3.1 of
`loop-braid-desc-links-simply-connected-via-colimit`) applied to the P-action on `X_n(F)`, with
strict fundamental domain `Q_F`, gives simple connectivity. ∎

**Remark.** The P-action on the invariant subcomplex `X_n(F)` still has strict fundamental domain
`Q_F`, since `t` restricts. The stabilizers are the same cabling subgroups of the big group
`PLB_n`, not of `PLB_N`. So the family is not just a copy of `X_N`: forbidden rings still braid
through everything.

## 4. Reduction theorem

Let `c(N)` be the infimum, over all `n` and `F` with `n − |F| = N`, of the connectivity of `X_n(F)`.

### 4.1 The Morse step

Fix distinct free rings `v, w`. For a vertex u of `X_n(F)`, let `q(u)` depend on how its type pair
meets `{v, w}`:

| type meets `{v, w}` in | `q(u)` |
|---|---|
| nothing | 0 |
| `{v}` only | 1 |
| `{w}` only | 2 |
| both, i.e. type `(v,w)` or `(w,v)` | 3 |

Set `X^0 := X_n(F ∪ {v, w})`, the full subcomplex on `q = 0`. Adjoin the remaining vertices in the
height order `3 < 1 < 2`. Vertices of equal height share a ring, so they are not adjacent. Every
neighbour of u has a type disjoint from u's.

The descending links, by Lemma 2.1:

| q(u) | which neighbours are lower | descending link | free count |
|---|---|---|---|
| 3 | all neighbours have q = 0 | all of lk(u) ≅ X_{n−1}(F ∪ {f}) | N − 2 |
| 1, type (v,b) or (b,v) | only the q = 0 neighbours (q = 3 would reuse v; q = 2 is higher) | lk(u) ∩ {types avoid w} ≅ X_{n−1}(F ∪ {f, w}) | N − 3 |
| 2 | neighbours have q ∈ {0,1}, both lower | all of lk(u) | N − 2 |

By (F5):

  (4.1) `(X_n(F), X^0)` is `(min(c(N−2), c(N−3)) + 1)`-connected.

The intermediate stage after height 3 is exactly `Y := Y_n(F; v, w)`, the full subcomplex on
`q ∈ {0, 3}`. The same computation gives

  (4.2) `(X_n(F), Y)` is `(min(c(N−2), c(N−3)) + 1)`-connected.

### 4.2 Why (4.1) alone gives nothing

`X^0` has free count `N − 2`, so it is `c(N−2)`-connected. Therefore (4.1) only yields
`c(N) ≥ min(c(N−2), c(N−3) + 1)`. That is satisfied by a constant function. The whole difficulty
is one degree, which is exactly the "push" step of BFMWZ Thm 3.10 and of Putman's scheme.

### 4.3 Theorem

Let `η(N) := ⌊(N − 5)/3⌋`. Assume the

**Coning Statement CS(N).** For all `n, F` with free count N and all distinct free `v, w`,
`Y_n(F; v, w)` is `η(N)`-connected.

Assume CS(N) for every `N ≥ 11`. Then `X_n(F)` is `η(N)`-connected for all `N ≥ 5`. In particular
`conn L_n(LB_*) ≥ ⌊(n − 5)/3⌋ → ∞`.

*Proof.* Induct on N.
- **Base.** `N = 5, 6, 7` gives `η = 0` (Lemma 3.1). `N = 8, 9, 10` gives `η = 1` (Lemma 3.2).
- **Inductive step, `N ≥ 11`.** By induction, `c(N−2) ≥ η(N−2) ≥ η(N−3)` and `c(N−3) ≥ η(N−3)`.
  So by (4.2), `(X_n(F), Y)` is `(η(N−3) + 1) = η(N)`-connected.
  - Hence `π_j(Y) → π_j(X_n(F))` is onto for `j ≤ η(N)`.
  - CS(N) gives `π_j(Y) = 0`, so `π_j(X_n(F)) = 0` for `j ≤ η(N)`. ∎

### 4.4 Only one degree is needed

For `j ≤ η(N − 2)`, `π_j(Y) = 0` already follows from the induction:
- `Y` is obtained from the `c(N−2)`-connected `X^0` by coning off the subcomplexes `lk(b) ⊂ X^0`;
- the b are pairwise non-adjacent, so the cones `b * lk(b)` meet each other only inside `X^0` (the
  `lk(b)` may overlap);
- each `lk(b)` is `c(N−2)`-connected, by Lemma 2.1;
- coning off `c(N−2)`-connected subcomplexes of a `c(N−2)`-connected complex keeps it
  `c(N−2)`-connected (van Kampen and Mayer–Vietoris / Hurewicz).

So CS(N) is new content only in the single degree `j = η(N)`, and only when `η(N) > η(N − 2)`,
i.e. `N ≡ 0, 2 (mod 3)`. The first open instances are:
- `N = 11, 12` at `j = 2`;
- `N = 14, 15` at `j = 3`;
- and so on.

## 5. The Coning Statement: position and structure

### 5.1 CS versus the Push Lemma

Let `PL(N, j)` say that `π_j(X^0) → π_j(X_n(F))` is zero for all n, F, v, w with free count N.
- **PL is equivalent to the target.** By (4.1), `π_j(X^0) → π_j(X_n(F))` is onto for
  `j ≤ η(N)`. So PL, together with the induction, gives `π_j(X_n(F)) = 0`. Conversely, the target
  makes PL trivial. PL is therefore a restatement, not a reduction.
- **CS implies PL.** The map factors through `π_j(Y)`.
- **CS at the key degree.** Let `j = η(N) = η(N−2) + 1 ≤ c(N−2) + 1`.
  - `H_i(Y, X^0) = ⊕_b H̃_{i−1}(lk b)` vanishes for `i ≤ c(N−2) + 1`.
  - `X^0` is simply connected (`N − 2 ≥ 9`), so relative Hurewicz gives that
    `π_j(X^0) → π_j(Y)` is onto.
  - Hence CS at the key degree ⟺ `π_j(X^0) → π_j(Y)` is zero. In words: every j-sphere of `X^0`
    dies after coning off only the links of the type-`{v, w}` vertices.
- **CS is not implied by the target.** `(X, Y)` is only `η(N)`-connected, so
  `π_j(Y) → π_j(X)` need not be injective at `j = η(N)`. CS is a genuine prerequisite that can
  fail on its own.

### 5.2 Structure of Y

1. **Fundamental domain.** P acts on Y with strict fundamental domain
   `Q_Y = OM(K_{N−2}) * {(v,w), (w,v)} = Σ OM(K_{N−2})`. The two cone points are compatible with
   every pair avoiding `{v, w}`, and not with each other. Y is the development of `Q_Y` with the
   cabling stabilizers.
2. **Cover by stars.** Every simplex σ of `X^0` lies in `lk(b)` for some type-`{v, w}` vertex b:
   write `σ = p·σ_Q` and take `b = p·[(v,w)]`. Hence `Y = ⋃_b St(b)`, a cover by contractible
   closed stars. The b are pairwise non-adjacent, so for distinct `b_i`,
   `St(b_0) ∩ … ∩ St(b_t) = lk(b_0) ∩ … ∩ lk(b_t) ⊂ X^0`.
3. **Nerve criterion** (Björner, *Nerves, fibers and homotopy groups*, JCTA 102 (2003), Thm 6).
   Let `k = η(N)`, and let 𝒩 be the nerve of `{St(b)}`. Suppose:
   - every nonempty `lk(b_0) ∩ … ∩ lk(b_t)` (t ≥ 1, i.e. t+1 members) is `(k − t)`-connected;
   - 𝒩 is k-connected.

   Then Y is k-connected, i.e. CS(N) holds. This is the 3D analogue of the step "`lk(α) ∩ lk(α')`
   is highly connected" in BFMWZ Thm 3.10, where α' is α pushed over w.
4. **Annulus fibres are harmless.** Let `τ_b` be the cable twist of b (conjugating `x_v, x_w` by
   `x_v x_w`, transported by p).
   - `τ_b ∉ P_b`, but `τ_b ∈ P_u` for every u adjacent to b. This is the complete-join-over-annuli
     fact from the 2026-09-16 wave: `τ_j ∈ P_{v_i}` for `j ≠ i`.
   - So `τ_b` fixes `lk(b)` pointwise, and `lk(τ_b^k b) = lk(b)` for all k.
   - Hence every τ-orbit of b's spans a simplex of 𝒩, with intersection `lk(b)`, which is
     `c(N−2)`-connected.
   - So 𝒩 and the intersections may be computed on **annuli** (τ-orbits) instead of on vertices.
     The nontrivial intersections are between different annuli.

## 6. Computation: abelianized colimits

Script: `experiments/loop-braid-push-2026-09-17/abelian_colimit.py`. Output: `abelian_colimit_output.txt`.

**Method.**
- For a fundamental domain `D ∈ {Q_F, Q_Y}`, compute `H_1(colim_D P_σ)`:
  `(⊕_v Z^{A_pq on R_v}) / ⟨ι_u(x) − ι_{u'}(x) : x ∈ H_1(P_e)⟩`.
  - The edge-to-vertex maps are Lemma 5.1, abelianized: `A_pf ↦ A_pa + A_pb`, `A_fq ↦ A_aq + A_bq`.
  - Abelianization commutes with colimits. Triangle groups factor through edge groups.
- Ranks are taken mod 2, 3, 5, 7 and mod 1000003. Compare with `rank H_1(P) = n(n−1)`, which is
  torsion-free.

**Results.** The answer depends only on N, never on n.

| domain | N | (n, abs F) tested | H_1(colim) vs H_1(P) |
|---|---|---|---|
| Q_F | 6 | (6,0), (7,1) | extra Z/3-rank 1 |
| Q_F | 7 | (7,0), (8,1) | equal, torsion-free |
| Q_F | 8 | (8,0) | equal, torsion-free |
| Q_Y | 7 | (7,0), (8,1), (9,2) | **extra 3-torsion of rank 2** |
| Q_Y | 8 | (8,0), (9,1) | equal, torsion-free |
| Q_Y | 9 | (9,0) | equal, torsion-free |

- **Sanity.** The `Q_F`, `N = 7, 8` rows reproduce the established colimit theorem (n ≥ 7) in
  abelianized form, which checks the edge maps.

**Corollary 6.1** (proved, modulo the arithmetic). Let `N = 7`, with `v, w` free.
1. `Y_n(F; v, w)` is not simply connected, for every n.
   - `Q_Y = Σ OM(K_5)` is simply connected, since `OM(K_5)` is connected.
   - If Y were simply connected, then P would be the colimit of the stabilizers over `Q_Y`
     (Bridson–Haefliger II.12.20 / the covering criterion). This contradicts the extra torsion in
     `H_1`.
2. `X_n(F')` is not simply connected whenever `n ≥ 7` and the free count of `F'` is 5.
   - Take `F' = F ∪ {v, w}`.
   - `Y` is obtained from `X^0 = X_n(F')` by coning off connected subcomplexes `lk(b)` (free count
     5, Lemma 3.1), so `π_1(X^0) → π_1(Y)` is onto.

**What this changes.**
1. **The base cases are sharp in degree 1.** `c(5) = 0` exactly, at least for `n ≥ 7`.
2. **The torsion prime is 3,** as for matching complexes, where `H̃_1(M(K_7)) = Z/3` (Bouc;
   Shareshian–Wachs). This suggests the true connectivity slope is 1/3, and that no approach can
   give slope > 1/3 through this family.
3. **CS is consistent at every tested point.** CS(7) asks only for connectivity (true), while its
   degree-1 strengthening fails. CS(8) and CS(9) in degree 1 pass the `H_1` test. The failure at
   N = 7 shows that "coning off the q = 3 links raises connectivity by one" is **not** automatic.
   It needs `N − 2 ≥ 6` in degree 1, which is where the colimit argument on `Q_Y` starts to work:
   the pairs avoiding `{v, j}` then span `OM(K_{≥ N−3})` with `N − 3 ≥ 5`.

## 7. What remains, and the step with no 2D analogue

**Decomposition of the hole.**

| piece | status |
|---|---|
| (a) Link Lemma 2.1 | proved here |
| (b) Base cases 3.1 and 3.2 | proved here from established results |
| (c) Reduction Theorem 4.3 | proved here |
| (d) Coning Statement CS(N), N ≥ 11, in the one degree `η(N)` with `N ≡ 0, 2 (mod 3)` | **open** |

(d) is not implied by the target and could fail on its own (§5.1).

**Where the BFMWZ proof breaks.** In BFMWZ Thm 3.10 (2D), the push works as follows. Take the arc α
closest to w, slide it over w to get α', and identify `lk(α) ∩ lk(α')` with a smaller complex of
the same kind, by cutting the surface along α ∪ α' (★).

Here the analogue of α is a cabling annulus `A_b` between v and w. Compatibility of further annuli
with `A_b` is a global unlink condition, not disjointness: see the Whitehead-clasp obstruction,
model artifact §3. So (★) has no direct analogue. There is no cut-open manifold of the same type
whose annulus complex is `lk(b) ∩ lk(b')`.

**Open sub-question isolating (★).** For `b' = h·b` with h a single McCool generator `A_{vc}` or
`A_{wc}` (c free, `c ∉ {v, w}`), is `lk(b) ∩ lk(b')` a family member `X_{n−1}(F ∪ {f, c})` (free
count `N − 3`)? If so, and if these one-ring pushes suffice to make the nerve 𝒩 highly connected,
then CS follows. The first half is an equality of intersections of cabling subgroups,
`P_u ⊇ ⟨P_b ∩ P_{b'}⟩`-type, that can be tested with `cabling.py` (2026-09-16 experiment). Neither
half is done here.
