# One-ring push mutual link: the literal (★) fails, an absorbed-block family member embeds

swarm-0917-w17-w17-z-last1, 2026-09-19. Unreviewed notes.

This answers the open sub-question (★) of
`zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md` §7 (the w8 artifact). Notation is
that artifact's, with:
- `P = PLB_n = PΣAut_n` acting on `F_n = ⟨x_1, …, x_n⟩`;
- `A_ij : x_i ↦ x_j x_i x_j^{-1}`, all other generators fixed; products compose right to left;
- McCool relators (M1) `[A_ij, A_kl]`, (M2) `[A_ij, A_kj]`, (M3) `[A_ij A_kj, A_ik]`, over all
  index tuples with distinct letters;
- for disjoint blocks of rings X, J with block word `W_J` (the product of the `x_r`, r ∈ J, in
  block order), "X through J" is the automorphism `x_r ↦ W_J x_r W_J^{-1}` for r ∈ X, fixing the
  other generators. It is the product of the `A_rs` (r ∈ X, s ∈ J) in the evident order, and the
  factors for different r commute.
- `P_σ = κ_Γ(PLB_{n−m})` for a simplex σ of Q with ordered matching Γ. The pure cabling map `κ_Γ`
  sends "I through J" to "block(I) through block(J)" (colimit proof, Cor 5.2, with (F2) of the
  w8 artifact).

Fix free rings v, w, c. Put `b0 = [(v,w)]`, `b0' = A_vc b0`, `L = lk(b0) ∩ lk(b0')` in `X_n(F)`.
Here `lk(b0) ≅ X_{n−1}(F ∪ {f})`, with f the fused ring.

**(★), literal form.** Is L the part of `lk(b0)` whose types avoid c, a copy of
`X_{n−1}(F ∪ {f, c})` (free count N − 3)?

## 0. Results

1. **Invariant (proved).** For types u and z, `I(pP_u, qP_z) := rank(p(C_u) ∩ q(C_z))`, where
   `C_u := ⟨x_a x_b, x_k (k ≠ a, b)⟩` for `u = (a, b)`.
   - It is a well-defined P-invariant of pairs of vertices.
   - Adjacent pairs take the standard value.
   - So a nonstandard value certifies non-adjacency.
   - It detects the Whitehead-clasp obstruction (model artifact §3). No abelian invariant can
     separate the vertices it separates (§1).
2. **The literal (★) is false (proved, with an explicit certificate).**
   - The vertex `A_ca[(a, b)]` lies in `lk(b0)` and its type avoids c, but it is not in `lk(b0')`.
   - This holds for every n ≥ 5 and every F.
   - Of the one-generator vertices of `lk(b0)`, exactly those moving a or b "the wrong way" fail
     (§2).
3. **Absorbed-block embedding (proved).**
   - Define `θ : PLB_{[n]∖{v,w}} → P` by `A_cj ↦ B_j := A_cj A_vj A_wj` (the block {v,w,c}
     through j), with every other `A_ij ↦ A_ij`.
   - θ is an injective homomorphism into `P_vw ∩ C_P(A_vc, A_wc)`.
   - It induces a simplicial embedding `Φ : X_{n−2}(F ∪ {c}) ↪ L`, where `X_{n−2}(F ∪ {c})` is on
     the rings `[n]∖{v, w}` and has **free count N − 3**, the same as the literal candidate.
   - The image lies in `⋂_{k ∈ Z} lk(A_vc^k b0)`.
4. **Conjecture (★′), strong evidence.** `L = Φ(X_{n−2}(F ∪ {c}))`. Evidence:
   - 5040 of 5040 random vertices of `lk(b0)` (n = 6, 7) pass the rank test exactly when they lie
     in the image of Φ, as far as the necessary model test can tell;
   - 0 of 1274 random vertices of type meeting c pass.

   Surjectivity reduces to one statement about `P_vw ∩ ker π` (§4).
5. **Consequence for CS.**
   - For the Björner nerve criterion (w8 §5.2.3) at t = 1, pairs related by a one-ring push
     contain a family member of free count N − 3. Under (★′) they equal one.
   - The bound needed is `c(N − 3) ≥ η(N) − 1`, and it holds, since `η(N−3) = η(N) − 1`.
   - Pairs related by longer pushes absorb bigger blocks and lose more free count, so they break
     the criterion as stated. A refined nerve is required (§5).

## 1. The free-factor invariant

**Lemma 1.1.** For `u = (a, b)`, `P_u` stabilizes `C_u`, i.e. `φ(C_u) = C_u` for `φ ∈ P_u`.

*Proof.* Check the Cor 5.2 generators of `P_u`:
- `A_ij` with `i, j ∉ {a, b}`: it conjugates one `x_k` by some `x_j`, and `x_j ∈ C_u`.
- The ring `i` through the block {a, b}: `x_i ↦ (x_a x_b) x_i (x_a x_b)^{-1}`.
- The block through `j`: `x_a x_b ↦ x_j x_a x_b x_j^{-1}`, with every `x_k` (k ≠ a, b) fixed.

Each maps the generating set of `C_u` into `C_u`, and so does its inverse. Hence equality. ∎

(This is also checked by machine for all u at n = 6, 7, 8: `one_ring_push.py` (0).)

**Corollary 1.2.** `I(pP_u, qP_z) := rank(p(C_u) ∩ q(C_z))` is well defined on pairs of vertices.
It is invariant under the left P-action, since `r(A) ∩ r(B) = r(A ∩ B)`.

If the vertices `p[u]` and `q[z]` span an edge, then by strictness of Q that edge is `r·{[u], [z]}`.
So `p ∈ rP_u`, `q ∈ rP_z`, and `I = I_std(u, z) := rank(C_u ∩ C_z)`. **A nonstandard value certifies
non-adjacency.**

Ranks of intersections are computed with Stallings graphs, as the base component of the pullback
(`stallings.py`).

**Calibration** (`one_ring_push.py` (1)).
- Take the model-artifact §3 clasp `[1,(1,2)]`, `[α_13,(3,4)]` and its variants
  (`A_13^{±1}`, `A_31^{±1}`, `A_14`, `A_32`): all give 3 against the standard value 4 (n = 6).
- 40 random adjacent pairs give the standard value.

**Why abelian invariants cannot see what I sees.**
- `g[(a,b)]` is adjacent to `h[(v,w)]` iff `h^{-1} g ∈ P_vw P_ab`.
- For the vertices of §2, `h^{-1} g = A_vc^{-1} A_ca`. Here `A_vc^{-1} ∈ P_ab` and `A_ca ∈ P_vw`, so
  `h^{-1} g ∈ P_ab P_vw`.
- Its image in every abelian quotient therefore lies in the image of `P_vw + P_ab`. Only the
  **order** of the two factors is wrong.
- So the obstruction is invisible to the exponent-sum invariant `e` of the model artifact, and to
  the abelianized colimits of w8 §6.

## 2. Result A: the literal (★) is false

**Proposition 2.1.** Let `n ≥ 5`, let v, w, c, a, b be distinct free rings, and put
`u = A_ca[(a, b)]`. Then:
- `u ∈ lk(b0)`;
- `t(u) = (a, b)` avoids c;
- `u ∉ lk(b0')`, where `b0' = A_vc b0`.

The same holds with `A_vc` replaced by `A_vc^{-1}` or `A_wc^{±1}`.

*Proof.*
1. `A_ca` is a Cor 5.2 generator of `P_vw`, because `c, a ∉ {v, w}`. So `u = A_ca[(a,b)]` lies in
   `A_ca lk(b0) = lk(b0)`.
2. Certificate at n = 5, with (v, w, c, a, b) = (1, 2, 3, 4, 5):
   - `A_ca(C_ab) = ⟨x4x5, x1, x2, x4x3x4^{-1}⟩`;
   - `A_vc(C_vw) = ⟨x3x1x3^{-1}x2, x3, x4, x5⟩`.

   Their intersection has rank 2, with basis `x4x5` and `x5^{-1}x3x5`. The second basis element is
   `(x4x5)^{-1}(x4x3x4^{-1})(x4x5)`. The standard value is `rank(C_ab ∩ C_vw) = 3`.
3. For `n > 5`, the extra generators `x_k` (k ≥ 6) are fixed by `A_ca` and `A_vc`, and they lie in
   both subgroups.
   - Each Stallings graph is the n = 5 graph with one extra loop per k at the base, and the letter
     `x_k` occurs nowhere else.
   - So in the pullback, the only `x_k`-edges are loops at the base.
   - Both the computed rank and the standard rank go up by `n − 5`: they are `n − 3` and `n − 2`.
4. The other pushes are checked by machine for n = 6, 7, 8 (`one_ring_push.py` (2)).
5. F plays no role, since the invariant does not depend on it. ∎

So L is **not** the full "types avoiding c" part of `lk(b0)`. The literal identification with
`X_{n−1}(F ∪ {f, c})` fails.

**Census of one-generator vertices** (`one_ring_push.py` (2), n = 6, 7, 8, all four pushes).
Take `u = g[(a, b)]`, with g a Cor 5.2 generator of `P_vw` and `{a, b} ∩ {v, w, c} = ∅`.

u fails the rank test (so `u ∉ lk(b0')`) for exactly 6 generators per type, which gives the counts
36, 72, 120. For `k ∈ {a, b}` they are:
- c through k (`A_ck`);
- k through the fused ring f (conjugation of `x_k` by `x_v x_w`);
- f through k (`A_vk A_wk`).

Every other generator passes, and so does the product `B_k = A_ck A_vk A_wk` (the block {v,w,c}
through k). In words: in L, ring c may pass through a or b only together with the block
{v, w}. That is the absorbed block.

## 3. Result B: the absorbed-block embedding

Let `R = [n] ∖ {v, w}` and `P'' = PLB_R` (n − 2 rings, c among them). Define θ on McCool
generators of `P''`:

  `θ(A_cj) = B_j := A_cj A_vj A_wj` (the block {c, v, w} through j),  `θ(A_ij) = A_ij` for `i ≠ c`.

The three factors of `B_j` commute pairwise, by (M2). Let `π : P → P''` be induced by
`F_n → F_R`, `x_v, x_w ↦ 1`.
- π is well defined: each `φ ∈ P` maps `x_v, x_w` to conjugates of themselves, so it preserves
  their normal closure, and the induced automorphism is again basis-conjugating.
- `π(A_ij) = A_ij` if `i, j ∈ R`, and `π(A_ij) = 1` otherwise.

**Lemma 3.1.** θ is a homomorphism, and `π ∘ θ = id`. In particular θ is injective.

*Proof.*

1. **Relators with no generator `A_kc`** (c never a second index). Let `κ_{cvw}` be the pure
   cabling map from `P''` into P that fattens ring c into the block {c, v, w}.
   - Concretely, `A_cj ↦` (block {c,v,w} through j), and every other generator is fixed.
   - This is the ring-level substitution of the preamble, and it is a homomorphism.
   - θ agrees with `κ_{cvw}` on every generator except `A_kc`, so these relators map to 1.
2. **Relators containing some `A_kc`**, going through the McCool families.
   - (M1) `[A_kc, A_ij]` with `{i, j} ∩ {k, c} = ∅`: i ≠ c, so the image is the same relator.
   - (M2) `[A_kc, A_lc]`: the image is the same relator.
   - (M3) `[A_ij A_kj, A_ik]` contains `A_kc`-type letters only when j = c or k = c.
     - j = c: `[A_ic A_kc, A_ik]` with i, k ≠ c. The image is the same relator.
     - k = c: `[A_ij A_cj, A_ic] ↦ [A_ij B_j, A_ic] = [X Y, Z]`, with `X = A_ij A_cj`,
       `Y = A_vj A_wj` and `Z = A_ic`. Here `[X, Z] = 1` is (M3), and `[Y, Z] = 1` by (M1), since
       v, w, j, i, c are distinct. So `[XY, Z] = 1`.
3. **π ∘ θ.** `π(B_j) = A_cj · 1 · 1`, and π fixes the other `θ(A_ij)`. ∎

Machine check of all relator images for n = 6, 7: `orbit_check.py` (a).

**Lemma 3.2.** `θ(P'') ⊆ P_vw ∩ C_P(A_vc) ∩ C_P(A_wc)`. Hence, for every `h ∈ ⟨A_vc, A_wc⟩`,
`θ(P'') ⊆ Stab(b0) ∩ Stab(h b0)`.

*Proof.*
- **Containment in `P_vw`.** `A_ij` (i, j ∈ R) is a Cor 5.2 generator of `P_vw`. So is `A_cj`, and
  so is `A_vj A_wj` (the fused ring through j). Hence `B_j ∈ P_vw`.
- **Commuting with `A_vc`.**
  - `A_ij` with `i, j ∈ R ∖ {c}`: (M1).
  - `A_kc`: (M2).
  - `B_j = (A_vj A_cj) A_wj`, using (M2) to reorder: `[A_vj A_cj, A_vc] = 1` is (M3) with
    (i, k) = (v, c), and `[A_wj, A_vc] = 1` is (M1).
- **Commuting with `A_wc`.** Symmetric.
- **The stabilizer.** `Stab(h b0) = h P_vw h^{-1} ⊇ h θ(P'') h^{-1} = θ(P'')`. ∎

Machine check: `orbit_check.py` (b) and `absorbed_block.py` (the sanity line).

**Lemma 3.3 (cabling compatibility).** Let Γ be an ordered matching on `R ∖ {c}`, with m edges.
Let `θ'` and `π'` be the maps defined by the same formulas one cabling level down: on
`PLB_{n−m}` and `PLB_{n−2−m}`, with the rings v, w, c unfused. Then:
- `θ ∘ κ''_Γ = κ_Γ ∘ θ'`;
- `π ∘ κ_Γ = κ''_Γ ∘ π'`.

Consequently, for every simplex σ of Q whose types avoid {v, w, c}: `θ(P''_σ) ⊆ P_σ` and
`π(P_σ) ⊆ P''_σ`.

*Proof.* Check on a generator "I through J" (blocks of the lower level).

1. **θ.**
   - If I ≠ {c}, neither side changes it: the image is "block(I) through block(J)", a product of
     `A_rs` with r ≠ c.
   - If I = {c}, let block(J) = (s_1, …, s_p). Then
     `θ κ''_Γ(A_cJ) = B_{s_1} ⋯ B_{s_p}` and `κ_Γ θ'(A_cJ) = κ_Γ(A_cJ A_vJ A_wJ)`.
   - The second is (c through block J)(v through block J)(w through block J), which equals
     `(A_{c s_1} ⋯ A_{c s_p})(A_{v s_1} ⋯)(A_{w s_1} ⋯)`.
   - Reorder: `A_{v s_i}` and `A_{w s_i}` commute with `A_{c s_j}` (j ≠ i), and `A_{v s_i}` commutes
     with `A_{w s_j}` (j ≠ i), all by (M1). Same-letter factors `A_{c s_i}, A_{v s_i}, A_{w s_i}`
     commute by (M2). Neither move changes the relative order of the `A_{c ·}`, the `A_{v ·}` or the
     `A_{w ·}`.
   - So the product equals `∏_i (A_{c s_i} A_{v s_i} A_{w s_i}) = ∏_i B_{s_i}`.
   - If J = {c} (c through-ring), both sides give "block(I) through c".
2. **π.** Both sides kill a generator whose I or J is {v} or {w}. Otherwise both give
   "block(I) through block(J)" on R.
3. **Consequence.** `P_σ = κ_Γ(PLB_{n−m})` and `P''_σ = κ''_Γ(PLB_{n−2−m})`. ∎

**Theorem 3.4 (absorbed-block embedding).** Let `X'' := X_{n−2}(F ∪ {c})`, on the ring set R, with
free count `N − 3`. Then

  `Φ : X'' → X_n(F)`,  `p''σ ↦ θ(p'')σ`  (σ ∈ Q'' = Q ∩ {types avoiding F ∪ {v, w, c}})

is a well-defined, θ-equivariant, injective simplicial map. Its image lies in
`⋂_{h ∈ ⟨A_vc, A_wc⟩} lk(h b0)`, and in particular in `L = lk(b0) ∩ lk(A_vc b0)`.

*Proof.*
1. **Well defined.** `P''` acts on `X''` with strict fundamental domain `Q''` (F1 at level n − 2,
   restricted to the invariant subcomplex). If `p_1''σ = p_2''σ`, then `p_2''^{-1} p_1'' ∈ P''_σ`,
   and Lemma 3.3 gives `θ(p_2'')^{-1} θ(p_1'') ∈ P_σ`. Faces go to faces, so Φ is simplicial.
2. **Injective.** Suppose `θ(p_1'')σ_1 = θ(p_2'')σ_2`.
   - Types are P-invariant and Q is strict, so `σ_1 = σ_2 = σ`, and `θ(p_2'')^{-1} θ(p_1'') ∈ P_σ`.
   - Apply π, using Lemma 3.1 and Lemma 3.3: `p_2''^{-1} p_1'' ∈ π(P_σ) ⊆ P''_σ`.
   - So `p_1''σ = p_2''σ`. Hence Φ is injective on simplices, and it is an isomorphism onto the
     subcomplex `Φ(X'')`.
3. **Image.**
   - Every σ ∈ Q'' lies in `lk_Q([(v,w)])`, because its pairs avoid v and w.
   - Every `h ∈ ⟨A_vc, A_wc⟩` lies in `P_σ`, because for each edge (a, b) of σ, `A_vc` and `A_wc`
     are unfused-ring generators with `{v, c} ∩ {a, b} = ∅` (Lemma 3.3 form).
   - So `σ = hσ ∈ h lk(b0) = lk(h b0)`.
   - Then Lemma 3.2 gives `θ(p'')σ ∈ θ(p'')(lk(b0) ∩ lk(h b0)) = lk(b0) ∩ lk(h b0)`. ∎

**Remarks.**
- `A_vc A_wc` is "the fused ring f through c", which lies in `P_vw`. So `⟨A_vc, A_wc⟩ b0` is
  the single `Z`-orbit `{A_vc^k b0}`, and Φ lands in the intersection of all its links.
- Geometrically, L contains every configuration obtained from `lk(b0)` by first fusing the
  fused ring f with c: ring c "absorbs" the block {v, w}.
- The free count `N − 3` agrees with the literal (★). The complex is different, though: it has
  n − 2 rings with c forbidden, instead of n − 1 rings with f and c forbidden.

Also checked by machine (`orbit_check.py` (c)): 0 of 1274 random vertices `g[u]`, with
`g ∈ P_vw` and u a type meeting c, pass the rank test against `A_vc b0`.

## 4. Conjecture (★′) and the remaining gap

**Conjecture (★′).** `L = lk(b0) ∩ lk(A_vc b0) = Φ(X_{n−2}(F ∪ {c}))` for all n and F. So L is a
family member of free count N − 3.

**Lemma 4.1 (membership criterion).** Let `u = g σ`, with `g ∈ P_vw` and `σ ∈ Q''`. Then
`u ∈ Φ(X'')` iff `u = θπ(g) σ`.

*Proof.*
- (⇐) This is clear.
- (⇒) Suppose `u = θ(p'')σ` (types force the same σ). Then `g^{-1}θ(p'') ∈ P_σ`, so
  `π(g)^{-1} p'' ∈ P''_σ` by Lemma 3.3. Hence `θπ(g)σ = θ(p'')σ = u`. ∎

**Reduction of (★′).** Take `u = gσ ∈ L`.
- If the type of u meets c, (★′) says this cannot happen. That half is supported by the 0/1274
  census in §3.
- Otherwise write `g = θπ(g) · g'`, with `g' ∈ K := P_vw ∩ ker π`. Since `θπ(g)` preserves L
  (Lemma 3.2), `g'σ ∈ L`.
- By Lemma 4.1 (with π(g') = 1), `u ∈ Φ(X'')` iff `g'σ = σ` iff `g' ∈ P_σ`.

So (★′) is equivalent to the following two statements.

> **(K)** For `g' ∈ P_vw ∩ ker π` and `σ ∈ Q''`: if `g'σ ∈ lk(A_vc b0)`, then `g' ∈ P_σ`.
> **(C)** No vertex of L has a type meeting c.

These are statements about double cosets in P. K is the subgroup of `P_vw` generated, as a normal
subgroup, by the moves involving v or w (Cor 5.2 generators other than the `A_ij` with i, j ∈ R).
An attack on (K) would combine two things:
- a Stallings-fold normal form for `g'(C_ab)`;
- the fact that `π(g'(C_ab)) = C''_ab`.

**Evidence** (`absorbed_block.py`, seeds 919 and 20260919).
- The test applies to random words g of length 1–4 in the `P_vw` generators and types
  (4,5), (5,4), (4,6), with (v, w, c) = (1, 2, 3).
- It compares:
  - (i) the rigorous rank test "u may be in `lk(b0')`";
  - (ii) the necessary condition `g(C_ab) = θπ(g)(C_ab)` for `u = θπ(g)[(a,b)]`, i.e. for
    `u ∈ Φ(X'')` (Lemma 4.1).

| n | seed | pass / eq | fail / neq | mismatches |
|---|---|---|---|---|
| 6 | 919 | 815 | 985 | 0 |
| 6 | 20260919 | 739 | 1061 | 0 |
| 7 | 919 | 386 | 334 | 0 |
| 7 | 20260919 | 427 | 293 | 0 |

Together that is 5040 of 5040 samples. "Rank passes" ⟺ "model equality holds" on every sample,
so the rank invariant appears to be **complete** for membership in L.

It is not a proof: (i) is only necessary for u ∈ L, and (ii) is only necessary for u ∈ Φ(X'').

## 5. What this means for the Coning Statement

1. **The t = 1 Björner condition for one-ring pushes.** The w8 nerve criterion (§5.2.3) with
   `k = η(N)` needs `lk(b0) ∩ lk(b1)` to be `(k−1)`-connected.
   - For `b1 = A_vc^{±1} b0` or `A_wc^{±1} b0`, Theorem 3.4 gives a family member of free count
     `N − 3` inside the intersection. Under (★′) it is the whole intersection.
   - By the inductive hypothesis of the w8 reduction (§4), that member is
     `c(N − 3) = η(N − 3) = η(N) − 1 = k − 1` connected. So the one-ring pushes satisfy the t = 1
     condition exactly, with no slack. This matches the 1/3 slope of w8 §6.
2. **All pairs do not behave this way (caveat).** For `b1 = h b0` with h a longer word, the same
   construction absorbs a bigger block.
   - Take `h = A_vc A_vd`, a push of v through two rings.
   - The analogous θ fattens c and d. It gives a family member of free count `N − 2 − 2 = N − 4`
     at best, which is below `k − 1` for many N.
   - This is a heuristic count, not proved. Such pairs are nonetheless nonempty intersections, so
     they are edges of the nerve 𝒩.
   - So the **plain Björner nerve over all b fails** unless these deeper intersections are larger
     than their absorbed-block part.
3. **Decomposition this suggests** (each piece can fail on its own).
   - (D1) (★′) for one-ring pushes, i.e. (K) + (C).
   - (D2) A Morse-type ordering of the type-{v, w} vertices, by push length from b0 inside the
     `ρ`-fibre, whose descending links meet only through one-ring pushes. This is the BFMWZ 3.10
     pattern: push α over w one step at a time.
   - (D3) Higher intersections along a one-ring chain `b0, A_vc b0, A_vc A_wd b0, …` are iterated
     absorbed-block family members, with free count dropping by 3 per step, matching the `(k − t)`
     requirement.

4. **Relation to the w11 clasp obstruction.** `zp-loop-braid-cx-antisymmetric-clasp-obstruction-2026-09-18.md`
   shows that the Φ-levels of type-(a,b) vertices are separated only by the stars of distinct
   (v,w)-vertices. By its Lemma 2.2(2), the type-(a,b) vertices of `lk(A_va b0)` have
   `Φ = φ_ab(A_va) = −1`, and those of `lk(b0)` have `Φ = 0`. So the one-ring pairs
   `(b0, A_va b0)`, with c = a, are exactly the nerve edges that join adjacent Φ-levels. This
   artifact gives their mutual link on the types avoiding a: an absorbed-block member, where the
   triple-cable mechanism of w9 is unavailable.

   (D1)–(D3) together would give CS(N). (D1) is the step with no 2D analogue that w8 §7 isolated.
   It is now reduced to the double-coset statements (K) and (C), which are testable by computer.
