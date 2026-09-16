# Does L(G_X) ≅ L(G_Y) force G_X ≅ G_Y? Swarm session, 2026-09-16

- Agent: `swarm-subshift-group-factors-determi`.
- Hole worked: `subshift-group-factors-determine-subshift-groups`, the target, locked with a 180m TTL.
- Nothing committed. The referee lands.

## 0. Target and setup

- Let `X, Y` be infinite minimal subshifts, `A = LC(X,F_2)`, `R = A ⋊_T Z` and `G_X = EL_3(R)`. `G_X` is simple and
  has property (T).
- Question: does `L(G_X) ≅ L(G_Y)` imply `G_X ≅ G_Y`?
- In the graph at the start of the session the target was OPEN. Its `## Attempts` section already records:
  - separability counting;
  - character rigidity;
  - the observation that the diagonal is hyperfinite;
  - that deformation/rigidity has no entry point;
  - `Z ≤ Out`;
  - corner embeddings;
  - that commensurability degenerates for this family.

Graph claims used this session:
- `subshift-elementary-group-rigid-supports-are-mutual-centralizers`, reviewed PASS. Items: C1 span of `G_U − I`,
  C2 `C_G(G_U) = G_(X∖U)`, C3 `C_G(L_(X∖U)) = G_U`, C4 `L ≤ G` and `⋂ N_G(G_U) = L`.
- `locally-constant-simple-group-normal-subgroups-are-open-sets`, reviewed PASS.
- `subshift-group-factor-out-contains-z`, reviewed PASS: the automorphisms `θ_k = Ad diag(u^k,1,1)` of `G_X`.
- `icc-property-t-not-w-star-superrigid` and its artifact, which is the repo's record of Zhou's construction.

## 1. External literature gate (checked 2026-09-16)

**Tooling limit.** The session's web-search budget was exhausted (200 of 200) before the gate. The gate therefore used
only the arXiv API (`export.arxiv.org/api/query`, responses timestamped 2026-09-16 01:04–01:22 UTC), one source file
download, and repo search. MathSciNet, zbMATH and Google Scholar were not consulted, so the novelty audit is limited to
arXiv metadata and abstracts.

**Queries and hits.** Abstracts only, unless stated otherwise.
- **id 2608.02327v2**, S. Zhou, "ICC property (T) groups without W*-superrigidity", first version 2026-08-03.
  - Abstract: two explicit non-isomorphic ICC property (T) groups with isomorphic group von Neumann algebras; obtained
    with GPT-5.6 Sol assistance, concurrently with OpenAI.
  - Body not read in this session. The repo's reading of the manuscript (2026-08-19) is `Γ_i = D ⋊_(θ_i) H` with `D`
    normal elementary abelian, and a quadratic fibre shear on `D̂` identifies the two crossed products
    `L^∞(D̂) ⋊ H`.
- **`all:"Connes rigidity conjecture"`**, 7 hits:
  - 2608.14673v3 Sienicki–Sienicki (2026-08-03), an audit of the OpenAI results of 2026-08-01. Its abstract says later
    research confirms that Connes's rigidity conjecture is false.
  - 2608.02327v2 Zhou.
  - 2508.08194v3 Houdayer–Ioana (2025-08-11), on Weyl groups and lattices in semisimple groups.
  - 2503.12742v3 Chifan–Fernández Quero–Osin–Tan (2025-03-17), W*-superrigid property (T) groups with infinite centre.
  - 2410.11707v2 Houdayer (2024-10-15), the noncommutative Poisson boundary.
  - 1911.11729v2 Chifan–Das–Khan, Rips constructions.
  - math/0407103 Popa.
  - None concerns simple Kazhdan groups of the form `EL_n` over crossed products, or this question.
- **id 2511.23123v1**, Ariza Mejía–Chifan–Osin–Sun, "McDuff superrigidity for group II_1 factors" (2025-11-28). It is
  about McDuff factors. `L(G_X)` has (T), hence is full (Connes, recalled, not re-read), so it does not apply.
- **`all:"W*-superrigid" AND all:simple`**: 1 hit, 1603.07616 Gaboriau–Ioana–Tucker-Drob (cocycle superrigidity).
  Not applicable.
- **`all:"superrigid" AND all:simple`**: 17 hits, about lattices, cocycles, median spaces and similar topics. None is
  about group von Neumann algebras of simple groups.
- **`all:"topological full group" AND all:"von Neumann"`**: 2 hits.
  - 2507.18821v2 Bashwinger–DeBonis: CSS* groups, including topological full groups of SFTs; primeness, proper
    proximality.
  - 2311.08192v1 Kerr–Petrakos: `L(G)` is McDuff for subgroups of topological full groups containing the alternating
    group.
  - Both concern groups without (T). Contrast with the node of §2: there the support splitting
    `N_U ∨ N_(X∖U) ≅ N_U ⊗̄ N_(X∖U)` is irreducible, so it produces no central sequences.
- **`all:"relative commutant" AND all:"group von Neumann algebra"`**: 2 hits.
  - 2403.05948v3 Amrutam–Bassi, relative commutants in group and crossed product von Neumann algebras via contraction
    of measures; applied to negatively curved groups and `SL(d,Z)`.
  - math/0302082, solid von Neumann algebras.
  - At abstract level, neither overlaps with the support computation below.
- **`all:"elementary linear group" AND all:"von Neumann algebra"`**: 0 hits.
- **arXiv:1007.1412**, Ioana–Popa–Vaes, "A class of superrigid group von Neumann algebras".
  - The source file `superrigidity-group-vnalg22.tex` (gzip mtime 2012-08-20) was downloaded and §3 and §7 were read.
  - Numbering from the amsart counters: Theorem 3.1, the `dist(TΓ,TΛ) < √2` / height criterion; Theorem 3.3,
    symmetric dual 2-cocycles are coboundaries; Lemma 3.4; Proposition 3.5, countability for (T); Lemma 7.1,
    `Δ(u) = u⊗u` iff `u` is a group element.

**Status verdict.** The target is a question from the repo's own note, so no external page tracks it. No arXiv source
found on 2026-09-16 answers it, and it stays open. Zhou's mechanism does not transfer (§5.4).

**Novelty of the new node.** The Fourier finite-conjugacy-class argument is textbook. The contribution is its
application to `G_X`, combined with C3 and the normal-subgroup theorem for `LC(Z,Q)`. No novelty is claimed beyond
that.

## 2. Proven this session: support subalgebras are mutual relative commutants

- Claim `subshift-group-factor-supports-are-relative-commutants`.
- Route `subshift-group-factor-support-commutants-proof`, requiring the rigid-supports claim and the `LC(Z,Q)`
  normal-subgroup claim.
- Full proof in `research/artifacts/subshift-group-factor-support-commutants-2026-09-16.md`. Unreviewed.

With `M = L(G_X)` and `N_U = L(G_U)`, for all clopen `U, V`:
- `L(L_U)' ∩ M = N_U' ∩ M = N_(X∖U)`;
- `N_U ∩ N_V = N_(U∩V)` and `(N_U ∨ N_V)' ∩ M = N_(X∖(U∪V))`; `U ↦ N_U` is injective;
- each `N_U`, `U ≠ ∅`, is a II_1 factor, and `N_U ∨ N_(X∖U) ≅ N_U ⊗̄ N_(X∖U)` is irreducible;
- `L(GL_3(LC(X,F_2)))` is an irreducible hyperfinite II_1 subfactor of `M`;
- **transport:** `θ(L(L^X_U)) = L(L^Y_(U'))` forces `θ(N^X_U) = N^Y_(U')`.

Proof in one paragraph:
1. For `x ∈ L(L_U)' ∩ M`, the coefficient `x̂` is constant on `L_U`-conjugacy classes and square-summable. So each
   `g` in its support has a finite-index centralizer in `L_U ≅ LC(U,GL_3(F_2))`.
2. The normal core of that centralizer is `N_O` with `U∖O` finite. Distinct points outside `O` give `168^r` distinct
   cosets.
3. So `g` centralizes `L_V` for all clopen `V ⊆ U∖F`, and `g ∈ G_(X∖V)` by C3.
4. Since `X` has no isolated points, the finite set `F` is invisible to locally constant coefficients. So
   `⋂_V G_(X∖V) = G_(X∖U)`.

**Weakest steps.**
- Lemma 3.1 of the artifact: the normal core is some `N_O`, and `|Q|^r ≤ index` forces `U∖O` finite. It leans on the
  reviewed `LC(Z,Q)` claim.
- Lemma 4.1: the density step on both sides of `r = Σ f_n u^n`, the right side through `u^n e_V = e_(T^nV) u^n`.

Both were rechecked in writing the artifact.

## 3. The support family is not intrinsic (verified here, notes only)

The theorem describes `(M, λ(G_X))`. Even automorphisms of `M` coming from group automorphisms move the family
`{N_U}`.

**Remark 3.1.** Let `k ≠ 0` and `Θ_k` be the automorphism of `M` induced by `θ_k = Ad d_k`, `d_k = diag(u^k,1,1)`. If
`U` is clopen with `T^kU ≠ U`, then `Θ_k(N_U) ≠ N_(U')` for every clopen `U'`.

*Proof.*
- `Θ_k(N_U) = L(θ_k(G_U))`. By Lemma 2.2(iii) of the artifact, `L(S) = L(S')` iff `S = S'`.
- Suppose `θ_k(G_U) = G_(U')`. By C1 the spans of `g − I` agree:
  `d_k M_3(e_U R e_U) d_k^(-1) = M_3(e_(U') R e_(U'))`.
- These are the same subring of `M_3(R)`, so their units agree:
  `d_k E_U d_k^(-1) = diag(e_(T^kU), e_U, e_U) = e_(U') I_3`.
- This forces `T^kU = U = U'`, a contradiction.
- Such `U` exist: `T` has no periodic points, so pick `x`, and a clopen `U ∋ x` with `T^kx ∉ U`. ∎

So any recognition of the support subalgebras from `M` alone can only be up to automorphisms that move them. The
hypothesis of the transport item is the crux, not a technicality.

## 4. Approaches and exactly where each dies

### 4.1 Von Neumann diagonal recognition

- **Plan.** Show that every isomorphism `θ` maps `L(L^X)` onto a unitary conjugate of `L(L^Y)` respecting supports.
  Then use the transport item to get `θ(N^X_U) = N^Y_(U')`, recover the Boolean algebra, then the action through
  normalizers, then flip conjugacy through the group-level repo claims.
- **Dies at the first step.** No intrinsic property of `L(L)` inside `M` was found.
  - Irreducible hyperfinite II_1 subfactors are not special. Every separable II_1 factor is recalled (Popa, early
    1980s, not re-read, unverified) to contain irreducible copies of `R`.
  - Remark 3.1 shows the support family is not invariant under all group-like automorphisms.
  - Group-likeness on `L(L)` would not propagate: `N_G(L)/L ≅ Γ_X` (C5), and the root elements `e_ij(fu^n)` with
    `n ≠ 0` do not normalize `L`, so `L(L)` together with its group normalizer generates only `L(N_G(L)) ≠ M`.

### 4.2 Kazhdan-set height criterion (derived from IPV; notes only)

**Proposition 4.1.**
- Let `Γ` be an ICC property (T) group with Kazhdan pair `(K, ε)`, meaning that any unitary representation with a unit
  vector `ξ` satisfying `‖π(k)ξ − ξ‖ < ε` for all `k ∈ K` has a nonzero invariant vector.
- Let `Λ` be ICC and `M = LΓ = LΛ`, with canonical unitaries `u_g` and `v_s` and height
  `h_Λ(x) = max_s |τ(x v_s^*)|`.
- If `h_Λ(u_k) > (1 − ε²/2)^(1/4)` for all `k ∈ K`, then there are `w ∈ U(M)`, a character `γ` and a group
  isomorphism `δ: Γ → Λ` with `w u_g w^* = γ(g) v_(δ(g))`.

*Proof.*
1. **The representation.** Let `Δ(v_s) = v_s ⊗ v_s` and let `π(g)ξ = (Δ(u_g) ⊗ u_g) ξ (u_g ⊗ Δ(u_g))^*` on
   `L²(M^(⊗3))`.
   - Expanding `u_g = Σ_s c_s v_s` gives `⟨π(g)1, 1⟩ = Σ_s |c_s|^4 ≥ h_Λ(u_g)^4`. This is the same computation as in
     the proof of IPV Theorem 3.1.
   - So `‖π(k)1 − 1‖² = 2 − 2Σ_s|c_s|^4 < ε²` for `k ∈ K`.
2. **An invariant vector.** Property (T) gives a nonzero invariant `ξ`.
   - Polar decomposition and uniqueness give a nonzero partial isometry `V ∈ M^(⊗3)` with
     `(Δ(u_g) ⊗ u_g) V = V (u_g ⊗ Δ(u_g))`.
3. **`V` is a unitary.**
   - `VV^*` is invariant under `Ad(Δ(u_g)) ⊗ Ad(u_g)`. `Ad u` is weakly mixing on `L²(M) ⊖ C` because `Γ` is ICC, so
     `VV^* ∈ (Δ(M)' ∩ M⊗M) ⊗ 1 = C`, using that `Λ` is ICC.
   - Likewise `V^*V = 1`, so `V` is a unitary satisfying IPV's equation (eq.eqX).
4. **Conclusion.** The rest of the proof of IPV Lemma 3.4, from (eq.eqX) on, uses only that relation and weak mixing.
   With Theorem 3.3 and Lemma 7.1 it gives `w`, `γ` and an injective `δ`.
   - `δ` is onto, since `L(δ(Γ)) = wMw^* = M` and Lemma 7.1 applies. ∎

**For the target**, with `Γ = G_X` and `u_g = θ(λ_g)`:
- `G_X` is perfect, so `γ = 1`.
- The target is equivalent to: whenever `L(G_X) ≅ L(G_Y)`, some isomorphism `θ` has `h_(G_Y)(θ(λ_k)) > c` on the
  finite set `K`, where `c = (1 − ε²/2)^(1/4)`.
  - One direction is the proposition. For the other, a group-like `θ` has height `1`.
- **Where it dies.** It is a reformulation. There is no mechanism that produces an almost group-like isomorphism from
  an abstract one, and property (T) gives no deformation to move `θ` (§4.4).
  - Openness of the group-like set is automatic anyway, since `Inn` is open in `Aut` of a (T) factor (Connes, recalled,
    unverified).
  - The quantitative bound is the only content.
  - It is not put into the graph: it is a direct corollary of IPV plus (T), probably folklore, and no node needs it.

### 4.3 Generation by proper supports, coherence, and implementer ambiguity

**Lemma 4.2 (generation).** `G_X = ⟨G_W : W ⊊ X clopen⟩`.

*Proof.*
- `G` is generated by `e_ij(f u^n)`, and `e_ij` is additive, so `e_ij(f u^n) = ∏_(P∈𝒫) e_ij(e_P f u^n)` for any
  clopen partition `𝒫`.
- Since `e_P f u^n = e_P f u^n e_(T^(-n)P)`, each factor lies in `G_W` with `W = P ∪ T^(-n)P`.
- Choose `𝒫` fine enough that no `P ∪ T^(-n)P` is all of `X`:
  - pick three points at mutual distance `≥ d_0`, and atoms `P` with `diam P < d_0` and `diam T^(-n)P < d_0`, by
    uniform continuity;
  - two sets of diameter `< d_0` cannot contain the three points. ∎

**Coherence.**
- If a single unitary `w` makes `Ad w ∘ θ` group-like on every `N_W`, it is group-like on `M` by Lemma 4.2.
- **Dies.** Nothing makes any restriction group-like, and the implementers are not unique. The following lemma was
  checked this session.

**Lemma 4.3 (implementer ambiguity).**
- Let `S` be a group with no proper finite-index subgroup, and `w_1, w_2 ∈ U(LΛ)` with
  `w_i u_s w_i^* = γ_i(s) v_(δ_i(s))` for `s ∈ S`.
- Then `γ_1 = γ_2`, and `w_2 w_1^* ∈ v_(t_0) L(C_Λ(δ_1(S)))` for some `t_0` with `δ_2 = Ad t_0 ∘ δ_1`.

*Proof.*
- `z = w_2 w_1^*` satisfies `v_(δ_2(s))^* z v_(δ_1(s)) = c(s) z` with `c = γ_2 γ_1^(-1)`. So
  `ẑ(δ_2(s) t δ_1(s)^(-1)) = c(s) ẑ(t)`.
- `|ẑ|` is square-summable and constant on orbits of `t ↦ δ_2(s) t δ_1(s)^(-1)`. So its support lies in finite
  orbits, which are fixed points because `S` has no proper finite-index subgroups.
- A fixed point `t` with `ẑ(t) ≠ 0` gives `δ_2 = Ad t ∘ δ_1` and `c = 1`.
- The fixed points form a coset `t_0 C_Λ(δ_1(S))`. Apply Lemma 2.2 of the artifact to `v_(t_0)^* z`. ∎

**In this family.**
- If `δ_1(G^X_W) = G^Y_(W')`, then by C2 the centralizer is `G^Y_(Y∖W')`. So the ambiguity is the whole unitary group
  of the II_1 factor `N^Y_(Y∖W')` from §2.
- A coherence argument must therefore solve a non-abelian cocycle problem over the Boolean algebra of clopens, with
  values in unitary groups of complementary support factors.
- Whether `G_W` has no proper finite-index subgroups was not checked this session. It holds if `G_W` is simple, which
  was not verified for proper `W`.

### 4.4 Deformation/rigidity, Zhou's shear, invariants

- **Deformation/rigidity.** Property (T) makes every s-malleable or length deformation converge uniformly on the unit
  ball (Popa's rigidity, recalled). `G_X` is simple, not a wreath-like product, and not acylindrically hyperbolic, so the
  CIOS and IPV superrigidity theorems do not apply. There is no amenable or soft part to intertwine into. Dies before
  starting.
- **Zhou / OpenAI fibre shear** (repo record): it Fourier-transforms along a normal elementary abelian subgroup `D`,
  giving `L(Γ) = L^∞(D̂) ⋊ H`, and shears fibres. `G_X` is simple nonabelian, so it has no nontrivial abelian normal
  subgroup and no crossed-product decomposition of this kind.
  - Non-normal abelian subgroups, such as `e_12(A)`, give masas without a crossed-product structure, and the shear does
    not extend.
  - Dies at the first step.
- **Soft invariants.** Property (T), fullness, Connes-embeddability status, free entropy dimension 1 (Jung–Shlyakhtenko,
  recalled) and vanishing ℓ²-Betti numbers are the same for all `X`. `Out(L(G_X))` is countable and contains `Z` (graph
  claim). No invariant separating different `X` was found.

## 5. Certificate boundary

- **The node of §2** is a complete written argument modulo two reviewed graph claims and textbook facts: Parseval,
  conditional expectation onto `L(S)`, the separating vector, Brouwer's characterization, and ICC iff factor.
  - No computation.
  - Unreviewed.
- **Remark 3.1, Lemma 4.2 and Lemma 4.3** are elementary and fully proved above, but only in these notes, not in the
  graph.
- **Proposition 4.1** relies on the proofs of IPV Theorem 3.1, Lemma 3.4, Theorem 3.3 and Lemma 7.1, read at source.
  The step from an L² invariant vector to a unitary is written out above.
- **Recalled, not re-read, unverified:** Connes (fullness, countable `Out` and open `Inn` for (T) factors), Popa
  (irreducible hyperfinite subfactors), Jung–Shlyakhtenko, Murray–von Neumann uniqueness of `R`, and the
  normalizer-algebra theorems for group subalgebras (Smith–White–Wiggins; Fang–Gao–Smith, exact statements not
  checked).

## 6. Next targets

1. **Normalizer algebra.** Compute `N_M(L(L))''` and the quasi-normalizer of `L(L)` in `M = L(G_X)`. The conjecture is
   `L(N_G(L))`, with `N_G(L)/L ≅ Γ_X`. If it holds, `L(L) ⊆ N_M(L(L))''` would be a crossed-product-type inclusion
   carrying `Γ_X`, a candidate invariant once `L(L)` is recognized.
2. **Up-to-conjugacy recognition.** Characterize `{Ad w(N_U)}` intrinsically: mutually commuting pairs of irreducible
   II_1 subfactors with relative-bicommutant closure and a Boolean meet structure. Test against Remark 3.1 first.
3. **The implementer cocycle of §4.3.** Decide whether restrictions of an isomorphism to `N_W` can be simultaneously
   group-like. First sub-question: is `G_W` simple for proper clopen `W`?
4. **`Out(L(G_X))`** versus `Out(G_X)` (Jones's question), as in `subshift-group-factor-out-contains-z`.

## Referee (2026-09-16)

Adversarial referee and landing agent for this lane.

**What was checked.**
- Read in full: the claim, the route, the artifact and these notes. Also read the prerequisite claims
  `subshift-elementary-group-rigid-supports-are-mutual-centralizers` (with the C3 proof in
  `research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md` §3) and
  `locally-constant-simple-group-normal-subgroups-are-open-sets`, and the target hole.
- Artifact, re-derived step by step:
  - Lemma 1.1(i). An isolated point makes `X` a single discrete orbit, hence finite.
  - Lemma 1.2.
  - Lemma 2.1. The trace identity `τ(xλ_(hgh^(-1))^*) = τ(xλ_g^*)` and Parseval give a finite conjugacy class.
  - Lemma 2.2. Conditional expectation and the separating vector `δ_e`.
  - Lemma 3.1. The core is `N_O` by (NO); the `|Q|^r` elements `l_q` lie in distinct cosets of `N_O`, so `Z∖O` is finite.
  - Lemma 4.1, both halves. With `u f u^(-1) = f∘T^(-1)` (the convention of the rigid-supports artifact, line 11),
    `u^n e_V u^(-n) = e_(T^nV)`. So `r e_V = Σ f_n e_(T^nV) u^n`, and `f_n∘T^n` vanishes on `U∖F`, hence on `U`.
  - Lemma 4.2(i)–(iii), including `L_U ∩ G_V = L_(U∩V)` via commutativity of `A`.
  - Theorem 5.1(a)–(e), with the edge cases `U = ∅` (`N_X = M`) and `U = X` (`L_X = L`, `N_∅ = C`). The main step
    applies C3 to the clopen set `X∖V`, which gives `C_G(L_V) = G_(X∖V)`, as stated.
  - Corollary 6.1, including the Boolean-embedding bookkeeping.
  No gap, hidden hypothesis or quantifier mismatch was found. Separability/countability is used only for (e) and is
  proved (Lemma 1.1(iii)). The textbook inputs are Brouwer, ICC iff factor, and `L(G_1×G_2) ≅ L(G_1)⊗̄L(G_2)`. They are
  standard and named as such.
- Notes-only material, spot-checked:
  - Remark 3.1: the unit of `d_k M_3(e_U R e_U) d_k^(-1)` is `diag(e_(T^kU), e_U, e_U)`.
  - Lemma 4.2 (generation): `e_P f u^n = e_P f u^n e_(T^(-n)P)`.
  - Lemma 4.3: the Fourier orbit argument and the fixed-point coset.
  - Proposition 4.1, step 1: the identity `⟨π(g)1,1⟩ = Σ|c_s|^4` and the bound `‖π(k)1−1‖² < ε²`.
  The IPV-dependent steps 2–4 were not re-read at source by the referee. They remain notes-only and are labelled as a
  derived reformulation, which is appropriate.
- Duplicates: `bin/cairn search --similar` and a lexical search for "relative commutant" and "hyperfinite subfactor"
  found no existing node with this content. The nearest is the group-level rigid-supports claim, which is already
  listed in `distinct_from`. Id lengths: 54 (claim) and 46 (route).
- Citations, fetched on arXiv abstract pages 2026-09-16:
  - 2608.02327 Zhou (v1 2026-08-03, v2 2026-09-04): matches.
  - 1007.1412 Ioana–Popa–Vaes (v3 2012-08-20): matches the recorded source mtime.
  - 2403.05948 Amrutam–Bassi: matches.
  - 2608.14673 Sienicki–Sienicki: the abstract does say later research confirms Connes's rigidity conjecture is false.
  - 2511.23123 Ariza Mejía–Chifan–Osin–Sun, McDuff superrigidity: matches.
  - An extra arXiv API query, `all:"minimal subshift" AND all:"property (T)"`, returned one unrelated hit (1811.12256,
    Matte Bon).
  - General web search was unavailable to the referee too (budget exhausted). So the status check of the target rests
    on the arXiv API only. The target is the repo's own question, and nothing found resolves it.

**What was changed.**
- Added a one-paragraph referee PASS line to `research/subshift-group-factor-supports-are-relative-commutants.md`.
- Appended this section.
- No mathematical content was altered. The target hole file was not edited: these notes are already surfaced by
  `bin/cairn context subshift-group-factors-determine-subshift-groups`.

**Verdict.** Sound as written, and honestly labelled. The claim is ESTABLISHED via a route whose two prerequisites are
both reviewed PASS. Item 6 is explicitly conditional, and the scope paragraph correctly says the result describes the
pair `(L(G_X), λ(G_X))`, not an invariant of the factor. The target `subshift-group-factors-determine-subshift-groups`
stays OPEN. Landed as is, apart from the referee annotations.
