# The descending links L_n(LB_*) are simply connected for n ≥ 8

Swarm lane zaremsky-2-12-loop-braided-v-t, 2026-09-16. Hand proof, with computer checks of the
explicit formulas (§8). Refereed 2026-09-16: no mathematical error found. The referee added the
(HW) citation and `referee_indep_check.py`; see the referee section of
`notes/zaremsky-2-12-loop-braided-v-type-f-infi-swarm-2026-09-16.md`. It builds on:

- `zp-loop-braid-cloning-properly-graded-2026-09-13.md` ("PG"). Conventions, Lemma A, the free-group
  facts F1–F3.
- `zp-loop-braid-descending-links-model-2026-09-13.md` ("DL"). The complex and the plan of DL §4,
  which is carried out here.

## 0. Statement and scope

**Theorem.** For every `n ≥ 8` the complex `L_n(LB_*)` of Witzel–Zaremsky (arXiv:1405.5491v3, §5.3),
for the loop braid cloning system of their §10, is simply connected.

- **Corollary.** `V_loop = T(LB_*)` is finitely presented. This is WZ Proposition 5.9 with type `F_2`,
  using the established claims `loop-braid-groups-are-type-f-infinity` and
  `loop-braid-cloning-system-is-properly-graded`. The graph route is
  `v-loop-finitely-presented-via-simply-connected-descending-links`.
- **Structure of the proof.** Put `P = PLB_n` and `X = L_n(LB_*)`.
  1. §2. P acts on X with a strict fundamental domain `Q ≅ OM(K_n)`, and stabilizers fix simplices
     pointwise.
  2. §3. A covering-space criterion: if Q is simply connected and the colimit of the simplex
     stabilizers over Q maps isomorphically onto P, then X is simply connected.
  3. §4. `OM(K_n)` is simply connected for `n ≥ 8`.
  4. §§5–6. The colimit statement for `n ≥ 7`, from McCool's presentation and an explicit
     computation of the cabling maps on McCool's generators.
- **Not claimed.**
  - Higher connectivity of `L_n(LB_*)`, so type `F_∞` for `V_loop` (Problem 2.12) is still open.
  - Anything about `n ≤ 7`.

## 1. Inputs, quoted

**(W1) WZ, arXiv:1405.5491v3, §5.3, the complex** (TeX source, verbatim): "A simplex in
`L_n(G_*)` is represented by a pair `(g,Γ)`, where `g ∈ G_n` and Γ is a non-trivial matching of
`L_n`. Two such pairs `(g_1,Γ_1)`, `(g_2,Γ_2)` are *equivalent (under dangling)* if the following
conditions hold:

1. `Γ_1` and `Γ_2` both have m edges for some `1 ≤ m ≤ n/2`,
2. `g_2^{-1} g_1` lies in the image of `κ_{Γ_1}`, and
3. `Γ_2 = (g_2^{-1} g_1)κ_{Γ_1}^{-1} · Γ_1`.

We make `L_n(G_*)` into a simplicial complex with face relation given by passing to subgraphs of the
second term in the pair."

- Earlier in §5.3: "if Γ is a matching with m edges and n vertices we obtain a cloning map
  `κ_Γ: G_{n−m} → G_n` which is just the cloning map of `E(Γ)` … We also get an action of `G_{n−m}` on
  Γ which is given by the action of `ρ(G_{n−m})` on connected components."
- `E(Γ)` is the elementary forest with a caret on the leaves `k, k+1` for each edge `e_k` of Γ. For a
  forest `λ_{k_1} ⋯ λ_{k_r}`, WZ put `κ_F := κ_{k_1} ∘ ⋯ ∘ κ_{k_r}`, "well defined by condition
  (product of clonings) and … just the map `g ↦ g^F`".
- The forest action is fixed by `g · λ_k := λ_{ρ(g)k}` and `g · (λ_k F) = λ_{ρ(g)k}((g)κ_k · F)`
  (TeX lines 937, 1038). So the action on components moves the component in position c to position
  `ρ(h)c`. This is the reading under which condition 3 matches the Zappa–Szép relation
  `h E = (h·E) h^E` behind Observation 5.8.
- **(W2) Observation 5.8**, verbatim: "If x has n feet, the correspondence `(g,Γ) ↦ x g E(Γ)^{-1}`
  induces an isomorphism `L_n(G_*) → dlk(x)`." WZ add: "In particular, the `L_n(G_*)` are indeed
  simplicial complexes as claimed, since X(G_*) is a cubical complex."
- **(W3) Proposition 5.9**, verbatim: "Let G∗ be equipped with a properly graded cloning system. If
  G_k is eventually of type F_n and L_k(G∗) is eventually (n − 1)-connected then T(G∗) is of type
  F_n."
- **(W4) Axiom (CS1)**, verbatim: "`(gh)κ_k = (g)κ_{ρ(h)k}(h)κ_k`". WZ Lemma 10.1 says the formulas
  (10.1)–(10.2) define cloning systems on `LB_*` and `PLB_*`; the formulas are recalled in PG §0.

**(M) McCool's presentation**, as quoted by Ershov–Zaremsky, *Dense and empty BNSR-invariants of the
McCool groups*, arXiv:2505.18826v3 (text dated February 11, 2026), §2.2, verbatim: "In [McC86], McCool
exhibited a natural finite presentation for `PSAut_n`. There is a generator `α_ij` for each
`1 ≤ i, j ≤ n` with `i ≠ j`, and the defining relations are as follows:

- `[α_ij, α_kℓ] = 1` for `i, j, k, ℓ` distinct,
- `[α_ij, α_kj] = 1` for `i, j, k` distinct,
- `[α_ij α_kj, α_ik] = 1` for `i, j, k` distinct.

The generator `α_ij` is the automorphism of `F_n` sending `x_i` to `x_i^{x_j} = x_j^{-1} x_i x_j` and
fixing all `x_k` for `k ≠ i`."

- [McC86] is J. McCool, *On basis-conjugating automorphisms of free groups*, Canad. J. Math. 38(6)
  (1986), 1525–1529. The original was not fetched; the statement is used through the quotation above.

**Convention independence of (M).** Write `A_ij := α_ij^{-1}: x_i ↦ x_j x_i x_j^{-1}`.

- In any group, two elements commute iff their inverses commute.
- Modulo the second family of relations, `α_ij α_kj = α_kj α_ij`.
- So the three families of relations are equivalent to those obtained by replacing every generator by
  its inverse, or by reversing every word.
- Hence, whichever composition convention [McC86] uses, the group `P = PΣAut_n` under composition
  `(f∘g)(x) = f(g(x))` has the presentation with generators `A_ij` and these relators:
  - (R1) `[A_ij, A_kl]`;
  - (R2) `[A_ij, A_kj]`;
  - (R3) `[A_ij A_kj, A_ik]`.
- The script in §8 checks that R1–R3 hold in this convention for `n = 4, 5, 6`.
- Each relator is a word in the `A_pq` with `p, q` in a set `S(R)` of at most 4 indices.

**(B) BFMWZ, arXiv:1210.2931, the proposition with TeX label `prop:matching_cpx_conn`**, verbatim from
the TeX source: "The complex `M(K_n)` is `(ν(n)−1)`-connected."

- Here `ν(n) = ⌊(n+1)/3⌋ − 1` (TeX line 3061: "Recall that `ν(n) = ⌊(n+1)/3⌋−1`").
- They add: "This result is well-known, see for example [athanasiadis04, bjorner94]."

**(Q) Quillen, Homotopy properties of the poset of nontrivial p-subgroups (Adv. Math. 1978),
Theorem 9.1**, in the form in which BFMWZ (TeX line 3654) and WZ (TeX line 2375) apply it. Let
`f: Y → Z` be a simplicial map and d an integer, and assume:

- Z is d-connected;
- the link of every k-simplex of Z is `(d−k−1)`-connected;
- the fiber `f^{-1}(σ)` over every closed k-simplex σ is `(k−1)`-connected.

Then Y is d-connected. The original statement was not fetched here; it is used exactly as in the two
cited applications. BFMWZ l. 3654: "… so `lk(σ)` is `(η(m+1)−k−2)`-connected. It now suffices by
[Quillen, Theorem 9.1] to prove that the fiber `π^{-1}(σ)` is `(k−1)`-connected (here we treat a
simplex as a closed cell)." For `d = 1`, which is all that is used, §8 also checks the cases
`n = 8, 9` by machine.

**(HW) Hatcher–Wahl, Stabilization for mapping class groups of 3-manifolds, arXiv:0709.2173v4.**
Added by the referee; the TeX source was checked on 2026-09-16.

- **Definition 3.2 (TeX label `joincpx`).** A join complex over X is a simplicial map `π: Y → X`
  such that:
  - (1) π is surjective;
  - (2) π is injective on individual simplices;
  - (3) for each p-simplex σ of X, the subcomplex `Y(σ)` of p-simplices projecting to σ is the join
    of the vertex sets `Y_{x_i}(σ)`.

  It is *complete* if all `Y_{x_i}(σ) = π^{-1}(x_i)`.
- **wCM.** "X is (n−1)-connected and the link of each p-simplex of X is (n−p−2)-connected".
- **Proposition 3.5 (TeX label `label`), verbatim.** "If Y is a complete join complex over a CM
  (resp. wCM) complex X of dimension n, then Y is also CM (resp. wCM) of dimension n."

(HW) gives Proposition 4.1(b) without (Q); see the remark after its proof.

**(FRR) Generation.** `LB_n` is generated by `β_i^{±1}, σ_i` (`1 ≤ i ≤ n−1`); this is the
presentation WZ use in §10. `PLB_n` is generated by the `A_ij`, by (M).

## 2. The strict fundamental domain

Conventions are as in PG §0.

- Every `g ∈ LB_n` is identified with its left form `L(g) ∈ ΣAut_n`, and products are composition.
- `ρ = ρ_n: LB_n → S_n`, so `g(x_i)` is conjugate to `x_{ρ(g)i}`.
- `S_n := ⟨σ_1, …, σ_{n−1}⟩` is the group of permutation automorphisms `P_π: x_i ↦ x_{πi}`, and
  `ρ(P_π) = π`. So `ρ|_{S_n}` is an isomorphism.
- `LB_n = P ⋊ S_n` with `P = ker ρ = PLB_n`. Write `s_g := (ρ|_{S_n})^{-1}(ρ(g))`, a homomorphism
  `LB_n → S_n` with kernel P.
- `hat_k(c) = c` for `c < k`, and `hat_k(c) = c + 1` for `c > k`.

**Lemma 2.1 (cloning on permutations).** Let `g ∈ LB_n`, `1 ≤ k ≤ n`, and `j := ρ(g)k`.

- (a) If `g ∈ S_n` then `(g)κ_k ∈ S_{n+1}`, and `ρ((g)κ_k) = τ` with `τ(k) = j`, `τ(k+1) = j+1`, and
  `τ(hat_k c) = hat_j(ρ(g)c)` for `c ≠ k`.
- (b) For every g, `ρ((g)κ_k) = ρ((s_g)κ_k)`, hence `s_{(g)κ_k} = (s_g)κ_k`.
- (c) `κ_k` is injective, and so is every composite `κ_Γ`.
- (d) `κ_k` restricts to an injective homomorphism `PLB_n → PLB_{n+1}`.

*Proof.*

(a)
- The cloning formulas send each `σ_i` to a word in the σ's, and (CS1) computes the clone of a word
  letter by letter, so `(g)κ_k ∈ S_{n+1}`. Write `(g)κ_k = P_τ`.
- Lemma A (PG §1) gives `P_τ ∘ δ_k = δ_j ∘ P_{ρ(g)}`.
- Evaluating at `x_k` gives `x_{τk} x_{τ(k+1)} = δ_j(x_j) = x_j x_{j+1}`.
- Evaluating at `x_c` for `c ≠ k` gives `x_{τ(hat_k c)} = δ_j(x_{ρ(g)c}) = x_{hat_j(ρ(g)c)}`, as
  `ρ(g)c ≠ j`.

(b)
- For a generator `β_i^{±1}`, the clone is the same word as the clone of `σ_i`, with each σ replaced by
  `β^{±1}`. So the two clones have the same ρ, and `s_{β_i^{±1}} = σ_i`.
- If the claim holds for g and h (at every index), then (CS1) gives
  `ρ((gh)κ_k) = ρ((g)κ_{ρ(h)k}) ρ((h)κ_k) = ρ((s_g)κ_{ρ(s_h)k}) ρ((s_h)κ_k) = ρ((s_g s_h)κ_k)`.
- Induction on word length finishes it. The last assertion holds because both sides lie in `S_{n+1}`
  and have the same ρ.

(c)
- Suppose `(g)κ_k = (g')κ_k`. By (b) and (a), `ρ(g)k = ρ(g')k =: j`.
- (CS1) for `g'^{-1} g'` gives `(g'^{-1})κ_j = ((g')κ_k)^{-1}`. So
  `(g'^{-1} g)κ_k = (g'^{-1})κ_j (g)κ_k = 1`.
- If `(u)κ_k = 1`, then `ρ(u)k = k` by (a) and (b). Lemma A gives `δ_k = δ_k ∘ u`, so `u = 1`, since
  `δ_k` is injective.
- Composites of injective maps are injective.

(d) For pure h, (CS1) reads `(gh)κ_k = (g)κ_k (h)κ_k`, and a clone of a pure element is pure by (b). ∎

**Lemma 2.2 (retraction).** Let `Q := {[s, Γ] : s ∈ S_n}`, a subcomplex of X. Then
`r([g, Γ]) := [s_g, Γ]` is a well-defined simplicial map `X → Q`. It is P-invariant and the identity
on Q. Consequently:

- (i) every simplex of X is a P-translate of exactly one simplex of Q;
- (ii) if `p ∈ P` stabilizes a simplex, it fixes that simplex pointwise.

*Proof.*

- **Well defined.** Suppose `(g_1, Γ_1) ~ (g_2, Γ_2)`, with `g_2^{-1} g_1 = (h)κ_{Γ_1}` and
  `Γ_2 = h · Γ_1`.
  - Then `s_{g_2}^{-1} s_{g_1} = s_{(h)κ_{Γ_1}} = (s_h)κ_{Γ_1}`, by Lemma 2.1(b) iterated.
  - `s_h · Γ_1 = h · Γ_1 = Γ_2`, because the action on components only depends on `ρ(h) = ρ(s_h)`.
  - So `(s_{g_1}, Γ_1) ~ (s_{g_2}, Γ_2)`.
- **Simplicial and invariant.** Faces go to faces, since Γ is untouched. `s_{pg} = s_g` for `p ∈ P`,
  and `s_s = s` for `s ∈ S_n`.
- **(i).** Existence: `[g, Γ] = (g s_g^{-1}) · [s_g, Γ]`. Uniqueness: if `p σ_1 = σ_2` with
  `σ_1, σ_2 ∈ Q`, then `σ_2 = r(σ_2) = r(p σ_1) = r(σ_1) = σ_1`.
- **(ii).**
  - Let `p σ = σ`, and write `σ = q σ_0` with `σ_0 ∈ Q`.
  - For a vertex v of σ, `q^{-1} v` and `q^{-1} p v = (q^{-1} p q) q^{-1} v` are vertices of `σ_0`,
    so they lie in Q, and they are in one P-orbit.
  - By (i) they are equal, so `p v = v`. Since X is a simplicial complex (W2), σ is fixed pointwise. ∎

**Lemma 2.3 (Q is the ordered matching complex).** The vertices of `OM(K_n)` are the ordered pairs
`(a, b)` of distinct elements of `[n]`, and its simplices are the sets of pairwise disjoint pairs.
The map `Φ([s, Γ]) := {(ρ(s)k, ρ(s)(k+1)) : e_k ∈ Γ}` is a well-defined isomorphism
`Q → OM(K_n)`.

*Proof.*

- **On vertices, well defined.**
  - Suppose `(s_1, e_k) ~ (s_2, e_{k'})`, so `u := s_2^{-1} s_1 = (h)κ_k` and `e_{k'} = h · e_k`.
  - As in Lemma 2.2, h may be replaced by `s_h`. By (W1), `k' = ρ(h)k`.
  - By Lemma 2.1(a), `ρ(u)` maps `k ↦ k'` and `k+1 ↦ k'+1`. Since `ρ(s_1) = ρ(s_2)ρ(u)`, the two
    pairs agree.
- **On vertices, injective.**
  - Suppose `ρ(s_1)(k, k+1) = ρ(s_2)(k', k'+1)`, and put `τ := ρ(s_2^{-1} s_1)`, so `τ(k) = k'` and
    `τ(k+1) = k'+1`.
  - Define `π ∈ S_{n−1}` by `π(k) = k'` and `π(c) = hat_{k'}^{-1}(τ(hat_k c))` for `c ≠ k`.
  - Let `h := P_π ∈ S_{n−1}`. By Lemma 2.1(a), `ρ((h)κ_k) = τ`, so `(h)κ_k = s_2^{-1} s_1`.
  - Also `h · e_k = e_{ρ(h)k} = e_{k'}`. Hence `[s_1, e_k] = [s_2, e_{k'}]`.
- **On vertices, surjective.** Take `ρ(s)1 = a`, `ρ(s)2 = b`, `k = 1`.
- **Simplices.**
  - The vertices of `[s, Γ]` are the `[s, e_k]` with `e_k ∈ Γ`; their pairs are pairwise disjoint
    because `ρ(s)` is a bijection.
  - Conversely, let `(a_1, b_1), …, (a_m, b_m)` be pairwise disjoint pairs. Take `s ∈ S_n` with
    `ρ(s)(2t−1) = a_t` and `ρ(s)(2t) = b_t`, and `Γ = {e_1, e_3, …, e_{2m−1}}`. Then `[s, Γ]` has
    exactly these vertices.
  - Since X is a simplicial complex (W2), a simplex is determined by its vertex set. ∎

**Lemma 2.4 (stabilizers).** Let `σ = [s, Γ] ∈ Q` with m edges, and `π := ρ(s)`. Then
`P_σ := Stab_P(σ) = P_π · (PLB_{n−m})κ_Γ · P_π^{-1}`.

*Proof.*

- `Stab_P[s, Γ] = s · Stab_P[1, Γ] · s^{-1}`, since `s[1, Γ] = [s, Γ]` and P is normal.
- `p ∈ Stab_P[1, Γ]` means `(p, Γ) ~ (1, Γ)`, i.e. `p = (h)κ_Γ` with `h · Γ = Γ`.
- Then `(s_h)κ_Γ = s_p = 1 = (1)κ_Γ`, so `s_h = 1` by injectivity. Thus h is pure, and `h · Γ = Γ`
  holds automatically.
- Conversely, `(h)κ_Γ` is pure for pure h by Lemma 2.1(b). ∎

Under Φ we write `P_{(a,b)}` for vertex stabilizers and `P_{{v,w}}` for edge stabilizers.

## 3. A covering criterion

**Proposition 3.1.** Let a group P act simplicially on a simplicial complex X, and let `Q ⊆ X` be a
subcomplex such that:

- (i) every simplex of X is a P-translate of exactly one simplex of Q;
- (ii) the stabilizer `P_σ` of every simplex σ of Q fixes σ pointwise;
- (iii) Q is non-empty, connected and simply connected;
- (iv) the natural map `ψ: Ĝ → P` is an isomorphism, where
  `Ĝ := (∗_{v ∈ V(Q)} P_v) / ⟨⟨ ι_v(g) ι_w(g)^{-1} : {v, w} an edge of Q, g ∈ P_{{v,w}} ⟩⟩`,
  `ι_v` is the inclusion of the free factor `P_v`, and ψ restricts to the inclusion on each `P_v`.

Then X is connected and simply connected.

Only the surjectivity of ψ is used for connectivity. The statement is a special case of the theory of
developments of simple complexes of groups (Bridson–Haefliger, Ch. II.12; not fetched here), so a
self-contained proof is given.

*Proof.* **Connectivity.**

- Let `X_0` be the path component of X containing Q.
- For a vertex v of Q and `g ∈ P_v`, the component `g X_0` contains `g v = v`, so `g X_0 = X_0`.
- The set `{g ∈ P : g X_0 = X_0}` is a subgroup containing every `P_v`. By (iv) the `P_v` generate P,
  so this subgroup is P.
- Hence `X = P · Q ⊆ X_0` by (i).

**Simple connectivity.**

- **Setup.**
  - Let `p: X̃ → X` be the universal covering, with the lifted simplicial structure, so p is simplicial
    and restricts to a homeomorphism on every closed simplex.
  - Let `G̃` be the group of homeomorphisms φ of `X̃` such that `p ∘ φ = g ∘ p` for some `g ∈ P`, and
    `π: G̃ → P`, `φ ↦ g`. Here g is unique because p is onto.
  - Two lifts of the same g differ by a deck transformation. The deck group acts simply transitively on
    each fiber of p, and every `g ∘ p` has a lift, which is a homeomorphism (lift `g^{-1} ∘ p` too).
- **A lift of Q.** Since Q is connected, locally path connected and simply connected, the inclusion
  `Q ↪ X` lifts to `j: Q → X̃` with `p ∘ j = id_Q`. Then `j(Q)` is a subcomplex and
  `p|_{j(Q)}` is inverse to j.
- **Local lifts.** For a simplex σ of Q, let `b_σ` be its barycenter, and for `g ∈ P_σ` let `f_σ(g)`
  be the unique lift of g fixing `j(b_σ)`.
  - It exists: g fixes `b_σ`, so any lift maps `j(b_σ)` into `p^{-1}(b_σ)`, and a deck transformation
    moves it back.
  - `f_σ: P_σ → G̃` is a homomorphism, by uniqueness.
  - `f_σ(g)` fixes `j(σ)` pointwise. For `y ∈ σ`, let γ be the straight path in σ from `b_σ` to y.
    By (ii), `g ∘ γ = γ`. Then `j ∘ γ` and `f_σ(g) ∘ j ∘ γ` are lifts of γ starting at `j(b_σ)`, so
    they coincide by unique path lifting.
  - For `σ ⊆ τ` and `g ∈ P_τ ⊆ P_σ`, `f_τ(g)` fixes `j(b_σ) ∈ j(τ)`, so `f_τ(g) = f_σ(g)`.
- **The section.**
  - For an edge `e = {v, w}` of Q and `g ∈ P_e`: `f_v(g) = f_e(g) = f_w(g)`. So the `f_v` induce a
    homomorphism `F: Ĝ → G̃` with `π ∘ F = ψ`.
  - Put `s := F ∘ ψ^{-1}: P → G̃`. This is a homomorphism with `π ∘ s = id_P`.
  - If `h ∈ P_σ` for a simplex σ of Q, pick a vertex v of σ. Then `ψ^{-1}(h) = ι_v(h)`, so
    `s(h) = f_v(h) = f_σ(h)` fixes `j(σ)` pointwise.
- **Z maps injectively.** Let `Z := ⋃_{g ∈ P} s(g) j(Q)`, a subcomplex of `X̃` with `p(Z) = P · Q = X`.
  - Suppose two simplices `s(g_1) j(σ_1)` and `s(g_2) j(σ_2)` of Z have the same image
    `g_1 σ_1 = g_2 σ_2`.
  - By (i), `σ_1 = σ_2 =: σ` and `h := g_2^{-1} g_1 ∈ P_σ`.
  - Then `s(g_1) ∘ j|_σ = s(g_2) ∘ s(h) ∘ j|_σ = s(g_2) ∘ j|_σ`. So the two simplices are equal.
  - Every simplex of Z has the form `s(g) j(σ)`, so distinct simplices of Z have distinct images.
  - A point of X lies in the interior of exactly one simplex τ. Every preimage in Z lies in the interior
    of a simplex of Z mapping onto τ. That simplex is unique by the previous point, and p is injective
    on it. So `p|_Z` is injective.
- **Z is everything.**
  - Let `τ̃` be a simplex of `X̃` with a vertex `ỹ ∈ Z`, and put `τ := p(τ̃)`, `y := p(ỹ)`.
  - Since `p(Z) = X`, some simplex `τ'` of Z maps onto τ. Its vertex over y lies in Z, so it is ỹ by
    injectivity.
  - `(p|_{τ̃})^{-1}` and `(p|_{τ'})^{-1}` are lifts of the inclusion `τ ↪ X` that agree at y. As τ is
    connected, they agree, so `τ̃ = τ' ⊆ Z`.
  - Hence the vertex set of Z is closed under adjacency in the 1-skeleton of `X̃`. That 1-skeleton is
    connected and Z is non-empty, so Z contains every vertex, and then every simplex, of `X̃`.
- **Conclusion.** p is injective, so it is a one-sheeted covering, and `π_1(X) = 1`. ∎

## 4. The ordered matching complex

`OM(K_n)` is as in Lemma 2.3. `M(K_n)` has the 2-element subsets of `[n]` as vertices and the sets of
pairwise disjoint subsets as simplices.

**Proposition 4.1.**

- (a) `OM(K_n)` is connected for `n ≥ 5`.
- (b) `OM(K_n)` is simply connected for `n ≥ 8`.

*Proof of (a).* Let `(a, b)`, `(c, d)` be vertices.

- If they are disjoint, they are adjacent.
- Otherwise `|{a, b, c, d}| ≤ 3`, so for `n ≥ 5` there are two further elements e, f. The vertex
  `(e, f)` is adjacent to both. So the diameter of the 1-skeleton is at most 2. ∎

*Proof of (b).* Apply (Q) with `d = 1` to the simplicial map `f: OM(K_n) → M(K_n)`,
`(a, b) ↦ {a, b}`. It is simplicial because disjoint ordered pairs give disjoint 2-subsets.

- **Base.** By (B), `M(K_n)` is `(ν(n) − 1)`-connected. For `n ≥ 8`, `ν(n) = ⌊(n+1)/3⌋ − 1 ≥ 2`, so the
  base is 1-connected.
- **Links.** The link of a k-simplex (a matching with `k+1` edges) is the matching complex of the
  complete graph on the `n − 2k − 2` uncovered vertices, i.e. `M(K_{n−2k−2})`. We need it to be
  `(−k)`-connected.
  - `k = 0`: `M(K_{n−2})` is `(ν(n−2) − 1)`-connected, and `ν(n−2) = ⌊(n−1)/3⌋ − 1 ≥ 1` for `n ≥ 7`.
    So it is connected.
  - `k = 1`: `M(K_{n−4})` is non-empty for `n ≥ 6`.
  - `k ≥ 2`: there is no condition.
- **Fibers.** Let σ be a closed k-simplex with edges `{a_0,b_0}, …, {a_k,b_k}`.
  - A simplex of `OM(K_n)` maps into σ iff it chooses, for a subset of these edges, one of the two
    orientations of each chosen edge.
  - `(a_t, b_t)` and `(b_t, a_t)` are never adjacent.
  - So `f^{-1}(σ)` is the join of `k+1` copies of `S^0`, the boundary of the `(k+1)`-dimensional
    cross-polytope. This is `S^k`, which is `(k−1)`-connected. ∎

*Second proof of (b), from (HW) (referee).*

- `f` is a complete join complex over `M(K_n)`:
  - it is surjective and injective on simplices;
  - over a p-simplex, every choice of one orientation per edge spans a simplex, so `Y(σ)` is the join
    of the full fibers.
- The **Base** and **Links** items above say that `M(K_n)` is wCM of dimension 2 for `n ≥ 8`.
- By HW Proposition 3.5, `OM(K_n)` is wCM of dimension 2, and in particular 1-connected. ∎

**Remark 4.2.**

- The same count with `d = ν(n) − 1` gives that `OM(K_n)` is `(ν(n) − 1)`-connected for all n. The
  link `M(K_{n−2k−2})` is `(⌊(n−2k−1)/3⌋ − 2)`-connected, and
  `⌊(n+1−2(k+1))/3⌋ − 2 ≥ ⌊(n+1)/3⌋ − (k+1) − 2 = d − k − 1`.
- Only `d = 1` is used below.
- §8 confirms (b) independently of (B) and (Q) for `n = 8, 9`, by a machine certificate that every edge
  loop is null-homotopic.
- For `n = 5, 6` the complex is not simply connected (`H_1(−; F_2) ≠ 0`). For `n = 7` the certificate is
  inconclusive; this case is not needed.

## 5. Cabling McCool's generators

`A_ij: x_i ↦ x_j x_i x_j^{-1}` as in (M). For a permutation π of `[n]`, `P_π A_ij P_π^{-1} = A_{πi,πj}`
(evaluate both sides on `x_{πc}`).

**Lemma 5.1 (cabled generators).** Let `1 ≤ k ≤ m`, `n = m + 1`, `hat = hat_k`, and `p ≠ q` in `[m]`.
In `PLB_n`:

- `(A_pq)κ_k = A_{p̂, q̂}` if `p, q ≠ k`;
- `(A_pk)κ_k = A_{p̂, k+1} A_{p̂, k}`;
- `(A_kq)κ_k = A_{k, q̂} A_{k+1, q̂}`.

*Proof.*

- **Words.** From the left forms `a_i = L(β_i)` and `s_i = L(σ_i)` (PG §0), `L(σ_1 β_1) = s_1 a_1 = A_12`
  and `L(β_1 σ_1) = a_1 s_1 = A_21`. In the same way `L(σ_2 β_2) = A_23`.
- **Three base cases at `k = 1`.** The cloning formulas (10.1)–(10.2) are: `(σ_i)κ_k` equals `σ_{i+1}`,
  `σ_i σ_{i+1}`, `σ_{i+1} σ_i` or `σ_i` according as `k < i`, `k = i`, `k = i+1` or `k > i+1`, and the
  same with `β_i^{±1}`. Using (CS1):
  - `(σ_1 β_1)κ_1 = (σ_1)κ_2 (β_1)κ_1 = σ_2 σ_1 β_1 β_2`. Its left form `s_2 s_1 a_1 a_2` sends
    `x_1 ↦ x_3 x_1 x_3^{-1}`, `x_2 ↦ x_3 x_2 x_3^{-1}` and `x_3 ↦ x_3`. So it is `A_13 A_23`.
  - `(β_1 σ_1)κ_1 = (β_1)κ_2 (σ_1)κ_1 = β_2 β_1 σ_1 σ_2`. Its left form `a_2 a_1 s_1 s_2` fixes `x_1` and
    `x_2`, and sends `x_3 ↦ x_1 x_2 x_3 x_2^{-1} x_1^{-1}`. So it is `A_32 A_31`.
  - For `m ≥ 3`: `(σ_2 β_2)κ_1 = (σ_2)κ_1 (β_2)κ_1 = σ_3 β_3`, with left form `A_34`.
- **Conjugation.** Let `w ∈ S_m`, `g ∈ PLB_m` and `j := ρ(w)^{-1} k`.
  - (CS1) gives `1 = (1)κ_k = (w)κ_j (w^{-1})κ_k`.
  - Since g is pure, `ρ(g w^{-1}) k = j`, and (CS1) gives
    `(w g w^{-1})κ_k = (w)κ_j (g)κ_j (w^{-1})κ_k = W (g)κ_j W^{-1}` with `W := (w)κ_j`.
  - By Lemma 2.1(a), `W = P_τ` with `τ(j) = k`, `τ(j+1) = k+1`, and `τ(hat_j c) = hat_k(ρ(w)c)`.
- **General case.** In each case take `j = 1` and `w ∈ S_m` with `ρ(w) 1 = k`.
  - `p = k`: take also `ρ(w) 2 = q`. Then `w A_12 w^{-1} = A_kq`, and
    `(A_kq)κ_k = P_τ A_13 A_23 P_τ^{-1} = A_{τ1,τ3} A_{τ2,τ3} = A_{k, q̂} A_{k+1, q̂}`, since
    `τ3 = τ(hat_1 2) = hat_k(q)`.
  - `q = k`: take also `ρ(w) 2 = p`. Then `w A_21 w^{-1} = A_pk`, and
    `(A_pk)κ_k = A_{τ3,τ2} A_{τ3,τ1} = A_{p̂, k+1} A_{p̂, k}`.
  - `p, q ≠ k` (so `m ≥ 3`): take also `ρ(w) 2 = p` and `ρ(w) 3 = q`. Then `w A_23 w^{-1} = A_pq`, and
    `(A_pq)κ_k = A_{τ3,τ4} = A_{p̂, q̂}`. ∎

§8 checks the three formulas by machine for `n ≤ 7` and all k, p, q.

**Corollary 5.2 (vertex stabilizers).** For a vertex `v = (a, b)` of Q, `P_v` is generated by:

- `A_ij` with `i, j ∉ {a, b}`;
- `B_i^v := A_ib A_ia` for `i ∉ {a, b}`;
- `C_j^v := A_aj A_bj` for `j ∉ {a, b}`.

*Proof.*

- Write `v = Φ[s, e_k]` with `π = ρ(s)`, `πk = a`, `π(k+1) = b`.
- By Lemma 2.4, `P_v = P_π (PLB_{n−1})κ_k P_π^{-1}`.
- `κ_k` is a homomorphism on `PLB_{n−1}` (Lemma 2.1(d)), which is generated by the `A_pq` (M). So the
  image is generated by the elements of Lemma 5.1.
- Conjugate by `P_π`, using `π(hat_k c) ∉ {a, b}`. ∎

For a generator h in Corollary 5.2, let `S(h)` be the set of indices occurring in it: `{i, j}`,
`{i, a, b}` or `{a, b, j}`.

**Lemma 5.3 (memberships).** Let `n ≥ 6`.

- (C1') If `v = (a, b)` and `{a, b} ∩ {i, j} = ∅`, then `A_ij ∈ P_v`.
- (C1) If `{v, w}` is an edge of Q with `v = (a, b)`, `w = (c, d)`, and `{i, j}` is disjoint from
  `{a, b, c, d}`, then `A_ij ∈ P_{{v,w}}`.
- (C3) If h is a generator of `P_v` from Corollary 5.2 and `w = (c, d)` is disjoint from
  `{a, b} ∪ S(h)`, then `h ∈ P_{{v,w}}`.

*Proof.*

- **(C1')** is part of Corollary 5.2.
- **Edge stabilizers.** For an edge `[s, Γ]` of Q with `|Γ| = 2`, `π := ρ(s)`, Lemma 2.4 gives
  `P_{[s,Γ]} = P_π (PLB_{n−2})κ_Γ P_π^{-1}`.
  - `κ_Γ` is the cloning map of the forest `E(Γ)`.
  - For `Γ = {e_1, e_3}`, `E(Γ) = λ_1 λ_3 = λ_2 λ_1`, and `κ_Γ` is `κ_2` followed by `κ_1`. The first
    clones strand 2 into 2, 3; the second clones strand 1 into 1, 2.
  - For `Γ = {e_1, e_5}`, `E(Γ) = λ_1 λ_5 = λ_4 λ_1`, and `κ_Γ` is `κ_4` followed by `κ_1`.
  - The two factorizations give the same map by the (product of clonings) axiom quoted in (W1), so the
    order convention for composites does not matter.
  - The vertices of `[s, Γ]` are `[s, e_t]` for `e_t ∈ Γ`, with `Φ[s, e_t] = (πt, π(t+1))`.
- **(C1).** Choose π with `π1 = a`, `π2 = b`, `π3 = c`, `π4 = d`, `π5 = i`, `π6 = j`.
  - By Lemma 5.1, `((A_34)κ_2)κ_1 = (A_45)κ_1 = A_56`, and `A_34 ∈ PLB_{n−2}` since `n − 2 ≥ 4`.
  - So `A_ij = P_π A_56 P_π^{-1} ∈ P_{{v,w}}`.
- **(C3).** The set `S(h) \ {a, b}` has at most 2 elements and is disjoint from `{c, d}`.
  - Choose π with `π1 = a`, `π2 = b`, `π5 = c`, `π6 = d`, and `S(h) \ {a, b} ⊆ {π3, π4}`.
  - Then `h' := P_π^{-1} h P_π` is one of `A_34`, `A_43`, `A_32 A_31`, `A_42 A_41`, `A_13 A_23`,
    `A_14 A_24`. Take `Γ = {e_1, e_5}`.
  - By Lemma 5.1, applying `κ_4` and then `κ_1` (valid since `n − 2 ≥ 4`):
    - `A_23 ↦ A_23 ↦ A_34`;
    - `A_32 ↦ A_32 ↦ A_43`;
    - `A_21 ↦ A_21 ↦ A_32 A_31`;
    - `A_31 ↦ A_31 ↦ A_42 A_41`;
    - `A_12 ↦ A_12 ↦ A_13 A_23`;
    - `A_13 ↦ A_13 ↦ A_14 A_24`.
  - So `h' ∈ (PLB_{n−2})κ_Γ` and `h ∈ P_{{v,w}}`. ∎

## 6. The colimit of the stabilizers

**Theorem 6.1.** Let `n ≥ 7`, `P = PLB_n`, and let Q, `P_v`, `P_{{v,w}}` be as above. Then the natural
map `ψ: Ĝ → P` of Proposition 3.1(iv) is an isomorphism.

*Proof.*

- **Step 1: define φ on generators.**
  - For `i ≠ j`, let `V_ij` be the set of vertices `(a, b)` of Q with `{a, b} ∩ {i, j} = ∅`.
  - The full subcomplex of Q on `V_ij` is `OM(K_{[n] \ {i,j}}) ≅ OM(K_{n−2})`. It is connected by
    Proposition 4.1(a), since `n − 2 ≥ 5`.
  - Put `φ(A_ij) := ι_v(A_ij)` for any `v ∈ V_ij`, which makes sense by (C1').
  - This does not depend on v. If `v, w ∈ V_ij` are adjacent, then `A_ij ∈ P_{{v,w}}` by (C1), so
    `ι_v(A_ij) = ι_w(A_ij)` in Ĝ. Connectivity of `V_ij` finishes it.
- **Step 2: φ is a homomorphism.**
  - Let R be one of the relators R1–R3, a word in letters `A_pq` with all indices in `S(R)`,
    `|S(R)| ≤ 4`.
  - Since `n ≥ 6`, there is a vertex v of Q disjoint from `S(R)`. Every letter of R lies in `P_v` and
    `v ∈ V_pq` for every letter.
  - So φ maps R to `ι_v(R)`, where R is evaluated in `P_v ⊆ P`. There it is 1, because R is a relator
    of P.
  - By (M), φ extends to a homomorphism `φ: P → Ĝ`. On generators, `ψ ∘ φ = id_P`.
- **Step 3: φ is onto.** Ĝ is generated by the `ι_v(h)`, with h running over the generators of `P_v`
  from Corollary 5.2.
  - If `h = A_ij` with `i, j ∉ {a, b}`, then `v ∈ V_ij` and `ι_v(h) = φ(A_ij)`.
  - If `h = B_i^v = A_ib A_ia` or `h = C_j^v = A_aj A_bj`, then `|{a, b} ∪ S(h)| = 3`. So there is a
    vertex `w = (c, d)` disjoint from it (`n ≥ 5`), and w is adjacent to v.
  - By (C3), `h ∈ P_{{v,w}}`, so `ι_v(h) = ι_w(h)`.
  - Both letters of h have indices in `S(h)`, which is disjoint from `{c, d}`, so w lies in their `V_pq`.
  - Hence `ι_w(h)` is the product of the φ-images of the two letters, i.e. `φ(h)`.
- **Conclusion.** φ is onto and `ψ ∘ φ = id`, so φ is bijective and `ψ = φ^{-1}` is an isomorphism. ∎

## 7. The theorem

*Proof of the Theorem (§0).* Let `n ≥ 8`, `P = PLB_n` and `X = L_n(LB_*)`, with P acting by left
multiplication on the first coordinate. This respects dangling, since `(g g_2)^{-1}(g g_1) = g_2^{-1} g_1`.
Check the hypotheses of Proposition 3.1 for `Q = {[s, Γ] : s ∈ S_n}`:

- (i) and (ii) hold by Lemma 2.2;
- (iii) holds by Lemma 2.3 and Proposition 4.1;
- (iv) holds by Theorem 6.1.

So X is simply connected. ∎

*Proof of the Corollary.*

- By WZ Proposition 5.9 (W3) with `n = 2`, it suffices that the cloning system is properly graded, that
  `LB_k` is eventually of type `F_2`, and that `L_k(LB_*)` is eventually 1-connected.
- The first two are the established claims `loop-braid-cloning-system-is-properly-graded` and
  `loop-braid-groups-are-type-f-infinity`. The third is the Theorem. ∎

## 8. Computer checks

Scripts are in `experiments/zaremsky-2-12-loop-braided-v-type-f-infi-2026-09-16/`, with outputs saved
next to them. They are single-threaded `python3`, run under `timeout 600`.

- **`cabling.py`** (output `cabling_output.txt`). Checks, in the conventions of PG:
  - Lemma A on 400 random triples;
  - that cloning, computed letter by letter with (CS1), is well defined on elements, for all words of
    length ≤ 5 in `LB_3` and ≤ 4 in `LB_4`;
  - that R1–R3 hold for the `A_ij` for `n = 4, 5, 6`;
  - Lemma 5.1 for all `n ≤ 7`, k, p, q (350 cases).

  All printed `True`.
- **`matching_pi1.py`** (output `matching_pi1_output.txt`). For flag complexes, `π_1` is generated by
  edges, with the edges of a spanning tree and all triangles as relators. The script propagates
  triviality along triangles, and prints the `F_2`-rank of `H_1` when this is inconclusive.
  - `OM(K_8)`, `OM(K_9)` and `M(K_8)`, `M(K_9)` are certified simply connected.
  - `OM(K_5)` and `OM(K_6)` have `H_1(F_2)` of rank 41 and 46.
  - `OM(K_7)` is inconclusive, with `H_1(F_2) = 0`.
  - `M(K_5)`, `M(K_6)` have `H_1(F_2)` of rank 6 and 16, and `M(K_7)` is inconclusive.
  - `M(L_n)`, the matching complex of the path with n vertices, is certified simply connected for
    `n = 5` and `8 ≤ n ≤ 12`, and has rank-1 `H_1` for `n = 6, 7`. This is only for the remark in §9.
- **`referee_indep_check.py`** (output `referee_indep_check_output.txt`), added by the referee. It is
  written independently of `cabling.py` and checks:
  - Lemma 5.1 for all `m ≤ 7`, i.e. `n ≤ 8` (644 cases);
  - the product-of-clonings identity `κ_l` then `κ_k` = `κ_k` then `κ_{l+1}` on random words;
  - the composite memberships (C1) and (C3) for `n = 6, 7, 8`.

  All printed `True`.

## 9. Scope and what is open

- **Higher connectivity.** The method gives only simple connectivity: a colimit statement only controls
  `π_1` of the development. `L_n(LB_*)` being eventually `(k−1)`-connected for all k, which WZ
  Proposition 5.9 needs for type `F_∞` of `V_loop` (Problem 2.12), is not addressed.
  - §§2–3 exhibit X as the development of the simple complex of groups
    `σ ↦ P_π (PLB_{n−m})κ_Γ P_π^{-1}` over `OM(K_n)`. Higher connectivity of such a development needs
    more than a presentation of `PLB_n`, and nothing here provides it.
- **Small n.** Nothing is claimed for `n ≤ 7`. Proposition 5.9 only needs "eventually".
- **The pure system.** For `PLB_*` the permutation map is trivial, and the whole group `PLB_n` acts on
  `L_n(PLB_*)` with strict fundamental domain `{[1, Γ]} ≅ M(L_n)`. The analogue of §6 is not written
  out here, and `T(PLB_*)` is not the subject of Problem 2.12.
- **Inputs not re-derived.**
  - Quillen's Theorem 9.1 is used in the form of (Q); §8 checks `n = 8, 9` without it. The second
    proof of Proposition 4.1(b) replaces (Q) by the verified (HW) Proposition 3.5.
  - McCool's presentation is used through the Ershov–Zaremsky quotation (M).
  - The matching complex connectivity is used through BFMWZ (B).
