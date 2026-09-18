---
rg: 2
id: thompson-f-recurrent-f-sets-abelian-proof
kind: route
title: "Local stabilizers move three points of the singular set; a commutator trick puts the commutators of each projection into H, and a Z^3 rough embedding forces one projection to have finite index, which fills a neighbourhood of a singular point"
target: thompson-f-recurrent-f-sets-factor-through-the-abelianization
requires:
  - thompson-f-point-orbits-are-transient
  - recurrent-orbits-force-every-z3-to-meet-the-stabilizer
  - lyons-peres-energy-rough-embedding-and-polya-transience
  - thompson-f-rigid-interval-subgroups-facts
---

**Notation.**
- `F` acts on `[0,1]` as in `thompson-f-point-orbits-are-transient`. All intervals are closed with
  dyadic endpoints, unless written `int J`.
- For such `J`, `F_J` is the group of `g ∈ F` fixing `[0,1] ∖ J` pointwise. This is `F[a,b]` of
  `thompson-f-rigid-interval-subgroups-facts`. `F(J)` is its commutant `F(a,b)`, the elements that
  are the identity near both endpoints of `J` (fact (F2)).
- Let `H ≤ F` with `F/H` recurrent, and write `y = H`, so `H = Stab_F(y)`. Suppose `H ⊉ F′`. We
  derive a contradiction.

**Basic observations.**
- (O1) For `h ∈ F`, `h F_J h^(-1) = F_(h(J))`, and `h(J)` is again a dyadic interval, because `h`
  maps dyadic rationals to dyadic rationals.
- (O2) For the word `p = 01`, `[p] = [1/4,1/2]` and `F_p = F_([1/4,1/2])`; for the empty word,
  `F_p = F`. Indeed `ι_p(g) = A g A^(-1)` with `A(x) = (x+1)/4`, extended by the identity. Conjugating
  by `A` or `A^(-1)` preserves "PL with dyadic breakpoints and slopes in `2^Z`", so `ι_p(F)` is
  exactly the set of elements of `F` supported in `[p]`.
- (O3) *Recurrence passes to quotients.* Let a group with finite symmetric generating multiset `T`
  act on two transitive sets, with an equivariant surjection `q : A → B`. The walk
  `Y_n = t_n ⋯ t_1 a`, with `t_i` i.i.d. uniform in `T`, maps to the same walk `q(Y_n)` on `B`.
  Deleting loop steps only delays these walks. So if `A` is recurrent, then `B` is recurrent.
- (O4) *Heredity.* Every finitely generated `K ≤ F` acts recurrently on `K·y`. This is item 1 of
  `recurrent-orbits-force-every-z3-to-meet-the-stabilizer`, and `K·y ≅ K/(H ∩ K)`.

**Step 0 (local stabilizers move every interior point).**
- (a) `H` fixes no point of `(0,1)`.
- (b) If `J = [a,b]` with `0 < a < b < 1`, then `H ∩ F_J` fixes no point of `(a,b)`.

*Proof.* (a) is item 3 of `thompson-f-point-orbits-are-transient` with `G = F`, `θ = id` and `p`
empty.

For (b), fact (F4) gives `f ∈ F′` with `f(a) = 1/4` and `f(b) = 1/2`. Put `y′ = f·y`, so
`Stab_F(y′) = f H f^(-1)`. By (O1) and (O2),
`f (H ∩ F_J) f^(-1) = Stab_F(y′) ∩ F_([1/4,1/2]) = Stab_F(y′) ∩ F_(01)`.
If `H ∩ F_J` fixed `t ∈ (a,b)`, this group would fix `f(t) ∈ int [01]`. That contradicts item 3 of
`thompson-f-point-orbits-are-transient` with `p = 01`. ∎

**Step 1 (the singular set has at least three points).** Let `U ⊆ (0,1)` be the union of `int J`
over the dyadic intervals `J ⊆ [0,1]` with `F_J ⊆ H`, and put `S = (0,1) ∖ U`.
- By (O1), `h(U) = U` for `h ∈ H`, so `h(S) = S`.
- *Merging.* Suppose `F_([a,c]) ⊆ H` and `F_([b,d]) ⊆ H` with `a < b < c < d`. Then
  `F_([a,d]) ⊆ H` by (F3).
- *`S ≠ ∅`.* Suppose `U = (0,1)`, and take `g ∈ F′`.
  - The right slope at `0` and the left slope at `1` are homomorphisms `F → 2^Z`, so `g` has slope
    `1` at both ends. Being PL with finitely many breakpoints, `g` is the identity on `[0,c]` and on
    `[d,1]` for some dyadic `0 < c < d < 1`.
  - Cover `[c,d]` by a minimal finite family `int J_1, …, int J_k` with `F_(J_i) ⊆ H`, where
    `J_i = [a_i, c_i]` and `a_1 < a_2 < ⋯ < a_k`.
  - By minimality and connectedness of `[c,d]`, `c_1 < ⋯ < c_k` and `a_(i+1) < c_i`, so `a_1 < a_(i+1) < c_i < c_(i+1)` at each
    stage. Merging `k−1` times gives `F_([a_1,c_k]) ⊆ H`.
  - Since `[c,d] ⊆ (a_1,c_k)`, we get `g ∈ F_([a_1,c_k]) ⊆ H`. So `F′ ⊆ H`, against the hypothesis.
- *`S` is not finite.* If `S` were finite and nonempty, every `h ∈ H` would permute `S`. An
  increasing homeomorphism preserves the order of a finite set, so it fixes `S` pointwise. Then `H`
  fixes a point of `(0,1)`, against Step 0(a).

So `S` is infinite. Fix `p_1 < p_2 < p_3` in `S`.

**Step 2 (displacing elements).**
- Choose pairwise disjoint dyadic intervals `J_1, J_2, J_3 ⊆ (0,1)` with `p_i ∈ int J_i`.
- By Step 0(b), there is `n_i ∈ H ∩ F_(J_i)` with `n_i(p_i) ≠ p_i`.
- By continuity, there is a dyadic interval `I_i ⊆ J_i` with `p_i ∈ int I_i` and
  `n_i(I_i) ∩ I_i = ∅`. Also `n_i(I_i) ⊆ J_i`.

**Step 3 (the product subgroup).**
- The groups `F_(I_1), F_(I_2), F_(I_3)` have disjoint supports, so they commute and generate their
  internal direct product `K = F_(I_1) F_(I_2) F_(I_3)`.
- Each `F_(I_i) ≅ F` by (F2), so it is finitely generated. Let `T_i` be a finite symmetric
  generating multiset of `F_(I_i)`, and `T = T_1 ⊔ T_2 ⊔ T_3`.
- Let `L = H ∩ K`, let `π_i : K → F_(I_i)` be the coordinate projections, and `W_i = π_i(L)`.

**Step 4 (commutator trick): `[W_i, W_i] ⊆ H`.** Take `i = 1`; the other cases are the same. Let
`a, b ∈ W_1`, and choose `u = a u_2 u_3 ∈ L` and `v = b v_2 v_3 ∈ L` with `u_j, v_j ∈ F_(I_j)`.
Put `n = n_1` and `b′ = n b n^(-1)`.
- `b′` is supported in `n(I_1)`, which is disjoint from `I_1`. So `b′` commutes with `a` and `b`.
- `n` is supported in `J_1`, which is disjoint from `I_2 ∪ I_3`. So `n` commutes with `v_2, v_3`.
- Hence `c := n v n^(-1) v^(-1) = b′ v_2 v_3 · v_3^(-1) v_2^(-1) b^(-1) = b′ b^(-1)`. It lies in `H`,
  because `n, v ∈ H`.
- `c` is supported in `J_1`, so `u_2, u_3` commute with `c` and with `a`. Therefore
  `u c u^(-1) c^(-1) = a c a^(-1) c^(-1) = a b′ b^(-1) a^(-1) b b′^(-1) = a b^(-1) a^(-1) b`.
  The last equality holds because `b′` commutes with `a` and `b`.
- This element lies in `H`, because `u, c ∈ H`. It equals `[a, b^(-1)]`. As `a, b` range over `W_1`,
  these are all commutators of `W_1`, so `[W_1, W_1] ⊆ H`. ∎

**Step 5 (some projection has finite index).**
- *Recurrence of the product.* By (O4), `K·y ≅ K/L` is recurrent for `T`. The map
  `kL ↦ (π_i(k) W_i)_(i=1,2,3)` is well defined, because `π_i(L) = W_i`. It is a `K`-equivariant
  surjection onto `Q = ∏_i F_(I_i)/W_i`, with `K` acting coordinatewise. By (O3), `Q` is recurrent
  for `T`.
- *Structure of the product network.* Let `Γ_i = Sch(F_(I_i)/W_i, T_i)`. A generator in `T_i`
  changes only coordinate `i`. So in `Sch(Q, T)`, two vertices are joined exactly when they differ in
  one coordinate `i` by an edge of `Γ_i`, with the same conductance. Every edge has conductance
  `≥ 1`, hence resistance `≤ 1`.
- *Suppose all three `Γ_i` are infinite.*
  - Each `Γ_i` is connected, infinite and locally finite (degree `≤ |T_i|`). By König's lemma it
    contains a geodesic ray `r_i(0), r_i(1), …` of distinct vertices, with `r_i(k) ~ r_i(k+1)`.
  - Define `φ : Z^3 → Q` by `φ(x) = (r_1(|x_1|), r_2(|x_2|), r_3(|x_3|))`.
  - An edge `⟨x, x ± e_j⟩` changes `|x_j|` by exactly `1`. Let `Φ` send it to the single edge of
    `Sch(Q,T)` joining `φ(x)` and `φ(x ± e_j)` (oriented accordingly). This is a nonempty simple path
    of resistance `≤ 1`.
  - An edge of `Sch(Q,T)` changing coordinate `j` between `r_j(k)` and `r_j(k+1)`, with the other
    coordinates `r_l(m_l)`, is the image only of edges `⟨x, x′⟩` with `{|x_j|, |x′_j|} = {k, k+1}`
    and `|x_l| = m_l`. There are at most `2 · 2 · 2 = 8` unoriented such edges, so at most `16` oriented ones.
  - So `φ` is a rough embedding in the sense of `lyons-peres-energy-rough-embedding-and-polya-transience`,
    with `α = 1` and `β = 16`.
  - `Z^3` is transient (Pólya), so `Sch(Q,T)` is transient (Theorem 2.17), a contradiction.
- Hence some `Γ_i` is finite; by symmetry of the construction, say `Γ_1`. So `W_1` has finite index
  in `F_(I_1)`.

**Step 6 (the contradiction).** Write `I_1 = [a,b]` and `M = F(I_1)`, the commutant of `F_(I_1)`.
- By (F2), `F_(I_1) ≅ F`, and the isomorphism carries `M` onto `F′`, which is simple by (F1). `M` is
  nonabelian, since it contains `F_([c′,d′]) ≅ F` for dyadic `a < c′ < d′ < b`, and `F` is
  nonabelian (`F/F′ ≅ Z²` and `F′ ≠ 1`).
- `W_1 ∩ M` has finite index in `M`, so it contains a finite-index normal subgroup of `M` (its
  normal core in `M`). `M` is simple and infinite (torsion-free and nontrivial), so that core is `M`.
  Thus `M ⊆ W_1`.
- `[M, M]` is a nontrivial normal subgroup of the simple nonabelian group `M`, so `[M,M] = M`.
  Therefore `M = [M,M] ⊆ [W_1, W_1] ⊆ H`, by Step 4.
- Choose dyadic `c′ < p_1 < d′` with `[c′,d′] ⊆ int I_1`. Every element of `F_([c′,d′])` is the
  identity near `a` and near `b`, so `F_([c′,d′]) ⊆ M ⊆ H` (fact (F2) and its reading notes).
- Then `p_1 ∈ int [c′,d′] ⊆ U`, contradicting `p_1 ∈ S`.

So `H ⊇ F′`. ∎

**Remarks.**
- Only three properties of recurrence are used:
  - heredity to the finitely generated subgroups `K`, and to `F` at the conjugate base points;
  - passage to quotients;
  - failure on networks that contain a rough image of `Z^3`.
  The group theory is the displacement commutator trick (Step 4) and simplicity of `F′` (Step 6).
- This bypasses the stall recorded in the target's Attempts. Instead of one point with finite `H`-orbit
  data, it uses three separated points of the singular set `S`.
  - Step 4 turns the displacements `n_i ∈ H` into commutator subgroups inside `H`.
  - The rank-three transience of Step 5 forces one of the three local projections to be large.
