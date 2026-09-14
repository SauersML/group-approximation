# sk-free-2, part 1: 2-transitive actions and maximal subgroups of G_X (2026-09-13)

Lane sk-free-2 (wave 10, free structure lane). Status: ESTABLISHED by the proofs below, UNREVIEWED; queued with sk-verify-13.

**Setting (the note's conventions).**
- `X ⊆ A^Z` is an infinite minimal subshift with shift `T`, `R = LC(X,F_2) ⋊_T Z`, and `G = G_X = EL_3(R)`.
- Multiplication: `(f u^i)(f′ u^j) = f (f′∘T^{−i}) u^{i+j}` and `u e_U u^{−1} = e_{TU}`.
- `T` has no periodic points. So for every `L`, every point has a clopen neighbourhood `V` with `V ∩ T^j V = ∅` for `0 < |j| ≤ L`.
- `G` is simple with trivial centre (`simple-kazhdan-lef-group-from-minimal-subshift`; the centre is scalar and `F_2^× = 1`).

## 0. Two tools

**(T1) Tower matrix units** (note, §1). Let `I ⊂ Z` be an interval of length `h`, and `V ≠ ∅` clopen with `V ∩ T^jV = ∅` for `0 < |j| < h`. For `a,b ∈ I` put `ε_ab = e_{T^aV} u^{a−b}`.
- Since `u^{a−b} e_{T^{a′}V} = e_{T^{a−b+a′}V} u^{a−b}`, we get `ε_ab ε_{a′b′} = e_{T^a(V ∩ T^{a′−b}V)} u^{a−b′} = δ_{b a′} ε_{ab′}`.
- The `ε_ab` are nonzero and linearly independent (their supports `T^aV` are disjoint and nonempty).
- So `ψ(M) = Σ M_ab ε_ab` embeds `M_h(F_2)` as a ring onto the corner `eRe`, with `e = Σ_a ε_aa`.
- `ι(M) = I_3 − e I_3 + ψ(M)` is an injective homomorphism `GL_{3h}(F_2) = GL_3(M_h(F_2)) → GL_3(R)`.
- `ι(e_pq(E_ab)) = e_pq(ε_ab)` for `p ≠ q`, and `EL_3(M_h(F_2)) = SL_{3h}(F_2) = GL_{3h}(F_2)`. So `S_V := ι(GL_{3h}(F_2)) ⊆ G`.

**Product formula** (note, §1). Let `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w`, and let `c = Σ_{|a|≤w} f_a u^a`, `c′ = Σ_{|b|≤w} f′_b u^b`, with each `f_a` constant on `T^aV` (value `α_a`) and each `f′_b` constant on `V` (value `β_b`). Then, with `I = [−w,w]`:
`c e_V c′ = Σ_{a,b} f_a e_{T^aV} (f′_b∘T^{−a}) u^{a+b} = Σ_{a,b} α_a β_b ε_{a,−b}`.
This is nonzero iff `α ≠ 0` and `β ≠ 0`.

**(T2) Orbit modules.** For `x ∈ X` let `V_x = F_2[Z]` (finite support), with `f δ_n = f(T^n x) δ_n` and `u δ_n = δ_{n+1}`.
- `u f u^{−1} δ_n = f(T^{n−1}x) δ_n = (f∘T^{−1}) δ_n`. So `V_x` is a left `R`-module, and `G` acts on column vectors `V_x^3`.
- `ε_ab δ_m = e_{T^aV} δ_{m+a−b} = [T^{m−b}x ∈ V] δ_{m−b+a}`.
- The set `N = {n : T^n x ∈ V}` has gaps `≥ h`. So for `I = [0,h)` the blocks `W_n = span{δ_{n+c} : 0 ≤ c < h}`, `n ∈ N`, are pairwise disjoint.
- `ψ(M)` acts on every block as the matrix `M` and kills every `δ_m` outside the blocks. For `m = n+b′` with `n ∈ N`, `T^{n+b′−b}x ∈ V` forces `b′ = b`.
- So `ι(M)` acts on every `W_n^3` as `M` and as the identity elsewhere.

## 1. Theorem A: linear-independence transitivity on orbit modules

**Theorem A.** For every `x ∈ X` and `k ≥ 1`, `G` acts transitively on ordered `k`-tuples of linearly independent vectors of `V_x^3`. In particular `G` acts faithfully and 2-transitively on the countably infinite set `Ω_x = V_x^3 ∖ {0}`.

*Proof.*
- Let `(v_i)` and `(w_i)` be independent `k`-tuples, all supported in positions `[p, p+L)`.
- Choose a clopen `V ∋ T^p x` with `V ∩ T^jV = ∅` for `0 < |j| < L`, and take `h = L`, `I = [0,L)`. The block `W_p` contains every support.
- `GL_{3L}(F_2)` is transitive on independent `k`-tuples of `F_2^{3L}` (extend both to bases). Pick `M` with `M v_i = w_i` on `W_p^3`.
- All `v_i, w_i` vanish off `W_p^3`, so `ι(M) v_i = w_i`, and `ι(M) ∈ G`.
- Faithful: the action is nontrivial, since `e_12(1)(δ_0 e_2) = δ_0 e_1 + δ_0 e_2`. Its kernel is a proper normal subgroup, so it is trivial because `G` is simple.
- Over `F_2`, distinct nonzero vectors are independent, so `k = 2` gives 2-transitivity. ∎

## 2. Theorem B: continuum many conjugacy classes of maximal subgroups

**Theorem B.** `H_x := Stab_G(δ_0 e_1 ∈ V_x^3)` is a maximal subgroup of `G` of infinite index, and `x ↦ H_x` is injective. Consequences:
- `G` has continuum many conjugacy classes of maximal subgroups;
- `G` has continuum many pairwise non-isomorphic faithful 2-transitive actions on countable sets.

*Proof.*
- A 2-transitive action is primitive, so point stabilizers are maximal: if `H_x < K < G`, the `K`-orbit of `δ_0 e_1` would be a nontrivial block.
- The index is `|Ω_x| = ℵ_0`.
- For `f ∈ LC(X,F_2)`, `e_21(f)(δ_0e_1) = δ_0 e_1 + f(x) δ_0 e_2`, so `e_21(f) ∈ H_x ⟺ f(x) = 0`. If `x ≠ y`, a clopen `U ∋ y` with `x ∉ U` gives `e_21(e_U) ∈ H_x ∖ H_y`.
- `X` is a nonempty perfect compact metrizable space, hence of cardinality continuum. `G` is countable, so each conjugacy class of subgroups is countable. Hence there are continuum many classes.
- Transitive `G`-sets are isomorphic iff their point stabilizers are conjugate. ∎

*Remarks.*
- `δ_n ↦ δ_{n−1}` is an `R`-module isomorphism `V_x → V_{Tx}`. So `H_{Tx}` is the stabilizer of `δ_{−1}e_1` in `V_x^3`, which is conjugate to `H_x` by Theorem A.
- **Open:** is `H_x` conjugate to `H_y` only when `x` and `y` lie in one orbit?
- **Model tests.**
  - Finite models `SL_{3N}(F_2)` acting on `F_2^{3N}`: classical.
  - `EL_3(F_2[u^{±1}])` (the one-point system): `δ_0 e_1` is unimodular and `(1+u)e_1` is not, so transitivity fails. The step that fails is exactly the choice of `V` with disjoint translates, which needs aperiodicity.

## 3. Theorem C: the parabolic subgroups are maximal

**Theorem C.** `P = {g ∈ G : g_21 = g_31 = 0}`, the stabilizer of the summand `e_1R` of `R^3`, is a maximal subgroup of `G`. So is `P′ = {g ∈ G : g_31 = g_32 = 0}`, the stabilizer of `e_1R ⊕ e_2R`.

**Lemma C1 (finite).** Let `1 ≤ m < n`, let `U ⊆ F_2^n` have dimension `m`, and let `Q = Stab_{GL_n(F_2)}(U)`. Then `Q` is a maximal subgroup of `GL_n(F_2)`.

*Proof.*
- For `m`-subspaces put `d(A,B) = m − dim(A∩B)`. Adapted bases show that `GL_n` is transitive on pairs at each distance, so `Q` is transitive on each sphere `S_t(U)`.
- Let `Q < H`. The orbit `Ω = HU` is a union of spheres and contains some `S_t(U)` with `t ≥ 1`.
- **We show `S_1(U) ⊆ Ω`.** Take `B ∈ S_t(U)` and `h ∈ H` with `hU = B`. Then `h S_t(U) = S_t(B) ⊆ Ω`. Write `U = W ⊕ U_1`, `B = W ⊕ B_1`, with `W = U ∩ B`, `dim U_1 = t` and `U_1 = U_1′ ⊕ ⟨a⟩`. A `C ∈ S_t(B)` with `d(U,C) = 1` exists in each case:
  - `m + t < n`: pick `c ∉ U + B` and put `C = W ⊕ U_1′ ⊕ ⟨c⟩`;
  - `m + t = n` and `t < m`: write `W = W′ ⊕ ⟨w⟩`, pick `0 ≠ b ∈ B_1`, and put `C = W′ ⊕ U_1 ⊕ ⟨b⟩`. Then `U ∩ C = W′ ⊕ U_1` and `B ∩ C = W′ ⊕ ⟨b⟩`;
  - `t = m = n − m`: pick `0 ≠ b ∈ B` and put `C = U_1′ ⊕ ⟨a+b⟩`. Then `U ∩ C = U_1′` and `B ∩ C = 0`.
- Applying elements of `H` gives `S_1(A) ⊆ Ω` for all `A ∈ Ω`. The Grassmann graph is connected, so `Ω` is everything.
- `Stab_H(U) = Q`, so `|H| = |Ω|·|Q| = |GL_n(F_2)|`. ∎

**Lemma C2 (Whitehead, characteristic 2).**
- For a unit `v`: `e_12(v) e_21(v^{−1}) e_12(v) = [[0,v],[v^{−1},0]]` (since `1 + vv^{−1} = 0`), and `e_12(1)e_21(1)e_12(1) = [[0,1],[1,0]]`. Their product is `diag(v, v^{−1}, 1) ∈ G`.
- The same holds in other coordinate pairs. So `diag(1, u^{−s}, u^s) ∈ P ∩ G` for all `s`.

*Proof of Theorem C for `P`.* Let `P < H ≤ G` and `g ∈ H ∖ P`.

**Step 1: indices.**
- `g ∉ P` gives `i ∈ {2,3}` with `g_{i1} ≠ 0`.
- `g^{−1} ∉ P` gives `l ∈ {2,3}` with `(g^{−1})_{l1} ≠ 0`.
- For `c = Σ f_a u^a ≠ 0` put `S(c) = ⋃_a T^{−a}(supp f_a)` and `S′(c) = ⋃_a supp f_a`. Both are nonempty clopen sets.

**Step 2: aligning supports.**
- Let `p = diag(1, d_2, d_3) ∈ P ∩ G` with `d_l = u^{−s}` and the other entry `u^s` (Lemma C2). Put `g′ = g p ∈ H ∖ P`.
- Then `g′_{i1} = g_{i1}` and `(g′^{−1})_{l1} = u^s (g^{−1})_{l1}`.
- Since `u^s Σ f′_b u^b = Σ (f′_b∘T^{−s}) u^{s+b}`, we get `S′((g′^{−1})_{l1}) = T^s S′((g^{−1})_{l1})`.
- By minimality, some `s` makes `Wd = S(g_{i1}) ∩ T^s S′((g^{−1})_{l1})` nonempty.

**Step 3: a commutator in a finite group.**
- Let `w` bound the degrees of all entries of `g′` and `g′^{−1}`.
- Choose a nonempty clopen `V ⊆ Wd` with `V ∩ T^jV = ∅` for `0 < |j| ≤ 2w`, such that every coefficient of those entries is constant on each `T^aV`, `|a| ≤ w`. Take `I = [−w,w]` and `S = S_V`.
- Put `h = e_{1l}(e_V) = ι(I + E_{00} E_{1l}) ∈ P ∩ S`. By the product formula, `g′ h g′^{−1} = I + A` with `A_{pq} = g′_{p1} e_V (g′^{−1})_{lq} ∈ span{ε_ab}`. So `g′hg′^{−1} ∈ ι(GL_{3(2w+1)}(F_2))`, and `k = g′ h g′^{−1} h^{−1} ∈ H ∩ S`.
- `h^{−1} − I` has only a `(1,l)` entry, so column 1 of `k` equals column 1 of `I + A`. Hence `k_{i1} = g′_{i1} e_V (g′^{−1})_{l1} = Σ α_a β_b ε_{a,−b}`.
- `V ⊆ S(g′_{i1})` gives `α ≠ 0`, and `V ⊆ S′((g′^{−1})_{l1})` gives `β ≠ 0`. So `k_{i1} ≠ 0` and `k ∉ P`.

**Step 4: finite maximality.**
- `ι(M) ∈ P` iff the blocks `M_21` and `M_31` vanish, i.e. iff `M ∈ Q = Stab(F_2^I ⊗ e_1)`.
- `H ∩ S ⊇ ι(Q)` and `k ∈ (H ∩ S) ∖ ι(Q)`, so Lemma C1 gives `H ∩ S = S`. In particular `e_21(e_V) = e_21(ε_00) ∈ H`.

**Step 5: level ideal.** Let `J = {r ∈ R : e_21(r) ∈ H}`. It is additive.
- `[e_32(t), e_21(r)] = e_31(tr)` and `[e_23(t), e_31(r′)] = e_21(t r′)`, with `e_32(t), e_23(t) ∈ P`. So `RJ ⊆ J`.
- `diag(v,v^{−1},1) e_21(r) diag(v,v^{−1},1)^{−1} = e_21(v^{−1} r v^{−1})` with `diag(v,v^{−1},1) ∈ P`. Together with `RJ ⊆ J`, this gives `J v ⊆ J` for every unit `v`.
- So `e_{T^jV} = u^j e_V u^{−j} ∈ J` for all `j`, and `e_{U∪U′} = e_U + e_{U′} + e_U e_{U′} ∈ J`. Finitely many `T^jV` cover `X` by minimality, so `1 ∈ J` and `J = R`.
- Then `e_31(R) ⊆ H` by the first identity, and `P ∋ e_12(r), e_13(r), e_23(r), e_32(r)`. So `H ⊇` all elementary generators, and `H = G`. ∎

*`P′`.* Rows and columns swap roles. Let `P′ < H` and `g ∈ H ∖ P′`.
- **Indices.** `g ∉ P′` gives `j ∈ {1,2}` with `g_{3j} ≠ 0`, and `g^{−1} ∉ P′` gives `l ∈ {1,2}` with `(g^{−1})_{3l} ≠ 0`.
- **Alignment.** Take `p = diag(d_1, d_2, 1) ∈ P′ ∩ G` with `d_l = u^{−s}` and the other entry `u^s`, and put `g′ = p g`. Then `g′_{3q} = g_{3q}` and `(g′^{−1})_{3l} = (g^{−1})_{3l} u^s`, whose support set `S` is `T^{−s}` of the old one. Choose `s` so that `S((g′^{−1})_{3l}) ∩ S′(g_{3j}) ≠ ∅`.
- **Finite group.** Choose `V` in that set as before, and put `h = e_{l3}(e_V) ∈ P′ ∩ S` and `k = h^{−1} (g′^{−1} h g′) ∈ H ∩ S`.
  - Row 3 of `h^{−1}` is `e_3^T`, so row 3 of `k` is row 3 of `I + g′^{−1} e_V E_{l3} g′`.
  - Hence `k_{3j} = (g′^{−1})_{3l} e_V g′_{3j} ≠ 0` by the product formula, and `k ∉ P′`.
- **Grassmann.** `S ∩ P′ = ι(Stab(F_2^I ⊗ (e_1 ⊕ e_2)))`, so Lemma C1 gives `H ∩ S = S` and `e_32(e_V) ∈ H`.
- **Level ideal.** `J′ = {r : e_32(r) ∈ H}` is additive.
  - `[e_32(r), e_21(t)] = e_31(rt)` and `[e_31(r″), e_12(t′)] = e_32(r″t′)`, with `e_21, e_12 ∈ P′`. So `J′R ⊆ J′`.
  - Conjugation by `diag(1,v,v^{−1}) ∈ P′` gives `e_32(v^{−1} r v^{−1})`, so `vJ′ ⊆ J′` for units `v`.
  - So `e_{T^jV} = u^j e_V u^{−j} ∈ J′`. `J′` is closed under unions of clopen idempotents, so `1 ∈ J′` and `J′ = R`.
- **Conclusion.** `H ⊇ e_32(R), e_31(R)`, and `P′ ⊇ e_12(R), e_13(R), e_21(R), e_23(R)`. So `H = G`. ∎

## 4. Scope, credit and what is not claimed
- **Hypotheses used:**
  - aperiodicity, for the neighbourhoods `V` with disjoint translates (Theorems A–C);
  - minimality, for aligning supports and covering (C) and for simplicity (faithfulness in A);
  - coefficients in `F_2`, for `GL = SL`, `F_2^× = 1` and the Whitehead identities in the form used.
- **Other fields and `n`:** the same proofs should give EL_n, n ≥ 3, with every parabolic `P_m`, and `F_q` modulo the centre with `SL_d`. Not written; not claimed.
- **Credit.**
  - Over fields, stabilizers of subspaces are maximal (Tits systems; Aschbacher class C_1).
  - Continuum many maximal subgroups of infinite index for f.g. linear non-virtually-solvable groups: Margulis–Soifer (profinite method). `G_X` is not residually finite, and the orbit-module mechanism here is different.
  - Novelty check: main-graph grep only (tip 853d35312b; "maximal subgroup", "2-transitive", "primitive action", "orbit module"). No literature search yet.
- **Next (part 2):**
  - stabilizers of non-free summands `e_1 e_W R`;
  - which maximal subgroups contain `U_12 = e_12(R)`;
  - whether `H_x ∼ H_y` iff `x ∼ y`.
