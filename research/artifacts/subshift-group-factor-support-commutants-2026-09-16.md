# Support subalgebras of L(G_X) are mutual relative commutants

Lane `swarm-subshift-group-factors-determi`, 2026-09-16. Unreviewed.

This artifact proves claim `subshift-group-factor-supports-are-relative-commutants` along route
`subshift-group-factor-support-commutants-proof`. It uses two claims of the graph:

- **(RS)** `subshift-elementary-group-rigid-supports-are-mutual-centralizers`, items 3 and 4:
  - `C_G(L_(X∖U)) = G_U` for every clopen `U`;
  - `L = GL_3(A) ≤ G`.
- **(NO)** `locally-constant-simple-group-normal-subgroups-are-open-sets`. For a Cantor space `Z` and a finite
  nonabelian simple group `Q`, every normal subgroup of `LC(Z,Q)` is `N_O = {f : supp f ⊆ O}` for an open `O ⊆ Z`.

Everything else is proved here. The facts about group von Neumann algebras used in §2 are textbook facts: the trace,
Parseval, the trace-preserving conditional expectation and the separating vector `δ_e`.

## 0. Setting and conventions

- `X` is an infinite minimal subshift with shift `T`.
- `A = LC(X,F_2)` and `R = A ⋊_T Z` with `u f u^(-1) = f∘T^(-1)`, as in the rigid-supports artifact. So
  `u^j e_V u^(-j) = e_(T^jV)` for clopen `V`, where `e_V ∈ A` is the indicator of `V`.
- Every `r ∈ R` has a unique expression as a finite sum `r = Σ_n f_n u^n` with `f_n ∈ A`.
- `G = G_X = EL_3(R)`, and `L = GL_3(A) = LC(X,Q)` with `Q = GL_3(F_2)`. `Q` is the finite simple group of order
  168, and `L ≤ G` by (RS).
- For clopen `U`:
  - `G_U = G ∩ (I + M_3(e_U R e_U))`;
  - `L_U = {l ∈ L : l ≡ I off U}`;
  - `supp l = {x : l(x) ≠ I}`, which is clopen.
- `M = L(G)` acts on `ℓ²(G)`, with trace `τ(x) = ⟨xδ_e, δ_e⟩` and canonical unitaries `λ_g`.
  - The Fourier coefficients of `x ∈ M` are `x̂(g) = τ(xλ_g^*) = ⟨xδ_e, δ_g⟩`, so `xδ_e = Σ_g x̂(g)δ_g`.
  - For a subgroup `S ≤ G`, `L(S) = λ(S)''`, a copy of the group von Neumann algebra of `S`.
- `N_U = L(G_U)`.

For an idempotent `e ∈ R` and `s ∈ R`, we have `s ∈ eRe` iff `(1−e)s = 0 = s(1−e)`. Indeed `s = ese` gives both
equations, and conversely `s = es = se` gives `s = ese`.

## 1. Two topological facts

**Lemma 1.1.**
- (i) `X` has no isolated points.
- (ii) Every nonempty clopen `U ⊆ X` is a Cantor space.
- (iii) `X` has only countably many clopen subsets.

*Proof.*
- `X` is a closed subset of a full shift over a finite alphabet. So it is compact, metrizable and totally
  disconnected, and the cylinder sets form a countable basis of clopen sets.
- (iii): a clopen set is compact, hence a finite union of cylinders, so there are only countably many.
- (i): suppose `x` is isolated.
  - By minimality every orbit is dense, so every orbit meets the open set `{x}`, and `X = {T^n x : n ∈ Z}`.
  - Each `T^n x` is isolated, since `T` is a homeomorphism. So `X` is discrete and compact, hence finite, which is
    a contradiction.
- (ii): a nonempty clopen `U` is compact, metrizable and totally disconnected. An isolated point of `U` would be
  isolated in `X`, because `U` is open. By Brouwer's characterization (textbook), `U` is a Cantor space. ∎

**Lemma 1.2.** Let `U ⊆ X` be open, `F ⊆ X` finite and `f: X → F_2` locally constant with `f = 0` on `U∖F`. Then
`f = 0` on `U`.

*Proof.* Take `p ∈ U`. `f` is constant on some open `W ∋ p`, and `W ∩ U` is an open neighbourhood of `p`. It is
infinite, since a finite open set in a Hausdorff space consists of isolated points, and there are none by 1.1(i). So
`W ∩ U` meets `U∖F`, and `f(p) = 0`. ∎

## 2. Fourier support of relative commutants

**Lemma 2.1.** Let `H ≤ G` and `x ∈ L(H)' ∩ M`. Then `x̂(hgh^(-1)) = x̂(g)` for all `h ∈ H` and `g ∈ G`. So if
`x̂(g) ≠ 0`, the centralizer `C_H(g)` has finite index in `H`.

*Proof.* Since `λ_h^* x λ_h = x`, the trace property gives
`τ(x λ_(hgh^(-1))^*) = τ(x λ_h λ_g^* λ_h^*) = τ(λ_h^* x λ_h λ_g^*) = τ(x λ_g^*)`.

By Parseval, `Σ_g |x̂(g)|² = ‖xδ_e‖² < ∞`. So a nonzero constant value is taken only on a finite `H`-conjugacy class,
and the class of `g` is in bijection with `H/C_H(g)`. ∎

**Lemma 2.2.** Let `S ≤ G`.
- (i) If `x ∈ L(S)`, then `x̂(g) = 0` for `g ∉ S`.
- (ii) If `x ∈ M` and `x̂(g) = 0` for all `g ∉ S`, then `x ∈ L(S)`.
- (iii) `L(S_1) ∩ L(S_2) = L(S_1 ∩ S_2)`, and `L(S_1) = L(S_2)` iff `S_1 = S_2`.

*Proof.*
- (i): `L(S)` is the strong closure of `span λ(S)`, and `yδ_e ∈ ℓ²(S)` for `y` in the span. Strong limits preserve
  this, because `ℓ²(S)` is closed.
- (ii): let `E: M → L(S)` be the trace-preserving conditional expectation, which is the restriction of the orthogonal
  projection `e_S` onto `ℓ²(S)`: `E(x)δ_e = e_S(xδ_e)`.
  - By hypothesis `e_S(xδ_e) = xδ_e`, so `(x − E(x))δ_e = 0`.
  - `δ_e` is cyclic for the right regular representation, which lies in `M'`, so `δ_e` is separating for `M`.
  - Hence `x = E(x) ∈ L(S)`.
- (iii) follows from (i) and (ii), since `λ_g` has Fourier support `{g}`. ∎

## 3. Finite-index subgroups of LC(Z,Q)

**Lemma 3.1.** Let `Z` be a Cantor space, `Q` a finite nonabelian simple group, and `H ≤ K = LC(Z,Q)` a subgroup of
finite index. Then there is a finite `F ⊆ Z` such that every `f ∈ K` with `supp f ∩ F = ∅` lies in `H`.

*Proof.*
- Let `N = ⋂_(k∈K) kHk^(-1)`, the kernel of the action of `K` on `K/H`. It is normal of finite index.
- By (NO), `N = N_O` for an open `O ⊆ Z`. Put `F = Z∖O`.
- Let `p_1, …, p_r ∈ F` be distinct, and choose pairwise disjoint clopen `W_i ∋ p_i`.
  - For `q = (q_1, …, q_r) ∈ Q^r`, let `l_q ∈ K` equal `q_i` on `W_i` and `1` off `⋃W_i`.
  - If `q ≠ q'`, then `l_q l_(q')^(-1)` takes the value `q_i q_i'^(-1) ≠ 1` at some `p_i ∉ O`. So it is not in `N_O`.
  - Hence the `|Q|^r` elements `l_q` lie in distinct cosets of `N`, and `|Q|^r ≤ [K:N]`.
- So `F` is finite.
- If `supp f ∩ F = ∅`, then `supp f ⊆ O`, so `f ∈ N ⊆ H`. ∎

## 4. Support subgroups

**Lemma 4.1 (intersection).** Let `U ⊆ X` be clopen, `F ⊆ X` finite, and `𝒱` the set of clopen `V ⊆ U∖F`. Then
`⋂_(V∈𝒱) G_(X∖V) = G_(X∖U)`.

*Proof.* If `U = ∅`, both sides equal `G`, so assume `U ≠ ∅`.

**⊇.** For `V ⊆ U`, we have `e_(X∖U) = e_(X∖V) e_(X∖U) = e_(X∖U) e_(X∖V)`. So
`e_(X∖U) R e_(X∖U) ⊆ e_(X∖V) R e_(X∖V)`.

**⊆.** Let `g` lie in the intersection and let `r = Σ_n f_n u^n` be an entry of `g − I`. By §0, `e_V r = 0` and
`r e_V = 0` for all `V ∈ 𝒱`.

- **Left.** `e_V r = Σ_n (e_V f_n) u^n = 0` gives `e_V f_n = 0` for all `n`, by uniqueness of the expansion.
  - `U∖F` is open, so it is the union of the clopen sets it contains. So `f_n = 0` on `U∖F`, hence on `U` by
    Lemma 1.2.
  - So `e_U r = 0`.
- **Right.** `r e_V = Σ_n f_n e_(T^nV) u^n = 0` gives `f_n = 0` on `T^nV`, that is `f_n∘T^n = 0` on `V`, for all
  `V ∈ 𝒱`.
  - So `f_n∘T^n` vanishes on `U∖F`, hence on `U` by Lemma 1.2, applied to the locally constant function
    `f_n∘T^n`.
  - So `f_n e_(T^nU) = 0` and `r e_U = Σ_n f_n e_(T^nU) u^n = 0`.

By §0, `r ∈ e_(X∖U) R e_(X∖U)` for every entry. Since `g ∈ G`, we get `g ∈ G_(X∖U)`. ∎

**Lemma 4.2.** For clopen `U, V`:
- (i) `G_U ∩ G_V = G_(U∩V)`.
- (ii) Elements of `G_U` and `G_(X∖U)` commute, and `G_U ∩ G_(X∖U) = {I}`.
- (iii) `L_U ≤ G_U`, `L_U ∩ G_V = L_(U∩V)`, and restriction `l ↦ l|_U` is an isomorphism `L_U → LC(U,Q)` with the
  same supports.

*Proof.*
- (i): if `s = e_U s e_U = e_V s e_V`, then `e_(U∩V) s e_(U∩V) = e_U e_V s e_V e_U = e_U s e_U = s`. Conversely,
  `s = e_(U∩V) s e_(U∩V)` gives `e_U s e_U = s`, and likewise for `V`. Apply this entrywise.
- (ii): for `g ∈ G_U` and `h ∈ G_(X∖U)`, the entries of `(g−I)(h−I)` lie in `e_U R e_U · e_(X∖U) R e_(X∖U) = 0`,
  and similarly for `(h−I)(g−I)`. So `gh = I + (g−I) + (h−I) = hg`. The intersection is `G_∅ = {I}` by (i).
- (iii):
  - `l ∈ L_U` lies in `G` by (RS), and the entries of `l − I` lie in `e_U A = e_U A e_U ⊆ e_U R e_U`.
  - For `l ∈ L_U ∩ G_V`, each entry `a ∈ e_U A` of `l − I` satisfies `a = e_V a e_V = e_V a`, since `A` is
    commutative. So `a` vanishes off `U ∩ V`, and `l ∈ L_(U∩V)`. The reverse inclusion is immediate.
  - The last statement is immediate. ∎

## 5. The theorem

**Theorem 5.1.** For all clopen `U, V ⊆ X`:
- (a) `L(L_U)' ∩ M = N_(X∖U)`.
- (b) `N_U' ∩ M = N_(X∖U)`, and hence `(N_U' ∩ M)' ∩ M = N_U`.
- (c) The support subalgebras behave like a Boolean algebra:
  - `N_U ∩ N_V = N_(U∩V)` and `(N_U ∨ N_V)' ∩ M = N_(X∖(U∪V))`;
  - `U ↦ N_U` is injective;
  - for `U ≠ ∅`, `N_U` is a II_1 factor, equivalently `G_U` is ICC.
- (d) `N_U ∨ N_(X∖U) ≅ N_U ⊗̄ N_(X∖U)`, and `(N_U ∨ N_(X∖U))' ∩ M = C`.
- (e) `L(L)' ∩ M = C`, and `L(L)` is the weak closure of an increasing union of finite-dimensional *-subalgebras. So
  `L(L)` is an irreducible hyperfinite II_1 subfactor of `M`. By Murray–von Neumann uniqueness it is `≅ R`; this is
  recalled and not used.

*Proof of (a).* By Lemma 4.2(ii),(iii), the unitaries `λ(G_(X∖U))` commute with `λ(G_U) ⊇ λ(L_U)`. This gives the
chain

`N_(X∖U) ⊆ N_U' ∩ M ⊆ L(L_U)' ∩ M`. (★)

Now let `x ∈ L(L_U)' ∩ M`. If `U = ∅`, then `L_∅ = {I}` and `N_X = L(G) = M`, so there is nothing to prove. Let
`U ≠ ∅` and let `g ∈ G` with `x̂(g) ≠ 0`.
1. By Lemma 2.1 with `H = L_U`, the centralizer `C_(L_U)(g)` has finite index in `L_U`.
2. By Lemma 1.1(ii), `U` is a Cantor space. Lemma 3.1, transported along `L_U ≅ LC(U,Q)` (Lemma 4.2(iii)), gives a
   finite `F ⊆ U` such that every `l ∈ L_U` with `supp l ∩ F = ∅` commutes with `g`.
3. For every clopen `V ⊆ U∖F`, `L_V ⊆ C_(L_U)(g)`. So `g ∈ C_G(L_V) = G_(X∖V)`, by (RS) applied to the clopen set
   `X∖V`.
4. By Lemma 4.1, `g ∈ G_(X∖U)`.

So `x̂` is supported in `G_(X∖U)`, and `x ∈ N_(X∖U)` by Lemma 2.2(ii). With (★), all three algebras in (★) are equal.

*Proof of (b).* The first equation is (★). Applying it to `X∖U` gives `N_(X∖U)' ∩ M = N_U`.

*Proof of (c).*
- By Lemma 2.2(iii) and Lemma 4.2(i), `N_U ∩ N_V = L(G_U ∩ G_V) = N_(U∩V)`.
- The relative commutant of a join is the intersection of the relative commutants. So by (b) and the meet formula,
  `(N_U ∨ N_V)' ∩ M = N_(X∖U) ∩ N_(X∖V) = N_(X∖(U∪V))`.
- **Injectivity.** If `U ≠ V`, say `W = U∖V ≠ ∅`. Then:
  - `L_W ⊆ L_U ⊆ G_U`, and `L_W ≠ {I}`;
  - `L_W ∩ G_V = L_∅ = {I}` by Lemma 4.2(iii);
  - so `G_U ≠ G_V`, and `N_U ≠ N_V` by Lemma 2.2(iii).
- **Factor.** The centre of `N_U` lies in `N_U ∩ (N_U' ∩ M) = N_U ∩ N_(X∖U) = N_∅ = C`.
  - For `U ≠ ∅`, `G_U ⊇ L_U ≅ LC(U,Q)` is infinite, so `N_U` is an infinite-dimensional factor with a faithful normal
    tracial state, hence of type II_1.
  - A group von Neumann algebra is a factor iff the group is ICC (textbook).

*Proof of (d).*
- By Lemma 4.2(ii), multiplication `G_U × G_(X∖U) → P = G_U G_(X∖U)` is a group isomorphism.
- `L(P)` is generated by `λ(G_U) ∪ λ(G_(X∖U))`, so `L(P) = N_U ∨ N_(X∖U)`.
- `L(G_1 × G_2) ≅ L(G_1) ⊗̄ L(G_2)` via `ℓ²(G_1 × G_2) = ℓ²(G_1) ⊗ ℓ²(G_2)`.
- By (c), `(N_U ∨ N_(X∖U))' ∩ M = N_(X∖U) ∩ N_U = N_∅ = C`.

*Proof of (e).*
- (a) with `U = X` gives `L(L)' ∩ M = N_∅ = C`.
- By Lemma 1.1(iii), enumerate the clopen sets `W_1, W_2, …`. Let `P_n` be the finite partition generated by
  `W_1, …, W_n`, and `L^(n) ≤ L` the finite group of maps constant on the atoms of `P_n`.
- The `L^(n)` increase. Their union is `L`, because the finitely many level sets of `l ∈ L` are clopen, hence all
  among `W_1, …, W_n` for some `n`.
- So `span ⋃_n λ(L^(n))` is a strongly dense *-subalgebra of `L(L)` and an increasing union of finite-dimensional
  algebras `L(L^(n))`.
- Irreducibility makes `L(L)` a factor, and `L` is infinite, so `L(L)` is of type II_1. ∎

## 6. Transport along diagonal subalgebras

**Corollary 6.1.** Let `X, Y` be infinite minimal subshifts, `θ: L(G_X) → L(G_Y)` a *-isomorphism, and `U ⊆ X`,
`U' ⊆ Y` clopen with `θ(L(L^X_U)) = L(L^Y_(U'))`. Then:
- `θ(N^X_(X∖U)) = N^Y_(Y∖U')`;
- `θ(N^X_U) = N^Y_(U')`.

Suppose moreover that `β: Clop(X) → Clop(Y)` satisfies `θ(L(L^X_U)) = L(L^Y_(β(U)))` for all `U`. Then `β` is an
injective map preserving `∅`, complements and intersections, i.e. a Boolean algebra embedding.

*Proof.*
- A *-isomorphism carries relative commutants to relative commutants: `θ(P' ∩ M_X) = θ(P)' ∩ M_Y`.
- Apply (a) to `U` and `U'` to get the first equation, then (b) to `X∖U` and `Y∖U'` to get the second.
- For the second statement:
  - The two expressions `θ(N^X_(X∖U)) = N^Y_(Y∖β(U))` and `= N^Y_(β(X∖U))` agree, so injectivity in (c) gives
    `β(X∖U) = Y∖β(U)`.
  - Similarly `θ(N^X_(U∩V)) = θ(N^X_U) ∩ θ(N^X_V) = N^Y_(β(U)∩β(V))` gives `β(U∩V) = β(U) ∩ β(V)`.
  - Finally, `θ(C) = C` gives `β(∅) = ∅`, and injectivity follows from (c) and injectivity of `θ`. ∎

## 7. What is not claimed

- Nothing here says that an arbitrary isomorphism `θ: L(G_X) → L(G_Y)` maps `L(L^X)` or any `L(L^X_U)` to an
  algebra of the same form, even up to unitary conjugacy.
  - The theorem describes the pair `(M, λ(G))`, not an invariant of `M` alone.
  - The session notes record that the automorphisms `Θ_k` of `subshift-group-factor-out-contains-z` already move
    some `N_U` off the family `{N_(U')}`.
- Corollary 6.1 yields only a Boolean algebra embedding. All Cantor spaces are homeomorphic, so this carries no
  information about `T`.
- Theorem 5.1 does not compute the normalizer `N_M(L(L))`, nor the one-sided or quasi-normalizers of `N_U`.
