---
rg: 2
id: punctured-cone-covered-actors-evaluation-ideal-proof
kind: route
title: Punctures add only evaluation operators, which form an ideal complementary to the Leavitt algebra whose unit kernel is locally finite, and graph-shift inputs are torsion-free
target: punctured-cone-covered-actors-are-locally-finite-by-leavitt
requires:
  - diagonal-cone-covered-actors-lie-in-binary-leavitt-unit-group
  - leavitt-algebras-l-k-1-n-are-simple
  - binary-leavitt-unit-word-problem-decidable
  - thompson-steinberg-presentation-of-leavitt-unit-group
  - graph-shift-groups-have-arbitrarily-hard-word-problem
  - hnn-torsion-theorem
---

Notation as in the target. Additive maps `M -> M` are `F_2`-linear. "Lemma 1" and "the
relations" refer to `diagonal-cone-covered-actors-leavitt-commutant-proof`, the derivation of
`diagonal-cone-covered-actors-lie-in-binary-leavitt-unit-group`. Every nonempty clopen subset
of `C` is infinite, and a clopen set avoiding a finite set `P` is a finite union of cones
avoiding `P`.

## Lemma A: tameness

**(i) Upward closure.** Let `H <= H' <= V` with `H` tame for `P`. Then:
- `M^(H') ⊆ M^H = F_2·1`, and constants are `V`-invariant;
- the span of the `h f - f` only grows;
- `End_(H')(M) ⊆ End_H(M)`.

**(ii) `P = ∅`.** A clopen-rigid `H` is tame with `P = ∅`, by Lemma 1(a), (b), (c):
`span{hf - f} = M = ker(ev_∅)`.

**(iii) `V^(P)` is tame for finite nonempty `P`.** Put `H = V^(P)`.

- **Swaps.** If `x, y ∉ P` are distinct, there are disjoint cones `[u] ∋ x`, `[u'] ∋ y`
  avoiding `P`, with `|u| = |u'|`. The prefix replacement exchanging them lies in `H`.
- **Transitivity.** `H` is transitive on nonempty clopen sets avoiding `P`. Given two such
  sets `A, B`, choose a clopen neighbourhood `N` of `P` disjoint from `A ∪ B`, small enough
  that `C∖(N∪A)` and `C∖(N∪B)` are nonempty. This is possible because `C∖(A∪B)` is a
  neighbourhood of `P` and is infinite. `C∖N` is a finite union of cones, so `V_(C∖N) ≅ V`
  (prefix replacements supported in `C∖N`) lies in `H`. By (H1) for `V` it carries `A` to
  `B`.
- **(T1).** Let `E` be a nonempty proper clopen invariant set. Pick `x ∈ E∖P` and
  `y ∈ (C∖E)∖P`, and take the swap with `[u] ⊆ E`, `[u'] ⊆ C∖E`. It moves `E`, a
  contradiction. So an invariant clopen set is `∅` or `C`, and `M^H = F_2·1`.
- **(T2).** For nonempty `A, B` avoiding `P`, transitivity gives `χ_A ≡ χ_B` modulo
  `Σ := span{hf - f}`. For a cone `[w]` avoiding `P` this gives
  `χ_[w] = χ_[w0] + χ_[w1] ≡ 2χ_[w] = 0`. Such cones span `ker(ev_P)`, so `ker(ev_P) ⊆ Σ`.
  Conversely every `hf - f` vanishes on `P`, since `h` fixes `P`. So `Σ = ker(ev_P)`.
- **(T3).** Let `T` commute with `H`.
  1. **Sets avoiding `P`.** Let `A` be nonempty clopen avoiding `P`, and let `G_A` be its
     stabiliser in `H`. The clopen set where `Tχ_A = 1` is `G_A`-invariant.
     - `G_A ⊇ V_A ≅ V`, so its intersection with `A` is `∅` or `A`, by (T1) for `V`.
     - `G_A` contains the elements of `V` supported in `C∖A` that are the identity near `P`.
       The swap argument inside `C∖A` then gives an intersection with `C∖A` of `∅` or
       `C∖A`.

     So `Tχ_A = aχ_A + bχ_(C∖A)`. By transitivity, and `T(hχ_A) = hTχ_A`, the pair `(a,b)`
     does not depend on `A`. Split a cone `[w]` avoiding `P` into `[w0], [w1]`:
     `Tχ_[w] = aχ_[w] + b(χ_(C∖[w0]) + χ_(C∖[w1])) = aχ_[w] + bχ_[w]`, which must equal
     `aχ_[w] + bχ_(C∖[w])`. So `b = 0`, and `T = a·id` on `ker(ev_P)`.
  2. **Correction term.** Choose pairwise disjoint cones `[u_p] ∋ p` and put `e_p = χ_[u_p]`
     and `c_p := Te_p - a e_p`. Since `f - Σ_p f(p) e_p ∈ ker(ev_P)`,

         T f = a f + Σ_p f(p) c_p      for all f.

  3. **Invariance.** For `h ∈ H`, `(hf)(p) = f(p)`. Hence
     `T(hf) = a hf + Σ f(p) c_p`, while `hTf = a hf + Σ f(p) h c_p`. Taking `f = e_q` gives
     `h c_q = c_q`, so `c_q ∈ M^H = F_2·1`. So `T = a·id + Σ_p λ_p E_p`.

## Lemma B: the algebra `B`

- **`J_0` is `Φ(R)`-stable on both sides.** `Φ(a)(δ_y ⊗ g) = δ_y ⊗ Φ(a)g`. For the spanning
  monomials `a = s_μ t_ν` of `R`, `(s_μ t_ν f)(y) = f(ν y')` if `y = μ y'`, and `0` otherwise.
  So `(δ_y ⊗ g)Φ(s_μ t_ν)` is `δ_(νy') ⊗ g` or `0`.
- **`J_0` is closed under products.** `(δ_z ⊗ h)(δ_y ⊗ g) = δ_y ⊗ g(z)h`.
- Hence `B = Φ(R) + J_0` is a unital subalgebra and `J_0` is a two-sided ideal of `B`.
- **The sum is direct.** `Φ(R) ∩ J_0` is a two-sided ideal of `Φ(R) ≅ R`, since `Φ` is
  injective (`leavitt-algebras-l-k-1-n-are-simple`, as in item 2 of the diagonal-cone proof).
  It does not contain `id`, which has infinite rank while elements of `J_0` have finite rank.
  Simplicity of `R` forces `Φ(R) ∩ J_0 = 0`. So `π(Φ(a) + j) = a` is a well-defined unital
  ring homomorphism `B -> R` with kernel `J_0`.
- **`B` is stable under conjugation by `V`.** Elements of `V` are units of `Φ(R)`, and
  `Φ(R)` and `J_0` are each stable.

## Lemma C: the commutant of a tame diagonal cone subgroup (item 1)

Take the unconjugated `D`, with `H` tame for `P` and `K` tame for `Q`. Use the block
decomposition and the four equivariance identities from Lemma 2 of the diagonal-cone proof.
Their derivation uses only the relations, not clopen-rigidity.

1. `h T_(ij) = T_(ij) h` for all `h ∈ H`. So `T_(ij) ∈ F_2·id + span{E_p : p ∈ P}` by (T3).
2. `h T_(iβ) = T_(iβ) k` for all `h ∈ H`, `k ∈ K`.
   - With `k = 1`, the image lies in `M^H = F_2·1` by (T1).
   - With `h = 1`, `T_(iβ)` kills `span{kf - f} ⊇ ker(ev_Q)` by (T2).
   - A map killing `ker(ev_Q)` with image in `F_2·1` is `f ↦ ψ(f)·1` with `ψ` vanishing on
     `ker(ev_Q)`, i.e. `ψ ∈ span{δ_q : q ∈ Q}`. So `T_(iβ) ∈ span{E_q}`.
3. `k T_(βj) = T_(βj) h`. Symmetrically `T_(βj) ∈ span{E_p : p ∈ P}`.
4. `k T_(ββ) = T_(ββ) k`. So `T_(ββ) ∈ F_2·id + span{E_q}`.

Substituting into
`T = Σ s_(α_i) T_(ij) t_(α_j) + Σ s_(α_i) T_(iβ) T_β + Σ S_β T_(βj) t_(α_j) + S_β T_(ββ) T_β`:
- the scalar parts give `Σ λ_(ij) s_(α_i) t_(α_j) + μ S_β T_β ∈ Φ(R)`, and
  `S_β T_β = Σ_l s_(β_l) t_(β_l)`;
- every other term is `Φ(a) E_y Φ(b)` with `a, b ∈ R`, which lies in `J_0` by Lemma B.

So `T ∈ B`. If `C_j ⊇ θ D θ^(-1)` with `θ ∈ V`, then `θ^(-1) x_j θ ∈ B`, hence `x_j ∈ B`
by Lemma B. `∎`

## Item 2

This is Lemma B.

## Item 3

- **`W` lies in `B`.** Each `x_j^(±1)` commutes with `C_j`, so `x_j^(±1) ∈ B` by Lemma C.
  Elements of `V` lie in `Φ(U)`. So every element of `W` is a product of elements of `B`
  whose inverses are also in `B`.
- **The homomorphism.** `π` is multiplicative, so `π|_W : W -> R^× = U` is a homomorphism.
  Its image is generated by `V` and the `π(x_j)`, so it is finitely generated.
- **The kernel is `W ∩ (1 + J_0)`.** Let `g_1, ..., g_n` be kernel elements,
  `g_k = 1 + Σ_(y ∈ Y_k) δ_y ⊗ g_(k,y)`. Let `Y = ∪ Y_k`, which is finite, and let `G` be the
  finite-dimensional span of all `g_(k,y)`. The set

      S = { 1 + Σ_(y ∈ Y) δ_y ⊗ c_y : c_y ∈ G }

  is finite (at most `|G|^|Y|` elements) and closed under products, because
  `(1+j)(1+j') = 1 + j + j' + jj'` and `jj' = Σ_y δ_y ⊗ j(c'_y)` with `j(c'_y) ∈ G`. Each
  `g_k` has finite order, since its powers lie in `S`. So `g_k^(-1)` is a positive power of
  `g_k`, and `<g_1, ..., g_n> ⊆ S` is finite. The kernel is locally finite.
- **Subgroups.** If `L <= W` has no nontrivial locally finite normal subgroup, then
  `L ∩ ker π` is trivial and `π|_L` embeds `L` in `U`. A torsion-free `L` qualifies, since
  every element of `ker π` has finite order. `∎`

## Item 4

1. **`U` has a recursive time bound.** `U` is finitely generated
   (`thompson-steinberg-presentation-of-leavitt-unit-group`) and has decidable word problem
   (`binary-leavitt-unit-word-problem-decidable`). Fix a total algorithm and let `T_U(l)` be
   the maximal running time on words of length `<= l`. `T_U` is recursive.
2. **Choose the input.** By `graph-shift-groups-have-arbitrarily-hard-word-problem` (3), pick
   a decidable `A` such that no algorithm decides the word problem of
   `G_A = A(Γ_A) ⋊ Z` over `{a, b}` in time `C·T_U^+(C·l) + C·l + C`, where
   `T_U^+(m) = m + max_(k<=m) T_U(k)`.
3. **`G_A` is torsion-free.**
   - A torsion element has zero `b`-exponent, so it lies in `A(Γ_A)`.
   - It lies in the image of `A(Λ)` for a finite induced subgraph `Λ`, and that image map is
     injective by the retraction in the graph-shift proof, (1).
   - `A(Λ)` is torsion-free by induction on `|Λ|`. For a vertex `v`,
     `A(Λ) = < A(Λ∖v), a_v | a_v^(-1) x a_v = x, x ∈ A(lk v) >`, since the relators agree.
     The edge inclusion `A(lk v) -> A(Λ∖v)` is injective by the same retraction. So `A(Λ)`
     is an HNN extension of the torsion-free `A(Λ∖v)`, and it is torsion-free by
     `hnn-torsion-theorem`.
4. **Transfer.** If `G_A <= W`, item 3 embeds `G_A` in `U`. Substituting fixed words of
   length `<= L` for `a, b` and running the `U`-algorithm decides the word problem of `G_A`
   in time `C'·T_U^+(C'·l) + C'·l + C'`, as in `complexity-bounded-host-classes-are-not-universal`.
   This contradicts step 2. `∎`

## Item 5

If `c ∈ C` fixes `Fix(C)` pointwise, then `(c·m)|_(Fix(C)) = m|_(Fix(C))`. So the restriction
of the span of the translates to `Fix(C)` lies in `span{m_i|_(Fix(C))}`, of dimension `<= n`.
Restriction `M -> C(Fix(C), F_2)` is onto, because clopen sets of the closed set `Fix(C)` are
traces of clopen sets of `C`. So `C(Fix(C), F_2)` has dimension `<= n`, which forces
`|Fix(C)| <= n`. `∎`

## Twisted diagonals

Let `σ` be the bit flip, which normalises `V` because it conjugates the prefix replacement
`u_i y ↦ u'_i y` to `ū_i y ↦ ū'_i y`. Let `Ψ_σ f = f ∘ σ`. The subgroup
`{ s_0 h t_0 + s_1 σhσ t_1 }` covers `M`:
- translates of `s_0 χ_[0]` give every `s_0 χ_A` with `A` proper, nonempty and clopen, and
  these span `s_0 M`;
- likewise for `s_1 χ_[0]`, because `σVσ = V`.

The involution `x = s_1 Ψ_σ t_0 + s_0 Ψ_σ t_1` commutes with it, by direct multiplication.

**`x ∉ B`.** Otherwise `Ψ_σ = t_1 x s_0 ∈ B` by Lemma B.

1. **Reduce to `Φ(R)`.**
   - `Ψ_σ² = id`, so `π(Ψ_σ) =: a` satisfies `a² = 1`.
   - For `v ∈ V`, `Ψ_σ Φ(v) Ψ_σ = Φ(σvσ)`. Applying `π` gives `a v a = σvσ` in `R`.
   - Put `c = Φ(a) Ψ_σ`. Then `π(c) = 1`, and `c Φ(v) c^(-1) = Φ(a (σvσ) a) = Φ(v)`.
   - So `c` commutes with `V`, and `c = id` by Lemma 1(c) for `V`. Hence `Ψ_σ = Φ(a)`.
2. **Window counting.** Write `a = Σ_((μ,ν) ∈ F) s_μ t_ν` over a finite multiset `F`, and let
   `d >= max |ν|`. Fix `w` with `|w| = d`.
   - For every word `u`, `Φ(a) χ_[wu] = Σ_(i ∈ I) χ_[ρ_i u]`, where `I` is the set of pairs
     with `ν` a prefix of `w`, `w = ν w'` and `ρ_i = μ w'`.
   - Choose `n > max(d, max_i |ρ_i|)` and `u = 1^n`. Evaluate at `z = w̄ 0^∞`.
   - `Ψ_σ χ_[w1^n](z) = χ_[w1^n](w 1^∞) = 1`.
   - For each `i`, the letters of `z` in positions `|ρ_i|+1, ..., |ρ_i|+n` include position
     `|ρ_i| + n > d = |w̄|`, which carries `0`. So `z ∉ [ρ_i 1^n]`, and the sum is `0`.

   This is a contradiction. `∎`

## Scope

- No finite presentation or covering hypothesis on `W` is used in items 1–4.
- Item 4 does not follow from `complexity-bounded-host-classes-are-not-universal` alone. The
  hosts `W` share no recursive word-problem bound: for `P = {p, q}` with `p` computable, the
  word problem of `<V, id + E_p + E_q>` needs prefixes of `p`. That generator is an involution
  commuting with `V^(P)`. What is bounded is the quotient
  `π(W) <= U`, and torsion-freeness of the graph-shift inputs carries the bound across the
  locally finite kernel.
