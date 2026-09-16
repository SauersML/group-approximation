# Lane swarm-fp-simple-groups-with-arbitrar, 2026-09-16: characteristic-p affine self-similar hosts are linear

**Root:** `fp-simple-groups-with-arbitrarily-complex-word-problem`.
**Hole locked and worked:** `fp-self-similar-groups-with-arbitrarily-hard-word-problem`.

## Outcome

- **Not solved.** The hole stays OPEN.
- **Obstruction landed.** Cairn computes both claims ESTABLISHED. They are not
  independently reviewed, and no priority is claimed.
  1. `char-p-untwisted-self-similar-affine-groups-are-linear`, by the direct proof
     `char-p-untwisted-self-similar-affine-groups-linear-proof`. Affine groups
     `A x| Γ` over an elementary abelian `p`-group, with a finite-corank separating
     endomorphism that virtually commutes with `Γ`, embed in `GL_N(F_p[[t]])`. This
     includes every characteristic-`p` instance of Zaremsky's Example 4.7, over
     *non-commutative* rings too.
  2. `char-p-untwisted-affine-hosts-have-polynomial-word-problem`, by
     `char-p-untwisted-affine-hosts-polynomial-wp-proof`. Their finitely generated
     subgroups have polynomial word problem, share the bound `2^n`, and exclude the
     KMS group.
- **Reduction landed.** Route `hard-type-a-actors-from-hard-fp-self-similar-groups`
  shows that the hole implies `type-a-actors-with-arbitrarily-hard-word-problem`.
  That node's `distinct_from` says neither claim is known to imply the other; this
  route proves one direction. The committed node is not edited.
- **Correction.** Attempt 2 of the hole says Zaremsky's affine hosts "land inside
  linear groups over fields". Before today the graph had a word-problem bound only for
  affine groups over finitely generated commutative algebras over finite fields.
  §5 proves linearity in characteristic `p` for all rings satisfying Example 4.7. Characteristic `0` and exponent
  `p^m` with `m >= 2` remain unproved (§9).

## 1. Setting and notation

- **Setting (L).** `p` is a prime, and `A` is an elementary abelian `p`-group, that is,
  an `F_p`-vector space of any dimension. Every additive map of `A` is `F_p`-linear.
- `ν: A -> A` is additive and injective, `A/νA` is finite of `F_p`-dimension `r`, and
  `∩_(k>=0) ν^k A = 0`.
- `End_ν(A)` is the ring of additive maps `e: A -> A` with `eν = νe`.
- **Semidirect products.** For `Γ <= Aut(A)`, `A x| Γ` has product
  `(a, γ)(a', γ') = (a + γ(a'), γγ')`. This is Zaremsky's `A x| Γ`, which acts on
  `A` by `(a, γ).a' = a + γ(a')`.
- **Power series.** `Λ = F_p[[t]]`, and `Λ_k = F_p[t]/(t^k)`, which is also `Λ/t^kΛ`.
- `ε_1, ..., ε_r` is the standard basis of `Λ^r`.

## 2. The module lemma

**Lemma 2.1 (dimensions).** `dim_(F_p) A/ν^k A = kr` for every `k >= 0`.

*Proof.* In the filtration `A ⊇ νA ⊇ ... ⊇ ν^k A`, the map `ν^j` induces a map
`A/νA -> ν^j A/ν^(j+1) A`.
- It is surjective by definition.
- It is injective: if `ν^j a = ν^(j+1) b`, then `a = νb`, because `ν^j` is injective.

So each of the `k` layers has dimension `r`. `∎`

Fix `e_1, ..., e_r in A` whose classes form a basis of `A/νA`. For
`f = (f_1, ..., f_r) in F_p[t]^r` write `f(ν)e = Σ_i f_i(ν) e_i`.

**Lemma 2.2 (digits).** For every `k`, the map
`π_k: Λ_k^r -> A/ν^k A`, `f -> f(ν)e mod ν^k A`, is an `F_p`-linear isomorphism.

*Proof.*
- **Well defined.** `t^k` goes to `ν^k`, and `ν^k e_i` lies in `ν^k A`.
- **Surjective,** by induction on `k`. The case `k = 0` is trivial. Given `a in A`, pick
  `c in F_p^r` with `a - Σ c_i e_i = νa'`. By induction
  `a' ≡ g(ν)e mod ν^(k-1) A`, so `νa' ≡ (tg)(ν)e mod ν^k A`. Hence
  `a ≡ (c + tg)(ν)e mod ν^k A`.
- **Bijective.** Both sides have dimension `kr`, by Lemma 2.1. `∎`

**Definition 2.3 (ι).** The truncation `Λ_(k+1)^r -> Λ_k^r` carries `π_(k+1)^(-1)` of
`a mod ν^(k+1) A` to `π_k^(-1)` of `a mod ν^k A`, because `π_(k+1)` reduces to `π_k`.
Let `ι(a) in Λ^r` be the compatible limit of `π_k^(-1)(a mod ν^k A)`.

**Lemma 2.4.** The map `ι: A -> Λ^r` has the following properties.
1. It is additive and injective.
2. `ι(νa) = t ι(a)`, and `ι(f(ν)e) = f` for `f in F_p[t]^r`; in particular
   `ι(e_j) = ε_j`.
3. `a in ν^k A` iff `ι(a) in t^k Λ^r`.

*Proof.*
- **1.** Additivity holds because each `π_k^(-1)` is linear. If `ι(a) = 0`, then
  `a in ν^k A` for every `k`, so `a = 0`.
- **2.** If `a ≡ f(ν)e mod ν^k A`, then `νa ≡ (tf)(ν)e mod ν^(k+1) A`. So
  `ι(νa) ≡ t ι(a) mod t^(k+1)` for every `k`. The second formula is the definition,
  since `f(ν)e ≡ f(ν)e` at every level.
- **3.** `ι(a) ≡ 0 mod t^k` iff `π_k^(-1)(a mod ν^k A) = 0` iff `a in ν^k A`. `∎`

**Definition 2.5 (M).** For `e in End_ν(A)` let `M(e) in M_r(Λ)` have `j`-th column
`ι(e e_j)`.

**Lemma 2.6.** For all `e in End_ν(A)` and `a in A`, `ι(ea) = M(e) ι(a)`. The map
`M: End_ν(A) -> M_r(Λ)` is an injective unital ring homomorphism, and `M(ν) = tI`.

*Proof.*
- **The formula.** Fix `k`. By Lemma 2.2, `a = f(ν)e + ν^k b` with `f in F_p[t]^r` and
  `b in A`. Since `e` commutes with `ν`, `e f_j(ν) = f_j(ν) e`, and so
  `ea = Σ_j f_j(ν)(e e_j) + ν^k(eb)`. By Lemma 2.4,
  `ι(ea) = Σ_j f_j(t) ι(e e_j) + t^k ι(eb) = M(e) f + t^k ι(eb)`. Also
  `ι(a) = f + t^k ι(b)`, so `M(e)ι(a) = M(e) f + t^k M(e) ι(b)`. Hence
  `ι(ea) ≡ M(e)ι(a) mod t^k` for every `k`.
- **Ring homomorphism.** Additivity is clear. `ι(ee'a) = M(e)M(e')ι(a)`; at `a = e_j`
  this says that the columns of `M(ee')` and `M(e)M(e')` agree. `M(id) = I`.
- **`M(ν) = tI`.** `ι(ν e_j) = t ε_j`.
- **Injective.** If `M(e) = 0`, then `ι(ea) = 0` for all `a`, so `e = 0` by injectivity
  of `ι`. `∎`

If `γ in Aut(A)` commutes with `ν`, so does `γ^(-1)`, and `M(γ)M(γ^(-1)) = I`. So `M`
maps `Aut(A) ∩ End_ν(A)` into `GL_r(Λ)`.

## 3. Affine embedding and finite index

**Proposition 3.1.** Let `Γ_0 <= Aut(A)` commute with `ν`. Then
`Φ(a, γ) = [[M(γ), ι(a)], [0, 1]]` is an injective homomorphism
`A x| Γ_0 -> GL_(r+1)(Λ)`.

*Proof.*
- **Homomorphism.** `Φ(a,γ)Φ(a',γ')` has top-left block `M(γ)M(γ') = M(γγ')` and
  top-right column `M(γ)ι(a') + ι(a) = ι(γ(a') + a)`. That is `Φ((a,γ)(a',γ'))`.
- **Injective.** `Φ(a,γ) = I` forces `ι(a) = 0`, so `a = 0`, and `M(γ) = I = M(id)`, so
  `γ = id`. `∎`

**Proposition 3.2.** Let `Γ <= Aut(A)` contain a subgroup `Γ_0` of finite index `d` that
commutes with `ν`. Then `A x| Γ` embeds in `GL_((r+1)d)(Λ)`.

*Proof.*
- **Setup.** Put `G = A x| Γ`, `G_0 = A x| Γ_0` and `ρ = Φ`, so `[G : G_0] = d`. Fix left
  coset representatives `g_1, ..., g_d`. For `g in G` and each `j` there are unique
  `π_g(j)` and `h_j(g) in G_0` with `g g_j = g_(π_g(j)) h_j(g)`.
- **The representation.** Let `Ψ(g)` be the `d x d` block matrix with block
  `ρ(h_j(g))` in position `(π_g(j), j)` and zero blocks elsewhere.
- **Homomorphism.**
  `g g' g_j = g g_(π_(g')(j)) h_j(g') = g_(π_g π_(g')(j)) h_(π_(g')(j))(g) h_j(g')`.
  So `π_(gg') = π_g π_(g')` and `h_j(gg') = h_(π_(g')(j))(g) h_j(g')`, which is exactly
  the block product `Ψ(g)Ψ(g')`. Also `Ψ(1) = I`, so every `Ψ(g)` is invertible.
- **Injective.** If `Ψ(g) = I`, then `π_g = id` and `ρ(g_j^(-1) g g_j) = I`. Since `ρ` is
  injective, `g = 1`. `∎`

(This is the induced representation. Its kernel is the core of `ker ρ`, which is
trivial.)

## 4. Remark: the tree action is linearized too

Suppose `Γ_0 = Γ`, and let `φ = ν^(-1): νA -> A`, a surjective proper virtual
endomorphism of Zaremsky's kind. Level `k` of his coset tree `T_φ` is `A/ν^k A`, and
`(a, γ)` acts there by `a' + ν^k A -> a + γ(a') + ν^k A`.

By Lemma 2.4(3) and Lemma 2.6, `ι` induces the isomorphisms `π_k^(-1)`. These conjugate
the action to `ξ -> ι(a) + M(γ)ξ mod t^k` on `Λ_k^r`.

So the self-similar action of `A x| Γ` is the restriction of the affine action of
`Λ^r x| GL_r(Λ)` on the tree of cosets of `t^k Λ^r`, the characteristic-`p` analogue of
the digit-affine trees of `digit-affine-hosts-with-abelian-linear-parts-have-finite-rank`.
Nothing below uses this remark.

## 5. Zaremsky's Example 4.7 in characteristic p

**Corollary 5.1.** Let `R` be a unital ring with `p·1 = 0`. Let `x in R` satisfy:
- `R/Rx` is finite, of `F_p`-dimension `s`;
- `rx = 0` implies `r = 0`;
- `∩_k R x^k = 0`.

Then:
1. `R` embeds as a ring in `M_s(F_p[[t]])`;
2. for every `n >= 1` and every `Γ <= GL_n(R)`, `R^n x| Γ` embeds in
   `GL_(ns+1)(F_p[[t]])`.

*Proof.*
- **Setup.** Take `A = R^n`, an elementary abelian `p`-group, and `ν(r_1, ..., r_n) =
  (r_1 x, ..., r_n x)`.
  - `ν` is injective by the second hypothesis.
  - `ν^k A = (Rx^k)^n`, so `A/νA = (R/Rx)^n` has dimension `ns` and
    `∩_k ν^k A = 0`.
- **Part 2.** For `γ in GL_n(R)` acting by matrix multiplication on column vectors,
  `(γ(vx))_i = Σ_j γ_ij v_j x = (γv)_i x`. So `Γ` commutes with `ν`, and Proposition 3.1
  with `Γ_0 = Γ` gives part 2.
- **Part 1.** Take `n = 1` and `λ_a(r) = ar`.
  - `λ_a` commutes with `ν` by associativity, so `λ: R -> End_ν(R)` is a unital ring
    homomorphism.
  - It is injective, because `λ_a(1) = a`.
  - Compose with `M` from Lemma 2.6. `∎`

These are exactly the hypotheses of `principal-ideal-affine-groups-are-self-similar`
when `p·1 = 0`. Zaremsky's `φ: J -> R`, `rx -> r`, is well defined because
`rx = 0 => r = 0`.

**Remark 5.2 (PI).** By the Amitsur--Levitzki theorem (standard, not re-read), `M_s(C)`
satisfies the standard identity of degree `2s` for commutative `C`. So any ring of
characteristic `p` that satisfies Example 4.7's hypotheses is a PI ring. Examples such
as `M_k(F_p[t])` with `x = tI`, or the skew polynomial ring `F_q[t; Frob]` with
`x = t`, are consistent with this. Free algebras fail the finite-index hypothesis.

## 6. Twisted hosts

Let `μ: A -> A` be additive and injective with `A/μA` finite and `∩_k μ^k A = 0`. Then
`φ = μ^(-1): μA -> A` is a surjective proper virtual endomorphism.

Conversely, every surjective proper `φ` arises this way:
- a proper `φ` is injective (Zaremsky §4);
- the domain of `φ^k` is `μ^k A`: if `a` is in the domain of `φ^k`, then
  `a = μ^k(φ^k a)`.

Let `Γ <= Aut(A)` be `φ`-stable, meaning `γ(μ^k A) = μ^k A` for all `k`, and put
`σ(γ) = μ^(-1)γμ`, which Zaremsky writes `φγφ^(-1)`. Mutual stability is `σ(Γ) <= Γ`.

**Proposition 6.1.** Suppose there are:
- an integer `m >= 1`;
- a finite-index `Γ_0 <= Γ`;
- a `δ in Aut(A)` with `δ(μ^k A) = μ^k A` for all `k`,

such that `σ^m(γ) = μ^(-m)γμ^m = δγδ^(-1)` for all `γ in Γ_0`. Then `ν = μ^m δ` satisfies
setting (L) and commutes with `Γ_0`, so Proposition 3.2 applies to `A x| Γ`.

*Proof.*
- **Commutes with `Γ_0`.** From `μ^(-m)γμ^m = δγδ^(-1)` we get `γμ^m = μ^m δγδ^(-1)`,
  so `γν = γμ^mδ = μ^mδγ = νγ`.
- **Injective.** `ν` is a composite of injective maps.
- **The filtration.** By induction `ν^k A = μ^m δ(μ^(m(k-1)) A) = μ^(mk) A`, since `δ`
  preserves each `μ^j A`. So `A/νA = A/μ^m A` is finite, and `∩_k ν^k A = 0`. `∎`

**Special cases.**
- `δ = id`: the twist `σ` has finite order dividing `m` on `Γ_0`.
- `m = 1` and `δ in Γ`: `φ`-stability gives `δ(μ^k A) = μ^k A`, and the twist is inner
  by an element of `Γ`.

**The genuinely twisted case.** Since `μ^k σ^k(γ) = γμ^k`, for `u_k in E = span(e_i)`:

```text
γ( Σ_(k<K) μ^k u_k + μ^K b ) = Σ_(k<K) μ^k σ^k(γ)(u_k) + μ^K σ^K(γ)(b).
```

So `γ` is computed digit by digit, by a transducer whose states are `σ^k(γ)`.
- In the untwisted case the transducer has one state and `γ` is `Λ`-linear.
- When no power of `σ` is virtually inner by a filtration-preserving automorphism, `γ`
  is `F_p`-linear and continuous but, in general, not `Λ`-linear for any choice of `ν`.

Such maps appear to be the affine tree automorphisms of Savchuk--Sidki
(arXiv:1510.08434; abstract only, 2026-09-16). Among Corollary 4.5 hosts over
elementary abelian `p`-groups this is the only place where hardness can enter
(self-similar groups that are not such hosts are not addressed). It matches the
hole's first necessary condition, infinitely many states.

## 7. Word problem and the KMS exclusion

**Theorem 7.1.** In setting (L), let `Γ <= Aut(A)` have a finite-index subgroup
commuting with `ν`, and let `H <= A x| Γ` be generated by a finite set `B`.
1. The word problem of `H` over `B` is decidable in time `C*l^C + C`.
2. It lies in `F(2^n)`.
3. The KMS group `G` of `kms-groups-avoid-commutative-algebra-affine-hosts` embeds in
   no such `A x| Γ`.

*Proof.*
- **Linearize.** Let `Ψ: A x| Γ -> GL_N(Λ)` be the embedding of Proposition 3.2. Let
  `S <= Λ` be the `F_p`-subalgebra generated by the entries of `Ψ(b)` and `Ψ(b)^(-1)`
  for `b in B`.
  - `S` is a finitely generated commutative `F_p`-algebra.
  - Every element of `H` is a product of `b^(±1)`, so `Ψ(H) <= GL_N(S)`.
- **Parts 1 and 2.** `GL_N(S) = Aut_S(S^N)` sits in `Aff_S(S^N)` as `w -> (0, w)`. So
  `Ψ(H)` is a finitely generated subgroup of `Aff_S(S^N)`, and `S^N` is a finitely
  generated `S`-module. Since `Ψ` is injective, a word over `B` is trivial in `H` iff its
  image is trivial in `Ψ(H)`. Parts 1 and 2 of
  `commutative-algebra-affine-groups-have-polynomial-word-problem` apply with `q = p`.
- **Part 3.** `G` is finitely presented, so if `G <= A x| Γ`, the same construction
  embeds `G` in `Aff_S(S^N)`. This contradicts that node. `∎`

**Non-uniformity.** The algorithm exists, with finite data: a presentation of `S` and a
Gröbner basis. It is not claimed to be computable from `(A, ν, Γ)`, which need not be
effective at all. The complexity transfer only needs existence.

**Meaning for the hole.**
- All finitely generated groups that embed in such hosts have word problem in
  `F(2^n)`. So none beats `T(n) = 2^n`. As a family these hosts cannot witness
  `fp-self-similar-groups-with-arbitrarily-hard-word-problem`, and by
  `complexity-bounded-host-classes-are-not-universal` they are not universal.
- In particular the finitely presented self-similar groups `R^n x| Γ` from Example 4.7
  over rings of characteristic `p`, commutative or not, are dead as a source.

## 8. Route A: hard self-similar groups give hard type (A) actors

**The argument.**
- Fix a recursive `T` and put `T+(m) = m + max_(k<=m) T(k)`. It is recursive, monotone
  and at least `T`.
- Suppose `fp-self-similar-groups-with-arbitrarily-hard-word-problem` holds. It gives a
  finitely presented self-similar `H` with word problem outside `F(T+)`.
- By (a) of `fp-self-similar-subgroups-satisfy-permutational-boone-higman`, `H` lies in
  `B_A`. So `H <= G` for some `G` with an action of type (A). By definition such an
  action is faithful and `G` is finitely presented
  (`type-a-action-gives-boone-higman-for-subgroups`).
- Write the generators of `H` as words of length at most `L` over those of `G`. A
  word-problem algorithm for `G` in `F(T)` then gives one for `H` in `F(T+)`, by the
  substitution in `complexity-bounded-host-classes-are-not-universal-proof`. That is a
  contradiction, so `G` beats `T`. `∎`

**Consequences.**
- The hole implies `type-a-actors-with-arbitrarily-hard-word-problem`. By (d) of
  `twisted-brin-thompson-wp-equals-actor-orbit-problem`, it therefore also implies the
  four equivalent twisted Brin--Thompson statements there.
- The converse is not known. A type (A) actor need not be self-similar.
- The committed `distinct_from` rationale in `type-a-actors-with-arbitrarily-hard-word-problem`
  ("neither is known to imply the other") is superseded in one direction. It is not
  edited here, per swarm rules.

## 9. What is not covered

1. **Genuinely twisted `σ`** (§6). No linearization is available. Heuristic, not
   checked: without the uniform self-similarity constraint, filtration-preserving
   `F_p`-linear tree automorphisms contain many residually-`p` groups, through Jennings
   filtrations. So linear algebra alone gives no obstruction there.
2. **Exponent `p^m` with `m >= 2`, and characteristic `0`.** Sketch only, not promoted.
   - Let `N = |A/νA|` and `Â = lim A/ν^k A`. This is a pro-`N` group on which `ν`
     acts topologically nilpotently, so it is a module over
     `Λ' = (∏_(p|N) Z_p)[[t]]` with `t` acting as `ν`. By topological Nakayama it is
     generated by lifts of generators of `A/νA`, and every `e in End_ν(A)` extends
     `Λ'`-linearly. Separation makes `A -> Â` injective.
   - For finitely generated `H`, lift the finitely many generator actions to matrices
     over `Λ'`. Take `S` to be the finitely generated `Z`-subalgebra containing the
     entries, and `M_S` the image of `S^s` in `Â`.
   - This gives `H -> Aff_S(M_S)`. It is faithful because `M_S` contains `Λ'`-module
     generators of `Â` and the maps are `Λ'`-linear.
   - What is missing is a polynomial word-problem bound for affine groups of
     finitely generated modules over finitely generated commutative rings of mixed or
     zero characteristic. It is not in the graph; the node
     `commutative-algebra-affine-groups-have-polynomial-word-problem` excludes that case.
   - So in characteristic `0` Attempt 2's "lands inside linear groups over fields"
     remains unproved for non-commutative rings.
3. **Non-abelian `A`,** as in Corollary 4.5 in general.
4. **Non-surjective `φ`.**
5. **Self-similar groups not of the form `A x| Γ`.** This includes Attempt 3 of the hole
   (virtual endomorphisms of KMS groups), which is still not executed.

## 10. Literature gate (2026-09-16)

- **M. C. B. Zaremsky**, *Embedding finitely presented self-similar groups into
  finitely presented simple groups*, arXiv:2405.09722v2 (v1 2024-05-15, v2 2025-01-21).
  §4 was read from the TeX source today: Tree of cosets, Lemmas Faithful and
  Self-similar, Corollary 4.5, Examples 4.6 and 4.7. No linearization statement is
  there.
- **F. Fournier-Facio, X. Wu, M. C. B. Zaremsky**, *Abstract twisted Brin--Thompson
  groups*, arXiv:2603.24687v2 (2026-03-25, v2 2026-04-02). Abstract only; about
  embedding finitely presented simple groups, with no complexity statement.
- **Almeida, Dantas, Oliveira-Tosti**, *On the Self-Similarity of Permutational Wreath
  Products and Their Embedding into Finitely Presented Simple Groups*,
  arXiv:2609.01868v1 (2026-09-01). Abstract only. New Boone--Higman examples, with no
  hardness statement.
- **Livramento, Noseda**, *Self-similarity of the classical p-adic Lie groups and Lie
  algebras*, arXiv:2410.22639v1 (2024-10-30). Abstract only; about virtual endomorphisms
  of Lie lattices.
- **Dantas, Santos, Sidki**, *Intransitive self-similar groups*, arXiv:2004.08941v2
  (2020-04-19, v2 2020-04-21). Abstract only.
- **Savchuk, Sidki**, *Affine automorphisms of rooted trees*, arXiv:1510.08434v1
  (2015-10-28). Abstract only: affine actions on tree boundaries viewed as
  infinite-dimensional vector spaces.
- **L. Bartholdi, I. Mitrofanov**, *The word and order problems for self-similar and
  automata groups*, arXiv:1710.10109v4 (2017-10-27, updated 2017-11-27). Abstract only.
  The word problem is undecidable for functionally recursive groups. These are not
  finitely presented, and the abstract gives no time bounds.
- **arXiv API searches, 2026-09-16:**
  - `abs:"self-similar" AND abs:"virtual endomorphism"`;
  - `abs:"self-similar" AND abs:"word problem"`;
  - `abs:"Boone-Higman"`;
  - `abs:"finitely presented simple" AND abs:"word problem"`;
  - `abs:"linear automata" AND abs:group`;
  - `abs:"self-similar" AND abs:affine AND abs:tree`.

  None states the linearization above, or a finitely presented self-similar group
  beyond a given recursive bound.
- **Standard, not re-read:** the Amitsur--Levitzki theorem, and Cox--Little--O'Shea
  (through the imported word-problem node).
