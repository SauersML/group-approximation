# gq-referee-b: `leavitt-tuples-make-the-scalar-clauses-agree` (citation and hypothesis lens)

Node and route as landed at 5ff76dde9 (lane gq-infinite-primes). Voronetsky, arXiv:2004.08551v2, was read at source
for dcf202f7c.

**Verdict: PASS, with two wording corrections (C1, C2).** Both of the lane's questions are answered yes, with one
qualification:
- **Merging `d` idempotents.** Proposition 1 merges exactly two adjacent idempotents. Merging `d` idempotents is its
  `(d−1)`-fold iterate, which is legitimate for `N >= 3`. The route should say so (C1).
- **The scalar argument** is correct. One word is wrong: `λ ↦ λ^N` is not injective on `Q^x` for even `N`. The
  conclusion survives (C2).

## 1. Does Proposition 1 cover merging `d >= 2` idempotents at once?

**Not literally.** Voronetsky's `F_α` (§2, p. 5) is defined for one root `α = e_n − e_(n−1)`. It merges the two
idempotents `e_(n−1), e_n` into `e_∞ = e_(n−1) + e_n`. Proposition 1 (p. 10) states: "If `n ≥ 4` and `α ∈ Φ` is a
root, then `F_α` is an isomorphism". There is no multi-merge statement.

**The iterate works.** Start from the standard family of `M_(N+d−1)(R)` and merge the last two idempotents `d − 1`
times.
- **Families at each step.** Each intermediate family is again a complete family of orthogonal, pairwise Morita
  equivalent idempotents. This is Voronetsky p. 3: "If `e` and `ẽ` are orthogonal and Morita equivalent, then they are
  Morita equivalent to `e + ẽ`." So Proposition 1 applies at each step, with no Leavitt structure needed there.
- **Sizes.** The fine families have sizes `N + d − 1, N + d − 2, …, N + 1`. The last step needs `N + 1 >= 4`, that is
  `N >= 3`, which is the node's range. ✓
- **The composite on generators.** It is `x_(i∞)(a) ↦ Π_(k in block) x_(ik)(a e_k)` and
  `x_(∞j)(a) ↦ Π_k x_(kj)(e_k a)`. The factors commute, by (St2). So the composite is the `d`-tuple refinement.
- **Identification of the coarse family.** `α(E_NN) = T E_NN U = Σ_(i=1..d) E_(N−1+i, N−1+i)`: indeed
  `(…, y_1..y_d) ↦ (0, …, σ_1*(Σσ_k y_k), …, σ_d*(Σσ_k y_k)) = (0, …, y_1, …, y_d)`. So `α` carries the standard
  family of `M_N(R)` onto the coarse family, and `St_N(R) ≅ St(M_(N+d−1)(R), coarse)`. ✓

**C1 (wording).** "Voronetsky's Proposition 1 applies to `M_(N+d-1)(R)`, with ... the coarse family that merges the
last `d` idempotents" should read: "Proposition 1, applied `d − 1` times (merging two adjacent idempotents each time;
the intermediate families stay Morita equivalent by Voronetsky p. 3, and the smallest fine family has `N + 1 >= 4`
members)".

**A weaker input suffices for item 1.** Only `α(E_N) = E_(N+d−1)` is used. For that, surjectivity of each `F_α`
already suffices, and Voronetsky gives it for `n ≥ 3`, p. 9: "a surjection for `n ≥ 3`". The bijectivity is not
needed.

## 2. `λ ⊕ I ∈ E(R) ⇒ λ ⊕ I_(M−1) ∈ E_M` for all large `M`, and `λ I_M ∈ E_M`

- **Stabilization.** `E(R) = ∪_M E_M(R)`, with `E_M ⊆ E_(M+1)` under `A ↦ A ⊕ 1`. By the Whitehead lemma, `E(R) =
  [GL(R), GL(R)] = ker(GL(R) -> K_1(R))`.
  - So `[λ] = 0` gives `λ ⊕ I_(M_0−1) ∈ E_(M_0)` for some `M_0`, and then for every `M ≥ M_0`, by stabilization. ✓
- **The product of conjugates.**
  - Let `P_k` be a signed permutation matrix moving coordinate `1` to `k`. It lies in `E_M`, as products of
    `w_ij(1) = e_ij(1) e_ji(−1) e_ij(1)`.
  - `P_k (λ ⊕ I) P_k^(−1)` is the diagonal matrix with `λ` in position `k`. The signs cancel, because `λ` and `±1` are
    central.
  - These `M` diagonal matrices commute, and their product is `λ I_M`. All factors lie in `E_M`, so `λ I_M ∈ E_M`. ✓
- **The descent to rank `N`.** Take `M ≡ N (mod d − 1)` large, and apply item 1 `(M − N)/(d − 1)` times. This gives
  `λ ∈ Λ_N`. ✓

**C2 (wording).** "`Λ_N -> ker ι`, `λ -> λ^N`, is injective" is false for even `N`, since `(−1)^N = 1`. Its kernel is
contained in `{±1}`. The conclusion still holds:
- If `ker ι` is finitely generated, then the image `Λ_N^N ⊆ ker ι` is finitely generated.
- `Λ_N` is then an extension of it by a group of order at most 2, hence finitely generated.
- The converse holds because `ker ι ⊆ Λ_N` is a subgroup of the finitely generated abelian group `Λ_N`.

So replace "is injective" with "has kernel in `{±1}`".

## 3. Other checks

- **Item 1, `α(λ I_N) = λ I_(N+d−1)`.** `λ` comes from the unital map `Q -> R`, which is injective since `R ≠ 0`, and
  its image is central. ✓
- **Item 3, `R_L`.** `ker ι = Q^x` is the refereed `K_1(R_L) ≅ Z` computation, in which every rational scalar is `0`
  (`leavitt-resolvent-k-theory-is-shifted-rational-k-theory`, report 298991936). So `Λ_N(R_L) = Q^x` for every
  `N >= 3`. ✓
- **Item 4.** `[1] = Σ_i [σ_i σ_i*] = d[1]`, since `σ_i* σ_i = 1` makes each `σ_i σ_i*` equivalent to `1`. So
  `(d−1)[1] = 0`, and rings in which `[1]` has infinite order contain no Leavitt tuple. ✓
