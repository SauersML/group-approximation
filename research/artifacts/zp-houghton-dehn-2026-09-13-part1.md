# Houghton groups: the Dehn function is polynomially equivalent to one commutation area

Lane z1-24-houghton, 2026-09-13. Zaremsky Problem 1.24. Status: complete proof,
unreviewed.

## 0. Conventions

`Y = Y_n = {1,...,n} x N`, `N = {1,2,...}`, `n >= 3`. Following S. R. Lee
(arXiv:1212.0257, §2), permutations act on the right, products are read left to
right (`xy` = first `x`, then `y`), and `x^h = h^(-1) x h`. So the support of `x^h`
is `supp(x)·h`.

The depth of `(j,p)` is `p`. For distinct rays `a,b` let `λ_(a,b)` be the shift
that pulls ray `a` inward and pushes ray `b` outward:
`(a,p) -> (a,p-1)` for `p >= 2`, `(a,1) -> (b,1)`, `(b,p) -> (b,p+1)`, and the
identity elsewhere. Lee's generators are `g_i = λ_(1,i+1)` (`1 <= i <= n-1`) and
`α = ((1,1),(1,2))`, with the finite presentation of Lee's Theorem C
(`houghton-groups-have-at-most-exponential-dehn-function`). Every `λ_(a,b)` is a
fixed word: `λ_(1,b) = g_(b-1)`, `λ_(b,1) = g_(b-1)^(-1)`, and for `a,b != 1`,
`λ_(a,b) = λ_(a,1) λ_(1,b)`. This identity holds exactly as permutations: the
token `(a,1)` goes to `(1,1)` and then to `(b,1)`, ray `a` moves in, ray `1` is
pushed out and back, and ray `b` moves out.

`δ` is the Dehn function of Lee's presentation. `Area(w)` is the minimal number of
relator applications needed to reduce a null-homotopic word `w`.

**Definition (commutation area).** For `ℓ >= 1` let

```text
A(ℓ) = max { Area([z, α]) : z a word of length <= ℓ with zαz^(-1) = α in H_n }.
```

## 1. Statement

**Theorem.** For every `n >= 3` there is a constant `C` such that for all `L >= 1`

```text
A(L) <= δ(2L + 2)          and          δ(L) <= C L^3 (A(C L) + 1).
```

**Corollary.** `δ_(H_n)` is polynomially bounded if and only if `A` is. If
`A(ℓ) ≼ ℓ^k`, then `δ_(H_n)(x) ≼ x^(k+3)`.

The first inequality is immediate, since `[z,α]` has length `2ℓ + 2`. The rest of
this note proves the second.

## 2. Depth moves at most one step per letter

**Lemma 1.** For every generator `s ∈ {g_i^(±1), α^(±1)}` and every point `y`,
`|depth(y·s) - depth(y)| <= 1`.

*Proof.* `λ_(a,b)` changes depths on rays `a,b` by one and sends `(a,1)` to
`(b,1)`, keeping depth `1`. `α` swaps two points of depths `1` and `2`. ∎

So if `d` is a word of length `ℓ`, then `α^d` is a transposition whose two points
have depth `<= ℓ + 2`.

## 3. Canonical conjugators

**Lemma 2.** There is a constant `C_2` and, for every transposition `τ` of two
points of depth `<= R`, a word `c_τ` of length `<= C_2 (R + 1)` with `α^(c_τ) = τ`.

*Proof.* Let `τ = (x y)`.

*Case `x = (a,s)`, `y = (b,t)` with `a != b`.* A bounded word `b_(a,b)` (finitely
many cases) sends the support `{(1,1),(1,2)}` of `α` to `{(a,1),(b,1)}`. Choose a
ray `e ∉ {a,b}`, which exists since `n >= 3`, and put
`c_τ = b_(a,b) λ_(e,a)^(s-1) λ_(e,b)^(t-1)`. The factor `λ_(e,a)^(s-1)` moves
`(a,1)` to `(a,s)` and fixes ray `b`. Then `λ_(e,b)^(t-1)` moves `(b,1)` to
`(b,t)` and fixes ray `a`. So `supp(α)·c_τ = {x,y}`.

*Case `x = (a,s)`, `y = (a,t)` with `s < t`.* Choose distinct rays `e,f`, both
different from `a`. A bounded word sends `supp(α)` to `{(a,1),(e,1)}`. Then:

1. `λ_(f,a)^(t-s-1)` moves `(a,1)` to `(a,t-s)`;
2. `λ_(e,a)` pours `(e,1)` into `(a,1)` and pushes the other token to
   `(a,t-s+1)`;
3. `λ_(f,a)^(s-1)` pushes both, to `(a,s)` and `(a,t)`.

The total length is `O(t)`. ∎

Write `Can(τ) = c_τ^(-1) α c_τ`.

## 4. Sorting the translation letters

**Lemma 3.** Let `w` be a null-homotopic word of length `L`. With at most
`C_1 L^2` relator applications, `w` becomes a word that is freely equal to

```text
W = ∏_(k=1)^(M) d_k^(-1) α^(±1) d_k,        M <= C_1 L^2 + L,   |d_k| <= L + C_1.
```

*Proof.* For `i != j` and signs `ε, η`, the commutator `[g_i^ε, g_j^η]` is a
finitary permutation supported near the origin. For `(ε,η) = (1,1)` it is `α`
(Lee's relator). For the other sign patterns, both factors are shifts through ray
`1`, and they agree with mutually inverse translations outside a bounded set. So
there are fixed words `v_(i,ε,j,η) = ∏_(r=1)^(C_1) e_r^(-1) α^(±1) e_r`, with
`|e_r| <= C_1`, and relations `g_i^ε g_j^η = g_j^η g_i^ε v_(i,ε,j,η)` of area
`<= C_1`. They exist because every finitary permutation is a product of
transpositions, and each transposition is a conjugate of `α` (Lemma 2).

Bubble-sort the translation letters of `w` by their index `i`, which takes at
most `L^2/2` swaps. After each swap, move the created `v` to the right end of the
word by the free identity `u v y ≡ u y (y^(-1) v y)`. Every `α^(±1)` letter of `w`
is moved in the same way. The conjugators are suffixes of the evolving word, so
`|d_k| <= L + C_1`.

After sorting, the translation part is `g_1^(e_1) ⋯ g_(n-1)^(e_(n-1))` after free
reduction within each block. The exponent sums `e_i` are unchanged by swaps. The
translation vectors `φ(g_i) = -e_1 + e_(i+1)` are linearly independent and
`φ(w) = 0`, so every `e_i = 0` and the translation part is freely trivial. ∎

## 5. The symmetric-group word problem, one point at a time

Let `W` be as in Lemma 3. By Lemma 1 each factor is a transposition `τ_k` of points
of depth `<= R := L + C_1 + 2`. Let `B` be the set of points of depth `<= R`, so
`|B| = nR`, and `∏ τ_k = 1` in `Sym(B)`.

**Step 1 (normalize).** Replace each `α^(-1)` by `α` (relator `α^2`, area `<= M`).
Replace each `d_k^(-1) α d_k` by `Can(τ_k)`. That relation is freely conjugate to
`[d_k c_(τ_k)^(-1), α]`, and `d_k c_(τ_k)^(-1)` centralizes `α` and has length
`<= L + C_1 + C_2 (R+1)`. So its area is `<= A(C_3 L)`.

**Step 2 (eliminate a point `x ∈ B`).** Scan the word left to right. The first
letter containing `x` becomes the *carried* letter `τ = (x a)`. Move it right past
each following letter `σ`:

- If `x ∉ supp(σ)`, use `Can(τ) Can(σ) = Can(σ) Can(σ τ σ)`. The letter `σ` is
  unchanged, and the carried letter still contains `x`.
- If `σ = (x a)`, the two letters cancel (relator `α^2`). The next remaining
  `x`-letter, if any, becomes carried.
- If `σ = (x b)` with `b != a`, use `Can((x a)) Can((x b)) = Can((a b)) Can((x a))`.
  The left letter no longer contains `x`, and the carried letter stays `(x a)`.

The word length never increases, and each move is one application of a relation
of the form

```text
(ρσρ)   Can(ρ) Can(σ) Can(ρ) = Can(ρσρ)      (ρ, σ transpositions in B).
```

For the merge case take `ρ = (x a)`, `σ = (x b)`, `ρσρ = (a b)`.

A carried letter cannot survive to the end of a pass. If it did, the word would be
(letters without `x`)·`(x a)` = 1, which forces `(x a)` to fix `x`. The same
argument applies to every suffix after a cancellation, since the prefix without
`x` fixes `x`. So after the pass no letter contains `x`. One pass costs at most `M`
relations. After `|B|` passes the word is empty.

**Area of `(ρσρ)`.** Using `α^2` once,
`Can(ρ) Can(σ) Can(ρ) ≡ Can(ρ)^(-1) Can(σ) Can(ρ) = α^(c_σ Can(ρ))` freely. So the
relation `(ρσρ)` is freely conjugate to `[c_σ Can(ρ) c_(ρσρ)^(-1), α]`. This word
`z` has length `<= 4 C_2 (R+1) + 1` and centralizes `α`, because
`supp(σ)·ρ = supp(ρσρ)`. Its area is `<= A(C_3 L) + 1`, after enlarging `C_3`.

## 6. Total

```text
δ(L) <= C_1 L^2 + M + M·A(C_3 L) + nR·M·(A(C_3 L) + 1) <= C L^3 (A(C L) + 1),
```

since `M <= C_1 L^2 + L` and `R <= L + C_1 + 2`. This proves the Theorem. ∎

## 7. Remarks

- The reduction uses only three things: the translation quotient is abelian with
  independent generator images, finitary permutations of a word of length `L` live
  in the ball of depth `O(L)`, and there are conjugators of linear length.
  Amenability plays no role.
- Where the difficulty sits. `A(ℓ)` is the cost of proving that a word which fixes
  the two tokens of `α` commutes with `α`. The obvious transport derivations are
  circular. Let `μ` be a shift fixing `(1,1),(1,2)` and pushing ray `1` from depth
  `3`. Then `[μ, α]` has constant area, but `μ = λ_(e,1) ν` with `ν` a 3-cycle on
  the top three points of ray `1`. Converting `λ`-routed deep transpositions into
  `μ`-routed ones therefore needs far commutations `[ν^(λ^i), ·]`, at the same
  scale as the relation being proved. The attempts are recorded on the open
  claim `houghton-transposition-commutation-area-is-polynomial`.
- Lee's relator `α^(ḡ_i) = α^(ḡ_j)` is exactly the one-step route conversion
  (the transposition `((1,2),(1,3))` reached by pushing ray `1` from ray `i+1`
  versus from ray `j+1`). Longer route conversions and far commutations along one
  ray must be derived.
