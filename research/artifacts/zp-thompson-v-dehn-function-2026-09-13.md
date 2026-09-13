# Thompson's group V: where the Dehn-function degree is lost, and what a quadratic proof must do (2026-09-13)

Lane z2-05-v-dehn (Zaremsky Problem 2.5). Nodes:
`zaremsky-2-05-dehn-functions-of-thompson-t-and-v`,
`thompson-v-has-quadratic-dehn-function`,
`thompson-v-dehn-function-is-at-most-sextic`,
`thompson-v-elements-need-unboundedly-many-non-f-letters`.

## 1. Status (sources read 2026-09-13)

| group | Dehn function | source |
|---|---|---|
| F | `≃ n^2` | Guba, Invent. Math. 163 (2006), Theorem 1 |
| T | `≃ n^2` | Migliorini, arXiv:2410.23088, Theorem A (Forum Math. Sigma 13 (2025) e109) |
| V | `n^2 ≼ δ_V ≼ n^6` | lower: V not hyperbolic; upper: Lorrain, arXiv:2608.03813v2, Theorem 5.7 (unrefereed) |

Earlier upper bounds: T `n^7` and V `n^11` (Guba 2000); T quintic (Wang–Zheng–Zhang 2015, per Lorrain §1).
Higher-rank Dehn functions of F, T, V: nothing found (bounded search).

## 2. Lorrain's cost map (arXiv:2608.03813v2, pp. 51–65)

- Presentation: finite presentation of V on `x_0, x_1, c_1, π_0` (§1.1), with
  the letters `x_n, c_n, π_n` defined by conjugation (eq. (1)); definitions cost
  0 area (§1.2.2).
- Normal form (Definition 1.11; Guba 2000 Theorem 3 = Lorrain Theorem 5.5):
  `w = p π c_(n+1)^m q^(-1)`, with MP-words `p, q` of complexity `≤ n`, `π` an
  irreducible π-word of rank `≤ n`, and `0 ≤ m ≤ n+2`.
- π-words: the letters `π_i` satisfy the Coxeter relations of `S_∞` (§4.1). The
  rewriting system (8) is terminating and confluent (Guba 2000, Lemma 14).
  Irreducible words are sequences of downstreams with increasing ranks
  (Lemma 4.5), of length at most `(n+1)(n+2)/2` (Corollary 4.6).
- Costs:
  - switching two π-letters `O(n^2)` (§4.2, via Lemma 3.18);
  - inserting one letter into an irreducible word `O(n^4)` (Lemma 4.7);
  - reducing a π-word `|w|_∞^2 · O(n^2)` (Lemma 4.8);
  - c-letter across a π-letter `O(n^3)` (Lemma 3.29);
  - Lemma 4.14 `O(n^6)`.
- Theorem 5.6 inducts on length by halving. The p. 65 region tally
  `3O(n²) + O(n³) + 2O(n⁴) + O(n⁵) + 4O(n⁶)` is the merge cost `M(n)`.
- **Recursion remark.** With `A(n) ≤ 2A(⌈n/2⌉) + M(n)` and `M(n) = O(n^α)`,
  `α > 1`, the sum `Σ_j 2^j (n/2^j)^α = O(n^α)`. So the bound is exactly the
  merge cost: a quadratic merge gives a quadratic Dehn function. The sextic
  terms all come from π-words: Lemma 4.8 at `|w|_∞ = Θ(n^2)` in region ⑩, and
  Lemma 4.14 in region ⑧.

## 3. Obstruction 1: no bounded normal form (established)

`thompson-v-elements-need-unboundedly-many-non-f-letters`: the order-break
count `br` on V is subadditive, `br(F) = 1`, `br(T) ≤ 2`, and the depth-k block
reversal `r_k` has `br(r_k) = 2^k`. So every word for `r_k` has
`≥ (2^k − 1)/b_S` letters outside F. Migliorini's T step (Proposition 4.2: one
`C_0` letter) cannot transfer. The dead route
`thompson-v-quadratic-via-bounded-non-f-normal-form` records this.

## 4. Obstruction 2 (heuristic): permutation words are quadratically inflated

- Lower bound on word length by counting, self-contained. `Sym(2^k)` embeds in V
  as the permutations of the depth-`k` cones; each such element has a tree pair
  with `≤ 2^k − 1` carets. There are at most `(2|S|+1)^ℓ` words of length `≤ ℓ`
  over a generating set `S`. So some permutation of `N = 2^k` cones has word
  length `≥ log(N!)/log(2|S|+1) ≥ (N log_2 N − 2N)/log_2(2|S|+1)`. Migliorini §6
  quotes Birget (IJAC 14 (2004)) for the matching upper bound
  `‖f‖_V ≤ C·N(f)·log N(f)`.
- Guba's normal form writes the permutation part in adjacent transpositions
  `π_i`. Its π-length is the inversion number, up to `Θ(n^2)` at rank `n`
  (Corollary 4.6 is sharp: `π_0(π_1π_0)⋯(π_n⋯π_0)`), while the element needs
  only `O(n log n)` letters.
- Not a theorem: van Kampen area is not bounded below by intermediate lengths.
  Still, any argument that passes through Coxeter normal forms and pays per
  Coxeter move meets `Θ(n^2)`-length words, and moving letters within them costs
  `Θ(n^3)`–`Θ(n^4)` Coxeter moves. For example, some pairs of reduced words of the
  longest element of `S_(n+1)` are related only through at least `C(n+1,3)` braid
  moves, because in the pseudoline picture every triple of strands must be
  flipped. Lorrain's costs show this is where the `n^6` arises.

## 5. Strategies for `δ_V ≼ n^2`

**A. Triangle criterion with compressed permutation normal forms.**
Migliorini Proposition 4.3, verbatim from the arXiv HTML: "Let G = ⟨S|ℛ⟩ be a
finitely presented group, and for each g ∈ G choose a subset W_g of words in S
that represent the element g. Suppose that there exists C > 0 such the following
hold: for every g ∈ G there is w ∈ W_g with |w| ≤ C · ‖g‖_G; for every
null-homotopic word w = w₁w₂w₃, with w_i ∈ W_{g_i} for some elements
g₁,g₂,g₃, we have that Area(w) ≤ C|w|². Then the Dehn function of G is
quadratic."

Proposed `W_g`: `u · Λ_1 ⋯ Λ_d · v` with `u, v ∈ F`, where the `Λ_j` are merge
layers. A layer is a product of F-conjugates of `π_0`, disjoint cone swaps
arranged as one level of a merge sort on the `br(g)` pieces, with
`d = O(log br(g))`. Open lemmas:

- (A1) lengths `|w| = O(‖g‖)`; Birget's bound suggests this is achievable;
- (A2) area of commuting an F-letter past a layer is linear in the layer length;
- (A3) area of re-sorting two concatenated layer stacks is quadratic in length.

(A2) is the analogue of Migliorini's use of `C_0` normalizing `F × F`. A layer
of disjoint swaps normalizes the product of the copies of F supported on its
pieces.

**B. Stein–Farley complex.**
V acts properly on a CAT(0) cube complex (Farley), with cocompact sublevel sets
`X_(≤m)`. A loop of length `n` bounds a disc of area `≤ n^2/4` in `X`, by the
dual-curve argument, but the disc can climb to height `m_0 + Θ(n)`. Pushing down
through descending links (Brown's `F_∞` proof) multiplies area by a constant per
level. The naive result is exponential; it becomes polynomial only if the height
excess is `O(log n)`. Open: choose fillings with logarithmic height excess, or
push many levels at once.

**C. Symmetric diagram groups.**
V is the symmetric diagram group of `⟨x | x = x^2⟩` (Guba–Sapir). Guba's `n^11`
came from diagram-group standard forms; his quadratic F proof improved the
triangular-diagram estimates. Adapt the F proof's horizontal and vertical
diagram lemmas to diagrams with free wire crossings, where the crossings are the
permutation part.

## 6. Next targets for this lane

1. (A2) for a single layer: the area of `f · Λ = Λ' · f'` for `f ∈ F` of length
   `ℓ` and a layer `Λ` of `p` disjoint cone swaps. Aim for `O(ℓ + p)` area plus
   F-relations with quadratic area.
2. A rigorous version of Obstruction 2: a lower bound on the area of the V
   relation `π-word = its irreducible form` over Lorrain's finite presentation.
   If area `≥ n^3` is forced for some length-`n` relation, the Coxeter route has
   an established ceiling.
3. Higher-rank part: test for coarse Lipschitz retractions of F onto its
   disjoint-support flats `Z^(k+1)`, the lower-bound step toward
   `δ^(k)_F ≽ n^((k+1)/k)`.
