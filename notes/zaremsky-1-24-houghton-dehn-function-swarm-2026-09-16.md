# Zaremsky 1.24 (Houghton Dehn function): swarm attack, 2026-09-16

Lane swarm-zaremsky-1-24-houghton-dehn-fu. Target `zaremsky-1-24-houghton-dehn-function`.
Hole locked and worked: `houghton-groups-have-polynomial-dehn-function`.
Outcome: no resolution. This note records (i) a dated literature gate, (ii) a small
rigorous lemma: four natural relation families in `H_3` have polynomially equivalent
areas, which refines the "Tower of Hanoi" framing of route conversions, and (iii)
where every attempted upper-bound scheme dies. Nothing here is promoted to the graph.

## 1. Setup

Conventions as in `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md`: right
actions, products left to right, `x^h = h^(-1) x h`, `λ_(a,b)` pulls ray `a` in and
pushes ray `b` out, `g_i = λ_(1,i+1)`, `α = ((1,1),(1,2))`, Lee's finite presentation
(arXiv:1212.0257, Theorem C). The established reduction theorem gives
`A(L) <= δ(2L+2)` and `δ(L) <= C L^3 (A(CL)+1)`, where `A` is the commutation area.
Throughout, `n = 3` unless stated otherwise. For `n > 3` the same identities hold
inside the copy of the construction on rays `1,2,3`.

A fact used repeatedly: a relation of bounded length that holds in `H_3` has area
`O(1)` (it is a consequence of the finite presentation), and a free conjugate of a
relation has the same area.

### Line notation

Let `Λ = ray 2 ∪ ray 1`, identified with `Z`: position `p >= 0` is `(1,p+1)`, and
position `p < 0` is `(2,-p)`. Then `g_1` acts on `Λ` as `p -> p-1` and fixes ray 3.

- `a_j := α^(g_1^(-j)) = g_1^j α g_1^(-j)` is the transposition of positions `j, j+1`
  (all `j ∈ Z`). So `⟨α, g_1⟩` acts on `Λ` as `FSym(Z) ⋊ Z`, a copy of `H_2`. That
  group is not finitely presented, and its relators `[a_0, a_k]` are consequences
  in `H_3`.
- `ρ_j := g_2^(g_1^(-j)) = g_1^j g_2 g_1^(-j)` sends position `j` to `(3,1)`. It
  shifts positions `> j` down by one, fixes positions `< j`, and pushes ray 3
  outward.

Identities (all verified exactly by
`experiments/zaremsky-1-24-houghton-dehn-function-2026-09-16/check_identities.py`,
214 checks, for the index ranges printed there):

1. `g_1 g_2 g_1^(-1) g_2^(-1) = α`.
2. `ρ_j = a_j ρ_(j+1)`. As words this is `g_1^j (g_2 = α · g_1 g_2 g_1^(-1)) g_1^(-j)`,
   a free conjugate of a bounded relation, so its area is `O(1)` uniformly in `j`.
3. `a_d^(ρ_j) = a_(d-1)` if `d >= j+1`, and `a_d^(ρ_j) = a_d` if `d <= j-2`.
4. `α^(g_2^(-k)) = a_k` for `k >= 0`.

### Four relation families

- `F(d) = Area([a_0, a_d])`, `d >= 2`. This is `w_d` of
  `houghton-far-transposition-commutation-is-superpolynomial` up to free conjugation
  and `α^2` relators.
- `Q(d) = Area(g_2^(-1) a_d g_2 = a_(d-1))`, `d >= 1`. `Q(1) = O(1)`: it is Lee's
  relator `α^(ḡ_1) = α^(ḡ_2)`.
- `P(d) = Area([ρ_d, α])`, `d >= 2`.
- `C(k) = Area(α^(g_2^(-k)) = α^(g_1^(-k)))`, `k >= 1`: the route conversion
  between pushing ray 1 from ray 3 and from ray 2.

## 2. What was proven: the four families are polynomially equivalent

**Lemma.** There is a constant `c` such that for all `d >= 3`:

```text
(a) F(d) <= F(d-1) + 2 Q(d-2) + c,    F(2) <= c;
(b) Q(d) <= Σ_(i=2)^(d) F(i) + c d;
(c) P(d) <= Σ_(j=2)^(d-1) F(j) + c d;
(d) C(k) <= C(k-1) + Q(k),            C(0) = 0;
(e) F(d) <= P(d) + P(d+1) + c         (d >= 2; added by the referee).
```

So each of `F, Q, P, C` is bounded, at argument `d`, by `O(d^2)(1 + max_(i<=d+1) X(i))`
for any other family `X`: `F` bounds `Q, P` by (b), (c); `P` bounds `F` by (e); `Q`
bounds `F` by (a) and `C` by (d); and `C` bounds `Q`, because
`Q(k) <= C(k) + C(k-1) + O(1)` by writing both routes and freely cancelling. So
`F` is polynomially bounded iff `Q` is iff `P` is iff `C` is. (The original version of
this note stated the `P` equivalence without the inequality (e); see the Referee
section.)

*Proof of (a).* `F(2) = O(1)`: `[a_0, a_2]` is freely conjugate, by `g_1^2`, to
`[a_(-2), a_0]`, which is Lee's relator `[α, α^(g_1^2)]` up to inversion. For `d >= 3`,
conjugate the null-homotopic word `[a_0, a_d]` by `ρ_2`, which does not change the
area. Freely, `ρ_2^(-1) [a_0, a_d] ρ_2 = [ρ_2^(-1) a_0 ρ_2, ρ_2^(-1) a_d ρ_2]`.
Replace the letters:

- `ρ_2^(-1) a_0 ρ_2 -> a_0` uses the bounded relation `[ρ_2, α]` (identity 3), cost `O(1)`
  per occurrence.
- `ρ_2^(-1) a_d ρ_2` is freely `g_1^2 (g_2^(-1) a_(d-2) g_2) g_1^(-2)`. The inner
  relation `g_2^(-1) a_(d-2) g_2 = a_(d-3)` costs `Q(d-2)` (valid since `d-2 >= 1`),
  and `g_1^2 a_(d-3) g_1^(-2)` is freely `a_(d-1)`.

Each of `a_0, a_d` occurs twice (once inverted; inverse relations have equal area).
The result is `[a_0, a_(d-1)]`, of area `F(d-1)`. ∎

*Proof of (b).* Conjugating the relation word by `g_1^(-d)` (that is, `W -> g_1^(-d) W g_1^d = W^(g_1^d)`) gives the equivalent
relation `α^(ρ_(-d)) = a_(-1)`, where `ρ_(-d) = g_1^(-d) g_2 g_1^d`. By identity 2,
applied `d` times, `ρ_(-d) = a_(-d) a_(-d+1) ⋯ a_(-1) ρ_0` with area `O(d)`. Substitute
at both occurrences. The word becomes
`ρ_0^(-1) a_(-1)^(-1) ⋯ a_(-d)^(-1) α a_(-d) ⋯ a_(-1) ρ_0`. Eliminate the innermost
conjugations `a_(-i)^(-1) α a_(-i) -> α` for `i = d, d-1, ..., 2`. Each costs
`F(i) + O(1)`: `[α, a_(-i)]` is freely conjugate by `g_1^(-i)` to the inverse of
`[a_0, a_i]`. What remains, `(a_(-1) ρ_0)^(-1) α (a_(-1) ρ_0) = a_(-1)`, is a
bounded relation. ∎

*Proof of (c).* Identity 2 gives `ρ_(j+1) = a_j ρ_j` (with `α^2`). So
`ρ_d = a_(d-1) ⋯ a_2 ρ_2` with area `O(d)`. Commute `α` past `ρ_2` (bounded relation)
and past `a_2, ..., a_(d-1)` (costs `F(2), ..., F(d-1)`). ∎

*Proof of (d).* `α^(g_2^(-k))` is the word `g_2^k α g_2^(-k) = g_2 (g_2^(k-1) α g_2^(-(k-1))) g_2^(-1)`.
Replace the inner subword by `a_(k-1)`, cost `C(k-1)`. The relation
`g_2 a_(k-1) g_2^(-1) = a_k` is a free conjugate of the inverse of the `Q(k)`
relation, cost `Q(k)`. ∎

*Proof of (e)* (referee). Identity 2 says `a_d = ρ_d ρ_(d+1)^(-1)`. As words, the relation
`a_d ρ_(d+1) ρ_d^(-1) = 1` is freely conjugate (by `g_1^d`) to the bounded relation
`α g_1 g_2 g_1^(-1) g_2^(-1) = 1` (identity 1 and `α^2 = 1`), so area `O(1)`. In
`[α, a_d] = α^(-1) a_d^(-1) α a_d`, substitute both occurrences of `a_d`, giving
`α^(-1) ρ_(d+1) ρ_d^(-1) α ρ_d ρ_(d+1)^(-1)`. Replace `ρ_d^(-1) α ρ_d -> α` (cost `P(d)`),
then `ρ_(d+1) α ρ_(d+1)^(-1) -> α` (cost `P(d+1)`), leaving `α^(-1) α`. Up to `α^2`
relators and free conjugation this is `F(d)`. ∎

**Refinement of the recorded framing.** The Attempts on
`houghton-transposition-commutation-area-is-polynomial` and
`houghton-far-transposition-commutation-is-superpolynomial` say that route
conversions follow a Tower-of-Hanoi recursion `C(k) <= 2 C(k-1) + O(k)`. That is an
absolute recursion. Relative to the far-commutation family the picture is linear:
`C(k) <= Σ_(j<=k) Q(j) <= O(k^2)(1 + max_(i<=k) F(i))`. So route conversion
between rays 2 and 3 (for pushes along ray 1) is not an independent source of
superpolynomial growth. If `F` is polynomial, so is `C`. The exponential absolute
recursion only reappears when one tries to bound `F` itself, and every such attempt
below is circular.

**Scope.** The Lemma is a relative statement among explicit families. It does not
bound any of them absolutely, and it does not show that `A` (hence `δ`) is bounded
polynomially in `F`. The existing route `houghton-superpolynomial-dehn-from-far-commutation`
covers the other direction.

The Lemma holds verbatim in `H_n` for every `n >= 3`, because `g_1, g_2, α` act on
rays `1,2,3` as above, fix all other rays, and bounded relations have bounded area.
The ray-swap automorphism (exchange rays 2 and 3; `g_1 <-> g_2`, `α -> α`) sends
Lee's relators to bounded relations. So the far commutations along `ray 3 ∪ ray 1`
have area `≍ F` as well.

## 3. Approaches tried and exactly where each dies

1. **Absolute recursion from the Lemma.** Combining (a) and (b) gives
   `F(d) <= F(d-1) + 2 Σ_(i<=d-2) F(i) + O(d)`, which only yields exponential
   growth. The alternative identity `ρ_0 = a_0 ρ_1` gives
   `Q(d) <= F(d) + Q(d-1) + O(1)`, which is circular against (a). Dies:
   no inequality was found that bounds `F(d)` by a family at scale `d/2`.
2. **Halving.** A recursion `F(k) <= c F(k/2) + poly(k)` would give a polynomial
   bound, and `F(k) <= C k F(k/2)` would give `k^(O(log k))`. The doubling map
   `(j,p) -> {(j,2p-1),(j,2p)}` induces an injective endomorphism of `FSym(Y)` and
   extends to an injective endomorphism `D` of `H_n`, with
   `D(λ_(a,b)) = λ_(a,b)^2 · ((b,1),(b,2))` (checked by hand). `D` is given on
   generators by bounded words, so `Area(D(w)) <= c Area(w)`, and the usable
   inequality goes the wrong way. `D(w_(k/2))` is not `w_k`: its conjugator
   `D(g_1)^(-k/2)` carries `k/2` correction transpositions, and converting it to
   `g_1^(-k)` needs commutations at distance `≍ k`. Dies: the corrections bring
   back `F` at full scale.
3. **Rerouting through `μ`** (a shift fixing the top two points of ray 1). Freely,
   `μ^m = g_1^(-m) · ν^(g_1^(-(m-1))) ⋯ ν^(g_1^(-1)) ν` for a 3-cycle `ν`. Converting
   `α^(g_1^(-k))` into a `μ`-routed word needs `[ν^(g_1^(-i)), ·]` for all `i < k`.
   Dies: this is `Σ_(i<k) F(i)`-type cost with branching factor `>= 2`, the recursion
   already recorded on `houghton-transposition-commutation-area-is-polynomial`.
4. **Morse push-down in Lee's CAT(0) cube complex** (descending links are chessboard
   complexes). Pushing a loop down one height level can double its length.
   Dies: without a coherent choice of descents across levels the bound is `e^x`.
   The patch relations for a coherent choice are skipping-shift commutations,
   which is the same family.
5. **Ladder toward "`F` polynomial implies `δ` polynomial".** For a word `z` centralizing
   `α` with transposition path `τ_i = α^(z_1 ⋯ z_i)`, and canonical conjugators `c_τ`
   (Lemma 2 of the 2026-09-13 artifact), the relation `[z, α]` is freely a product of
   the `ℓ` one-step relations `[c_(τ_(i-1)) z_i c_(τ_i)^(-1), α]`. So
   `A(ℓ) <= ℓ · E(ℓ + O(1))`, where `E(R)` is the maximum area of a one-step
   relation for `τ` of depth `<= R` and a generator `s`. If `E(R) <= poly(R)(1 + max_(d<=CR) F(d))`,
   then `δ` is polynomial iff `F` is. For the adjacent transpositions `a_j` on `Λ`
   with conjugators `g_1^(-j)`, the one-step relations are free (for `s = g_1^(±1)`)
   or, when the image is again adjacent on `Λ`, exactly a `Q`- or `P`-relation (for
   `s = g_2^(±1)`, `j ∉ {-1, 0}`) or `F` itself (for `s = α`, `|j| >= 2`). All of
   those reduce to `F` by the Lemma. **Where it dies:** in the remaining cases
   (`s = g_2` with `j ∈ {-1, 0}`, `s = g_2^(-1)` with `j = -1`, `s = α` with `j = ±1`;
   note `a_0^(g_2^(-1)) = a_1` is adjacent, a `Q(1)`-relation) the image is not an
   adjacent transposition on `Λ`. A general transposition needs a conjugator
   containing `g_2`-powers,
   for example `(0 m) = α^(g_1 g_2^(-(m-1)) g_1^(-1))` on `Λ`, or a token on ray 3
   (and, for `n > 3`, on rays `>= 4`). Then `s = g_2^(±1)` changes the ray-3 depth,
   or `s = g_1^(±1)` must be commuted past a `g_2`-power. The one-step relation then
   involves the stack-reorder relation (verified by the script)
   `ρ_i ρ_j = ρ_(j+1) ρ_i · ((3,1),(3,2))` (for `i < j`), and conjugates of it by
   `ρ`-words of length `≍ R`. I could not bound those areas by `F` without a
   commutation between a deep ray-3 transposition and a deep `Λ`-transposition
   routed through different `g_2`-power counts. This is a "mixed-route" far
   commutation, and I did not show it reduces to `F`. So the implication
   "`F` polynomial implies `δ` polynomial" remains unproven. It is the natural next
   hole. It was not created as a node, because no part of it is established.

## 4. Status of the target (checked 2026-09-16)

- Zaremsky, open problems list, version dated July 12, 2026 (PDF text extracted and
  read): Problem 1.24 is stated as open, with no update note.
- arXiv API search `abs:Houghton`, newest first, through arXiv:2609.08849
  (submitted 2026-09-08): no paper on Dehn functions or isoperimetric inequalities
  of Houghton groups after S. R. Lee, arXiv:1212.0257v1 (2 Dec 2012). The queries
  `abs:"Dehn function" AND abs:Houghton` (0 results) and
  `all:Houghton AND (isoperimetric OR Dehn OR filling)` (only 1212.0257 among group
  theory papers) agree.
- Abstracts checked for relevance, none on Dehn functions of `H_n`:
  arXiv:2110.06721 (Genevois–Lonjou–Urech), arXiv:2502.01544 (Farley; `H_n` acts on
  a CAT(0) cube complex), arXiv:2608.25614 (Hulbert–Zaremsky; no Houghton content).
- Known bounds used: `x^2 ≼ δ_(H_n)(x) ≼ e^x` (Lee's Theorem D and the gap theorem;
  already recorded on the root claim). Word-length distortion of finitary
  permutations is at most logarithmic (Burillo–Cleary–Martino–Röver,
  arXiv:1403.0026, Theorem 4.1, as already cited in the repo; not re-fetched today).

## 5. Literature consulted

- S. R. Lee, arXiv:1212.0257 (abstract page fetched 2026-09-16; Theorems C and D as
  cited in the repo artifacts).
- M. C. B. Zaremsky, open problems list, version of July 12, 2026 (fetched and read
  2026-09-16).
- arXiv API listings as above (2026-09-16).
- Repo artifacts `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md` and
  `research/artifacts/zp-thompson-v-dehn-function-2026-09-13.md` (halving remark).
  The latter cites Lorrain arXiv:2608.03813v2 (unrefereed); not re-fetched today.

## 6. Replay

`timeout 600 python3 experiments/zaremsky-1-24-houghton-dehn-function-2026-09-16/check_identities.py`
prints `ALL OK` (exact checks on points of depth `<= 30`, with rays truncated at
depth 60).

## Referee (2026-09-16)

**Checked.**

- Read this note, `check_identities.py`, and the nodes it refers to:
  `houghton-groups-have-polynomial-dehn-function`,
  `houghton-transposition-commutation-area-is-polynomial`,
  `houghton-far-transposition-commutation-is-superpolynomial`,
  `houghton-superpolynomial-dehn-from-far-commutation`,
  `houghton-dehn-polynomially-equivalent-to-commutation-area`, the root claim,
  and §0 and §3 of `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md`.
- Reran `check_identities.py`: it reports `ALL OK` (214 checks).
- Re-derived identities 1–4 and every step of Lemma (a)–(d) by hand. In particular
  (the solver's "weakest step"):
  - `ρ_2^(-1) a_d ρ_2` is freely `g_1^2 (g_2^(-1) a_(d-2) g_2) g_1^(-2)`, and the inner
    relation is exactly the `Q(d-2)` relation.
  - The `Q(d)` relation word `g_2^(-1) a_d g_2 a_(d-1)^(-1)` is freely conjugate to
    `α^(ρ_(-d)) a_(-1)^(-1)`.
  - `[α, a_(-i)]` is freely conjugate to `[a_0, a_i]` or its inverse, up to `α^(±1)`.
  - The `C` and `Q` relations convert into each other as stated.
- Machine-checked this bookkeeping, and the group identities it relies on, in the
  independent script `experiments/zaremsky-1-24-houghton-dehn-function-2026-09-16/referee_checks.py`:
  - Part 1 uses exact free reduction and cyclic-conjugacy tests.
  - Part 2 checks permutations with a separate implementation. It covers the `ρ_(-d)`
    and `ρ_d` factorizations, `α^(ρ_(-d)) = a_(-1)`, `a_d^(g_2) = a_(d-1)`,
    `[ρ_d, α] = 1` for `d >= 2`, and `α^(g_2^(-k)) = a_k`.
  - Negative controls return false. The script prints `ALL OK`.
- Area conventions: the note uses only standard facts. A free conjugate of a
  null-homotopic word has the same area, substituting subwords along relations adds
  their areas, and a bounded relation that holds in `H_n` has area `O(1)`. There are no
  hidden hypotheses. The `n > 3` transfer is fine, because the families live on rays
  `1, 2, 3` and the areas are taken in `H_n`'s own finite presentation.
- Literature gate, rechecked today:
  - Zaremsky's `open_problems.pdf` is still dated July 12, 2026, and item 24 (added
    2/24/26) is unchanged and still open.
  - The arXiv API query `abs:Houghton`, newest first, tops out at 2609.08849
    (2026-09-08). No abstract concerns Dehn functions.
  - arXiv:1212.0257 is Lee, "Geometry of Houghton's Groups", 2 Dec 2012, with
    exponential isoperimetric inequalities.
  - arXiv:2608.25614 is Hulbert–Zaremsky, "Word length, Morse theory, and
    Vietoris-Rips complexes", with no Houghton content.
  - The citations match the report. BCMR Theorem 4.1 and Lorrain were not re-fetched
    and remain as cited in the repo.

**Issues found and fixed.**

1. *Overclaim (fixed).* The note said `F, Q, P, C` are pairwise polynomially
   equivalent, but no inequality bounded `F` (or `Q`, `C`) by `P`. `P` was only
   bounded above. I added (e), `F(d) <= P(d) + P(d+1) + c`, with proof. It uses
   `a_d = ρ_d ρ_(d+1)^(-1)` (identity 2), which as words is a free conjugate of
   the bounded relation `α g_1 g_2 g_1^(-1) g_2^(-1)`, and it is machine-checked. With
   (e) the equivalence claim is correct. I also fixed the malformed bound
   `O(d^2)(1 + max_(i<=d))`, which becomes `O(d^2)(1 + max_(i<=d+1) X(i))`.
2. *Convention wording (fixed).* In (b), "conjugate by `g_1^(-d)`" now reads
   `W -> g_1^(-d) W g_1^d`, which under the note's convention is `W^(g_1^d)`.
3. *Case list in approach 5 (fixed).* `a_0^(g_2^(-1)) = a_1` is adjacent (a
   `Q(1)`-relation), so `s = g_2^(-1)`, `j = 0` does not belong among the failing
   cases. This does not change where the approach dies.
4. *Framing.* I renamed "Correction to the recorded framing" to "Refinement". The
   recorded Tower-of-Hanoi recursion is an absolute upper-bound scheme and is not
   wrong. The new content is the relative bound `C ≼ k^2 (1 + max F)`.

**Not promoted.** The Lemma is a correct but purely relative statement, and no
existing route requires it. It stays in notes/, as the solver chose. Section 3 reports
failures. It gives no obstructions, and the unverified hand remarks there (the general
doubling formula `D(λ_(a,b))`, the `μ^m` factorization) carry no weight elsewhere.

**Verdict.** Sound after fixes. It lands as a note plus two check scripts. There are no
graph nodes. Problem 1.24 remains open, as does whether `F` is polynomial and whether
polynomial `F` implies polynomial `δ`.
