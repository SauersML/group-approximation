# A two-by-three table pair that is strict exactly at composite alphabet sizes

Swarm agent `swarm-strict-rule-pairs-ascend-to-la`, 2026-09-16. Target: `strict-rule-pairs-ascend-to-larger-alphabets`,
question (Q1) of `boolean-core-alphabets-and-network-coding-2026-09-12.md`, Section 5. **Refuted.** One fixed pair of
tables admits strict rules over 4 symbols and over no alphabet of prime size. The group-level ascent question stays
open and is recorded as `nonsurjunctive-alphabet-sizes-are-upward-closed`. Nothing here is independently reviewed.
Every computation is reproducible with `experiments/composite-size-strict-table-2026-09-16/verify_composite_table.py`.

## 0. Conventions

As in Section 0 of the boolean artifact:
- finite label sets `S` and `M`, each with a distinguished label `1`;
- forward cells `S x M`, reverse cells `M x S`; a *table* is an equivalence relation on the cells;
- rules `mu : A^M -> A` and `nu : A^S -> A`;
- `Dec(T_f)`: `nu( (mu((p(s,m))_m))_s ) = p(1,1)` for every `p` constant on `T_f`-classes;
- `Enc(T_r)`: `mu( (nu((q(m,s))_s))_m ) = q(1,1)` for every `q` constant on `T_r`-classes;
- `(mu, nu)` is *strict* for `(T_f, T_r)` when `Dec(T_f)` holds and `Enc(T_r)` fails.

Write `Adm(T_f, T_r)` for the set of `n >= 2` such that some alphabet with `n` symbols carries a strict pair.
The target asserted: `k ∈ Adm(T_f, T_r)` and `n >= k` imply `n ∈ Adm(T_f, T_r)`, for every table pair.

## 1. The table pair and the theorem

Take `S = {1, a}` and `M = {1, b, c}`.
- **Forward table `T_f`.** One nontrivial class `O = {(1,1), (1,b), (a,c)}`; the cells `(1,c)`, `(a,1)`, `(a,b)` are
  singletons.
- **Reverse table `T_r = T_f^t`.** One nontrivial class `{(1,1), (b,1), (c,a)}`; the cells `(1,a)`, `(b,a)`, `(c,1)` are
  singletons.

**Network form.** Name the forward sources `o = p(1,1)`, `e = p(1,c)`, `f = p(a,1)`, `g = p(a,b)`. Relay `1` reads
`(p(1,1), p(1,b), p(1,c)) = (o, o, e)` and relay `a` reads `(p(a,1), p(a,b), p(a,c)) = (f, g, o)`. So

    Dec(T_f):   nu( mu(o, o, e), mu(f, g, o) ) = o          for all o, e, f, g in A.

Name the reverse sources `o = q(1,1)`, `u = q(1,a)`, `v = q(b,a)`, `w = q(c,1)`. Reverse relay `1` reads `(o, u)`,
relay `b` reads `(q(b,1), q(b,a)) = (o, v)` and relay `c` reads `(q(c,1), q(c,a)) = (w, o)`. So

    Enc(T_r):   mu( nu(o, u), nu(o, v), nu(w, o) ) = o     for all o, u, v, w in A.

**Theorem.** `Adm(T_f, T_r)` is the set of composite integers.

More generally, let `T_r'` be any reverse table in which `(b,1)` and `(c,a)` are equivalent to `(1,1)`, while `(1,a)` and
`(b,a)` are not equivalent to each other. Then `Adm(T_f, T_r')` is the set of composite integers. There are 10 such
reverse tables; `T_r` is the finest of them.

**Corollary (refutation).** `4 ∈ Adm(T_f, T_r)` and `5 ∉ Adm(T_f, T_r)`. So `strict-rule-pairs-ascend-to-larger-alphabets`
is false. There is no threshold either: above every admissible size there is a prime, which is not admissible.

The theorem is Proposition 2.1 (composite sizes) together with Proposition 3.2 (prime sizes).

## 2. Composite sizes: a two-digit code

**Proposition 2.1.** Let `n = |B| |C|` with `|B|, |C| >= 2`. Then `n ∈ Adm(T_f, T_r')` for every `T_r'` as in Section 1.

*Construction.* Put `A = B x C` with projections `beta : A -> B` and `gamma : A -> C`, write `(β, γ)` for the symbol with
these coordinates, and fix a fixed-point-free permutation `pi` of `C`. Define

    mu(x_1, x_b, x_c) = ( beta(x_c), gamma(x_1) )        if x_1 = x_b,
                        ( beta(x_c), pi(gamma(x_1)) )    if x_1 != x_b;
    nu(y_1, y_a)      = ( beta(y_a), gamma(y_1) ).

*`Dec(T_f)` holds.* Relay `1` reads `x_1 = x_b = o`, so it outputs `(beta(e), gamma(o))`. Relay `a` reads `x_c = o`, so its
output has `beta`-coordinate `beta(o)`. The sink outputs `(beta(relay a), gamma(relay 1)) = (beta(o), gamma(o)) = o`.

*`Enc(T_r')` fails.* Choose `q` constant on the `T_r'`-classes with `q(1,1) = o`, hence `q(b,1) = q(c,a) = o`, and with
`beta(q(1,a)) != beta(q(b,a))`. This is possible: `(1,a)` and `(b,a)` lie in different classes, at most one of which is
the class of `(1,1)`, so the value on the other class is free, and `|B| >= 2`. The reverse relays output

    r_1 = nu(o, q(1,a))     = ( beta(q(1,a)), gamma(o) ),
    r_b = nu(o, q(b,a))     = ( beta(q(b,a)), gamma(o) ),
    r_c = nu(q(c,1), o)     = ( beta(o), gamma(q(c,1)) ).

Since `r_1 != r_b`, `mu(r_1, r_b, r_c) = (beta(r_c), pi(gamma(r_1))) = (beta(o), pi(gamma(o))) != o`, as `pi` has no
fixed point. ∎

For `T_r` itself: `o`, `w` arbitrary and `beta(u) != beta(v)`.

*A second code at `n = 4`* (checked by the script, not used): symbols are bit pairs; relay `1` outputs the pair
`(t, x_1[t])` with `t` the parity of `x_c`, flipped in its second bit off the diagonal `x_1 != x_b`; the sink reads
`o[t] = v` and `o[1-t] = v XOR (first bit of y_a)` from `y_1 = (t, v)`.

## 3. Prime sizes: rectangle rigidity

**Lemma 3.1 (rectangle lemma).** Let `|A| = n >= 2` and `D : A x A -> A`. Suppose `(D(o,e), D(f,o))` determines `o`: there
is a map `Phi` with `Phi(D(o,e), D(f,o)) = o` for all `o, e, f`. Then
1. every fiber `D^{-1}(σ)` has exactly `n` elements and is a product `R_σ x C_σ`;
2. if `n` is prime, then `D(x,z) = h(x)` for a bijection `h`, or `D(x,z) = k(z)` for a bijection `k`.

*Proof.* Entropies are in base `n`, so `H` of a uniform variable on `A` is `1`.

- Let `O, E, F` be independent and uniform on `A`, and put `U = D(O,E)`, `V = D(F,O)`. Then `H(O | U, V) = 0`, so
  `1 = H(O) = I(O; U, V)`.
- `U` and `V` are conditionally independent given `O`, because they are functions of `(O,E)` and `(O,F)`. Hence
  `H(U,V | O) = H(U | O) + H(V | O)` and

      I(O; U,V) = H(U,V) - H(U|O) - H(V|O) <= H(U) + H(V) - H(U|O) - H(V|O) = I(O;U) + I(O;V).

- Let `X, Z` be independent and uniform on `A`, and put `W = D(X,Z)`. The pair `(O,U)` has the law of `(X,W)` and the pair
  `(O,V)` has the law of `(Z,W)`. Expanding entropies,

      I(X,Z; W) - I(X;W) - I(Z;W) = I(X;Z | W) - I(X;Z) = I(X;Z | W),

  since `I(X;Z) = 0`. As `W` is a function of `(X,Z)`, `I(X,Z; W) = H(W) <= 1`. So

      1 = I(O; U,V) <= I(X;W) + I(Z;W) = H(W) - I(X;Z | W) <= 1.

- Every inequality is an equality: `H(W) = 1` and `I(X;Z | W) = 0`.
  - `H(W) = 1` says `W` is uniform, so every fiber has `n^2 / n = n` elements.
  - Given `W = σ`, the pair `(X,Z)` is uniform on the fiber `D^{-1}(σ)`, and its coordinates are independent. The
    support of a product of two distributions is the product of their supports, so the fiber equals
    `R_σ x C_σ`, where `R_σ` and `C_σ` are its projections. So `|R_σ| |C_σ| = n`.
- If `n` is prime, each fiber is a full row `{x} x A` or a full column `A x {z}`. The `n` fibers partition `A x A`. A row
  and a column always meet, so two distinct fibers are never a row and a column. One fiber is never both, since a row
  that is also a column has one element and fibers have `n >= 2`. So either every fiber is a row or every fiber is a
  column. If every fiber is a row, then `D(x,z) = h(x)`, and `h` is injective because distinct rows are distinct
  fibers. Columns give `D(x,z) = k(z)` in the same way. ∎

**Proposition 3.2.** Let `|A| = n` be prime and let `(mu, nu)` satisfy `Dec(T_f)`. Then `Enc(T_r')` holds for every reverse
table `T_r'` in which `(b,1)` and `(c,a)` are equivalent to `(1,1)`. In particular no pair over `A` is strict for
`(T_f, T_r')`.

*Proof.* Put `D(x,z) = mu(x, x, z)`. `Dec(T_f)` with `f = g` reads `nu(D(o,e), D(f,o)) = o`, so Lemma 3.1 applies.

- **Case A: `D(x,z) = h(x)`.** Given `(y_1, y_a)`, put `o = h^{-1}(y_1)` and `f = h^{-1}(y_a)`. Then `D(o,e) = y_1` and
  `D(f,o) = y_a`, so `Dec` gives `nu(y_1, y_a) = h^{-1}(y_1)` for all `(y_1, y_a)`. Let `q` be constant on `T_r'`, with
  `q(1,1) = q(b,1) = o`. The reverse relays output `r_1 = h^{-1}(o)`, `r_b = h^{-1}(o)` and `r_c = h^{-1}(q(c,1))`. So
  `mu(r_1, r_b, r_c) = D(h^{-1}(o), r_c) = o`, and `Enc(T_r')` holds.
- **Case B: `D(x,z) = k(z)`.** `Dec` with `f = g` gives `nu(k(e), k(o)) = o` for all `e, o`, so `nu(y_1, y_a) = k^{-1}(y_a)`
  for all `(y_1, y_a)`. `Dec` with arbitrary `f, g` then gives `k^{-1}(mu(f,g,o)) = o`, so `mu(x_1, x_b, x_c) = k(x_c)`
  everywhere. Let `q` be constant on `T_r'`, with `q(1,1) = q(c,a) = o`. Then
  `mu(r_1, r_b, r_c) = k(r_c) = k(k^{-1}(q(c,a))) = o`, and `Enc(T_r')` holds. ∎

At prime sizes, then, every `Dec` solution agrees with a relabelled copy code on every input `Enc(T_r')` reads. In Case A, `nu` copies relay `1`
and `mu` copies label `1` on the diagonal `x_1 = x_b`; off the diagonal `mu` is arbitrary, and `Enc(T_r')` never reads
it there. In Case B, both rules copy the cell `(a,c)`. Both transposed cells `(b,1)` and
`(c,a)` sit in the origin class of `T_r`, so neither copy fails `Enc`. This matches
`copy-codes-make-one-sided-table-identities-strict`.

**Why the primes die.** Relay `1` sees `o` together with the nuisance `e`, and relay `a` sees `o` together with `f, g`.
The sink needs all of `o`, so the two relays must share `o` without loss. Equality in Shannon's inequalities forces every
fiber of the diagonal map `D` to be a rectangle of area `n`. At a prime area only rows and columns remain, and those are
the copy codes. A composite size splits `o` into two digits carried by different relays, and the off-diagonal twist
of `mu` breaks `Enc`.

## 4. What the example does and does not say

- **The target is false.** Adding `refuted_by: [table-pair-strict-exactly-at-composite-alphabet-sizes]` makes it
  `REFUTED`, and the routes requiring it (`gottschalk-via-alphabet-ascent`,
  `linear-sofic-surjunctivity-via-formalizability-and-ascent`) become `INVALIDATED`.
- **The tables are not realized in any group.** A labelling `x : S ⊔ M -> G` with `x_1 = 1` whose forward table contains
  `T_f` has `x_b = 1` and `x_a x_c = 1`, so `x_c = x_a^{-1}`. Its reverse table then identifies `(1,a)` with `(b,a)`,
  since `x_b x_a = x_a = x_1 x_a`. So no labelling has reverse table contained in `T_r'` for any `T_r'` of Section 1, and
  Corollary 1.4 of the boolean artifact never applies. The realized data (in `Z`: `x_a = 1`, `x_c = -1`, `x_b = 0`) have
  `(1,a) ~ (b,a)` in the reverse table, which is exactly the coincidence the two-digit code needed to avoid.
- **Realized tables cannot give such examples cheaply.** If a table pair realized in some group had a nonempty `Adm`,
  that group would not be surjunctive (Theorem 1 of the boolean artifact), and Gottschalk's conjecture would fail. So
  ascent restricted to realized table pairs cannot be refuted by any example short of refuting the conjecture.
- **The group-level question stays open.** Upward closure of `NS(G)` for every group `G` is what both invalidated routes
  actually used. It is recorded as `nonsurjunctive-alphabet-sizes-are-upward-closed`, with the route
  `gottschalk-via-upward-closed-nonsurjunctive-sizes`. By this example, any proof must use that the tables come from
  a group, or must change the tables.
- **The passive-block reduction.** `passive-block-involution-codes-ascend` reduced general ascent to the statement that
  every strict pair is equivalent to a copy code or to a passive-block involution code. Both kinds ascend, so the strict
  pairs here are equivalent to neither. The evidence in Section 6 of the boolean artifact covered only 2 x 2 tables, and
  every 2 x 2 table pair is monotone up to `n = 5` (Section 6 below).
- **Product closure does not extend to upward closure.** `strict-rule-pairs-pass-to-product-alphabets` gives closure
  under multiples. The composite numbers are closed under multiples and are not upward closed. Which other closure
  properties hold for all table pairs is not settled here.

## 5. Verification

`experiments/composite-size-strict-table-2026-09-16/verify_composite_table.py --sat` (Python 3, `python-sat`), run
2026-09-16 with output:

    product code 2x2 (n=4): Dec=True, Enc witness=(0, 0, 0, 2)
    product code 2x3 (n=6): Dec=True, Enc witness=(0, 0, 0, 3)
    product code 3x2 (n=6): Dec=True, Enc witness=(0, 0, 0, 2)
    product code 2x4 (n=8): Dec=True, Enc witness=(0, 0, 0, 4)
    product code 3x3 (n=9): Dec=True, Enc witness=(0, 0, 0, 3)
    selector code (n=4): Dec=True, Enc witness=(0, 0, 0, 2)
    reverse family: product code 2x2 fails Enc at all 10 reverse tables
    n=2 exhaustive: 34 Dec solutions, 0 strict
    rectangle lemma n=2: 4 determining matrices, all row- or column-constant bijections
    rectangle lemma n=3: 12 determining matrices, all row- or column-constant bijections
    SAT n=3: strict pair exists = False (135 vars, 1603 clauses, 0.0s)
    SAT n=5: strict pair exists = False (875 vars, 32901 clauses, 8.9s)
    SAT n=4: strict pair exists = True (384 vars, 8753 clauses, 0.0s)
    all checks passed

- `Dec` and `Enc` are checked by evaluating every source assignment (`n^4` of each).
- The `n = 2` check runs over all `2^8 * 2^4` rule pairs.
- The rectangle lemma is checked over all `n^(n^2)` maps `D` for `n = 2, 3`.
- The SAT encoding (CaDiCaL 1.5.3) is independent of the census encoder of Section 6. It assumes `q(1,1) = 0` in the
  `Enc` failure, which loses nothing, because conjugating `mu` and `nu` by a permutation of `A` preserves both identities.
- The `n = 5` and `n = 3` UNSAT results confirm Proposition 3.2 at those sizes. `n = 7` was not decided by SAT within
  10 minutes and rests on the proof alone.

## 6. Census of small table pairs

Scripts `fastsat.py`, `scan.py`, `follow.py` in the same experiments directory; logs `census-summary.txt`,
`follow23_nny5.txt` and `follow32_nny5.txt`.

- **Method.** Enumerate all set partitions `T_f`, `T_r` of the cells, up to permutations of the non-identity labels.
  Skip two kinds of pairs whose `Adm` is already known:
  - *abelian:* the relations of `T_f` in a free abelian group force a reverse table contained in `T_r`, so `Adm = ∅`
    (Corollary 1.4 and Theorem 1 of the boolean artifact; abelian groups are surjunctive);
  - *copy:* some cell of the origin class of `T_f` has its transpose outside the origin class of `T_r`, so `Adm` is every
    `n >= 2` (`copy-codes-make-one-sided-table-identities-strict`).

  For every other pair, run CaDiCaL at each `n` with a conflict budget; `Y` means SAT, `N` means UNSAT, `?` means budget
  exceeded.
- **2 x 2, `n = 2..5`.** 44 abelian, 113 copy, 29 `NYYY`, 39 `NNNN`. No gaps.
- **2 x 3, `n = 2..4`.** 658 abelian, 13170 copy, 2683 `NYY`, 1893 `YYY`, 2557 `NNN`, 121 `NNY`, 3 `NN?`.
- **3 x 2, `n = 2..4`.** 658 abelian, 13170 copy, 2724 `NYY`, 1839 `YYY`, 2554 `NNN`, 132 `NNY`, 8 `NN?`.
- **2 x 3 `NNY` pairs at `n = 5`.** 85 `Y` and 36 `N`. The 36 pairs with a gap at 5 use four forward tables. One is
  `T_f` of Section 1, with exactly the 10 reverse tables of the theorem.
- **3 x 2 `NNY` pairs at `n = 5`.** Partial run (`follow32_nny5.txt`, stopped by the 600 s cap). At least 109 of the 132
  pairs were processed: 19 `N`, 6 `?`, the rest `Y`. Not used anywhere.

The census is supplementary; the theorem does not depend on it. It shows gaps are not rare once `|M| = 3`.

## 7. Literature

The literature check ran 2026-09-16. Nothing consulted states or refutes table-level alphabet ascent, or discusses how
surjunctivity at a fixed table depends on the alphabet size. For the titles seen only in listings, this rests on the
titles and snippets. What was consulted:
- Titles seen in search listings only, not read: arXiv:2503.23435 (30 Mar 2025, "On Gottschalk's surjunctivity
  conjecture for non-uniform cellular automata"), arXiv:2410.17688 ("Strongly sofic monoids, sofic topological entropy,
  and surjunctivity"), arXiv:2403.05998 ("Generalized Gottschalk's conjecture for sofic groups and applications"),
  arXiv:2405.18287 ("Stable finiteness of monoid algebras and surjunctivity") and arXiv:2511.06586 (Nov 2025,
  "Surjunctivity does not characterize cosoficity of invariant random subgroups").
- Abstract page fetched: arXiv:1608.01738, J. Connelly and K. Zeger, "Linear Network Coding over Rings, Part I: Scalar
  Codes and Commutative Alphabets" (submitted 5 Aug 2016). It concerns linear codes over rings, where solvability is
  monotone along a quasi-order of rings, and does not treat nonlinear single-demand codes like these.
- Recalled and unverified: general network-coding solvability is not monotone in the alphabet size. Nothing here uses
  it.

The example is elementary, and no novelty is claimed beyond this graph.
