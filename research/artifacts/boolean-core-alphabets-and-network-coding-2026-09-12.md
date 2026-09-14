# The Boolean core: network-coding form, product alphabets, and the smallest strict core

Lane `gk-n-boolean`, 2026-09-12. Handwritten proofs, no computation. Supports the claims
`boolean-core-is-uniform-single-demand-network-coding`,
`strict-rule-pairs-pass-to-product-alphabets`,
`smallest-boolean-strict-core-is-a-one-sided-inverse`,
`copy-codes-make-one-sided-table-identities-strict`,
`two-by-two-single-coincidence-strict-cores-classified`,
`equal-label-table-is-strict-at-three-symbols-not-two`, and the open holes
`surjunctivity-failure-descends-to-binary-alphabet` and `every-group-is-binary-surjunctive`.

The question: fix a pair of tables. Which finite alphabets carry rule pairs that satisfy the
decoder identity on the forward table and fail the reverse identity? The answers here are these.

- The problem is a uniform single-demand two-layer network-coding problem, evaluated on the
  network and on its transpose (Section 1).
- Strictness passes from `A` to `A x B` with the same tables. So the admissible alphabet sizes are
  closed under multiples, and at the group level surjunctivity over `kl` symbols implies it over
  `k` symbols (Section 2).
- Two pure Boolean filters (Section 3). A discrete forward table forces the reverse identity on
  every reverse table, over every alphabet. So does a one-relay or one-column shape whose reverse
  table contains the transpose.
- The one-coincidence table `(a,b) ~ (1,1)` (Section 4) is strict over some alphabet iff it is
  strict over every alphabet with at least two symbols, iff the reverse table does not repeat the
  coincidence. It is realized by a one-sided inverse in the bicyclic monoid and by no group.
  It is one of four strict single-coincidence 2 x 2 tables, not the only one (Section 6).
- All six single-coincidence 2 x 2 tables are classified (Section 6).
  - Three are strict through copy codes over every alphabet with at least two symbols.
  - Two are never strict.
  - The table `x_a = x_b` is strict over every alphabet with at least three symbols and over none
    with two. So strictness for fixed tables does not descend to two symbols.
- Whether strictness passes to every larger alphabet stays open. So does whether a group's
  strictness descends to two symbols once the tables may change (Section 5).

Nothing here decides the conjecture. For tables realized in some group, strict rules over any
alphabet would already be a counterexample.

## 0. Conventions

As in `gottschalk-rectangle-clauses-and-recognition-2026-09-12.md`:
- finite label sets `S` and `M`, each with a distinguished label `1`;
- forward cells `S x M` and reverse cells `M x S`;
- a table is an equivalence relation on the cells;
- rules `mu: A^M -> A` and `nu: A^S -> A`.

For a forward table `T_f` and a reverse table `T_r`:

    Dec(T_f):  nu( ( mu( (p(s,m))_m ) )_s ) = p(1,1)   for every p constant on T_f-classes,
    Enc(T_r):  mu( ( nu( (q(m,s))_s ) )_m ) = q(1,1)   for every q constant on T_r-classes.

Data are *strict* when `Dec(T_f)` holds and `Enc(T_r)` fails. That artifact proves the following.
- **Lemma 1.1:** coarser tables inherit both identities.
- **Lemma 1.2:** at a labelling in a group, `sigma tau = id` iff `Dec` holds at the realized
  forward table, and `tau sigma = id` iff `Enc` holds at the realized reverse table.
- **Theorem 1:** a group is not surjunctive iff it realizes strict data.
- **Corollary 1.4:** a labelling whose forward table contains `T_f` and whose reverse table is
  contained in `T_r` realizes the strict data `(T_f, T_r)`.

For a forward table `T`, write `T^t` for the transposed relation on `M x S`, meaning
`(m,s) T^t (m',s')` iff `(s,m) T (s',m')`.

## 1. The network-coding form

**Definition.** For a table `T` on `S x M`, the network `N(T)` has:
- **sources:** one source per class `c` of `T`, carrying a symbol `p_c` in `A`;
- **relays:** one relay per label `s` in `S`. Relay `s` receives the ordered tuple
  `(p_[(s,m)])_(m in M)`, so a class may feed several inputs of one relay and several relays.
  It outputs `mu` of that tuple;
- **sink:** receives the ordered tuple of relay outputs `(y_s)_(s in S)` and outputs `nu` of it;
- **demand:** the sink must output the source symbol of the class of `(1,1)`.

A code is a pair `(mu, nu)`. The relay function is shared by all relays, so the code is uniform.
It *solves* `N(T)` over `A` if the demand is met for every assignment of source symbols.

The *transposed network* `N^t(T')` of a table `T'` on `M x S` has one relay per `m` in `M`, each
applying the shared function `nu` to `(q_[(m,s)])_(s in S)`. Its sink applies `mu`, and the demand
is again the source of the class of `(1,1)`.

**Proposition 1.** `Dec(T_f)` holds iff `(mu, nu)` solves `N(T_f)`, and `Enc(T_r)` holds iff
`(nu, mu)` solves `N^t(T_r)`. So strict data are exactly the uniform codes that solve the forward
network while the same code, transposed, fails the reverse network.

*Proof.* A function constant on the classes is exactly a source assignment. Relay `s` outputs
`mu((p(s,m))_m)` and the sink outputs `nu` of the tuple of relay outputs, which is the left side
of `Dec`. The reverse composite is the same computation with the roles exchanged. QED.

**Remarks.**
- **Differences from general network coding.** There is a single demand. One relay function is
  shared by every relay. The same code must also be evaluated on a second, transposed network, and
  strictness asks that it succeed on one and fail on the other.
- **Linear codes.** Over a finite field `F`, take `mu(w) = sum_m a_m w_m` and
  `nu(y) = sum_s b_s y_s`. The code solves `N(T_f)` iff `sum_((s,m) in c) b_s a_m` is `1` for the
  class of `(1,1)` and `0` for every other class. It solves `N^t(T_r)` iff the same holds for
  `sum_((m,s) in c') a_m b_s`. At a labelling in `K` these conditions are `beta alpha = 1` and
  `alpha beta = 1` in `F[K]`, with `alpha = sum a_m x_m` and `beta = sum b_s x_s`. So linear
  strict data are one-sided inverse pairs, the content of
  `stable-finiteness-failure-refutes-surjunctivity`.

## 2. Product alphabets

**Theorem 2.** Let `(mu, nu)` be strict for `(T_f, T_r)` over `A`, and let `B` be any finite
nonempty set. Define rules over `A x B` by

    mu'( ((a_m, b_m))_(m in M) ) = ( mu((a_m)_m), b_1 ),
    nu'( ((a_s, b_s))_(s in S) ) = ( nu((a_s)_s), b_1 ),

where `b_1` is the second coordinate at the label `1`. Then `(mu', nu')` is strict for the same
tables `(T_f, T_r)`.

*Proof.* Write `p = (p_A, p_B)`; both components are constant on the `T_f`-classes.
- **`Dec`.** Relay `s` outputs `(mu(p_A(s,.)), p_B(s,1))`. The sink therefore outputs
  `(nu((mu(p_A(s,.)))_s), p_B(1,1)) = (p_A(1,1), p_B(1,1)) = p(1,1)`, by `Dec(T_f)` for `p_A`.
- **`Enc` fails.** Choose `q_A`, constant on the `T_r`-classes, with
  `mu((nu(q_A(m,.)))_m) != q_A(1,1)`. Put `q = (q_A, q_B)` with `q_B` constant. The first
  component of the transposed composite of `q` is `mu((nu(q_A(m,.)))_m)`, which differs from
  `q_A(1,1)`. QED.

**Corollary 2.1.** Let `Adm(T_f, T_r)` be the set of sizes `|A|` over which strict rules exist.
If `k` is in `Adm` then so is `kl` for every `l >= 1`. The size `1` is never in `Adm`, since over
a one-symbol alphabet every identity holds.

**Corollary 2.2 (groups).** If a group `K` is not `A`-surjunctive, it is not
`(A x B)`-surjunctive, with the same memory sets. Equivalently, surjunctivity over alphabets of
size `kl` implies surjunctivity over alphabets of size `k`.

*Proof.* Theorem 1 of the rectangle-clause artifact gives strict data realized by a labelling of
`K`. Theorem 2 keeps its tables, and Corollary 1.4 there turns the new data into a strict automaton
over `A x B`. (Directly: `tau x id_B` with decoder `sigma x id_B`.) QED.

**Corollary 2.3.** Every group is surjunctive over every finite alphabet iff every group is
surjunctive over alphabets of size `n!` for every `n`. The same holds for any family of sizes in
which every positive integer divides some member.

## 3. Boolean filters

**Proposition 3 (discrete forward table).** Suppose `T_f` is discrete, with no two forward cells
identified. Then every solution `(mu, nu)` of `N(T_f)` over `A` has `mu = f o pi_1` and
`nu = f^-1 o pi_1` for a permutation `f` of `A`. It satisfies `Enc(T)` for every table `T` on
`M x S`.

*Proof.*
1. **`mu` determines the label-1 coordinate.** Suppose `mu(w) = mu(w')` with `w_1 != w'_1`. Take
   two assignments whose row `1` is `w`, respectively `w'`, and whose other rows agree. The sink
   receives the same tuple but must output `w_1`, respectively `w'_1`, which is impossible. So
   `w_1 = h(mu(w))` for some `h: A -> A`. The map `h` is onto, hence a permutation, and
   `mu = f o pi_1` with `f = h^-1`.
2. **`nu` reads relay 1.** Every tuple in `A^S` is a tuple of relay outputs `(f(p(s,1)))_s`. The
   sink must return `p(1,1) = f^-1` of its first entry, so `nu = f^-1 o pi_1`.
3. **`Enc` holds.** For every `q`, `mu((nu(q(m,.)))_m) = f(nu(q(1,.))) = f(f^-1(q(1,1))) = q(1,1)`.
   QED.

So strictness needs at least one forward coincidence, at the Boolean level and over every
alphabet.

**Proposition 4 (one relay or one column).** Suppose `S = {1}` or `M = {1}`, and `T_r` contains
`T_f^t`. Then every solution of `N(T_f)` solves `N^t(T_r)`.

*Proof.*
- **`S = {1}`.** `Dec` says `nu(mu(w)) = w_1` for every `T_f`-constant row `w`. The symbol `w_1` is
  free, so `g = nu` is a permutation of `A` and `mu(w) = g^-1(w_1)` on `T_f`-constant rows. Let `q`
  on `M x {1}` be `T_r`-constant. It is then `T_f^t`-constant, so the tuple `g o q(.,1)` is a
  `T_f`-constant row. Hence `mu((nu(q(m,1)))_m) = g^-1(g(q(1,1))) = q(1,1)`.
- **`M = {1}`.**
  - **`mu` is a permutation.** If `mu(c) = mu(c')` with `c != c'`, change the symbol of the class of
    `(1,1)` from `c` to `c'`. Every relay output stays the same, but the demand changes, which is
    impossible. So `mu = f` is a permutation.
  - **`nu` reads relay 1.** `nu(y) = f^-1(y_1)` on every tuple `y = f o p(.,1)` with `p`
    `T_f`-constant.
  - **`Enc` holds.** Let `q` on `{1} x S` be `T_r`-constant. Then `f^-1 o q(1,.)` is `T_f`-constant,
    so `nu(q(1,.)) = f^-1(q(1,1))` and `mu(nu(q(1,.))) = q(1,1)`. QED.

**Group-realizable 2 x 2 data.** Let `S = {1,a}` and `M = {1,b}`.
- The forward values are `1, x_b, x_a, x_a x_b`. The reverse values are `1, x_a, x_b, x_b x_a`.
- In a group `x_a x_b = 1` iff `x_b x_a = 1`. Also `x_a x_b = x_a` iff `x_b = 1` iff
  `x_b x_a = x_a`, and `x_a x_b = x_b` iff `x_a = 1` iff `x_b x_a = x_b`.
- So the realized reverse table is always the transpose of the realized forward table.
- The group-level exclusion of these shapes is `amenable-decoder-memory-forces-surjectivity`.
  Section 4 shows the transpose relation is exactly what the Boolean core needs.

## 4. The one-sided-inverse table

Let `S = {1,a}` and `M = {1,b}`, and let `T_f` be the forward table whose only coincidence is
`(a,b) ~ (1,1)`.

**Theorem 5.** For a reverse table `T_r` on `M x S`, these are equivalent:
1. some alphabet admits strict rules for `(T_f, T_r)`;
2. every alphabet with at least two symbols admits strict rules for `(T_f, T_r)`;
3. `T_r` does not identify `(b,a)` with `(1,1)`.

In case 2 the column copy works: `mu(u,v) = v` and `nu(y_1, y_a) = y_a`.

**Realizations.**
- **The bicyclic monoid.** The data `(T_f, discrete)` are realized in `< s, t | t s = 1 >` by
  `x_a = t` and `x_b = s`. The forward values are `1, s, t, ts = 1`, and the reverse values
  `1, t, s, st` are pairwise distinct.
- **No group.** No group realizes them, since `x_a x_b = 1` forces `x_b x_a = 1`.

*Proof.*
- **(3 => 2).** For the column copy, the sink outputs relay `a`'s output, which is
  `p(a,b) = p(1,1)`, so `Dec(T_f)` holds. The transposed composite is
  `mu(nu(q(1,1), q(1,a)), nu(q(b,1), q(b,a))) = nu(q(b,1), q(b,a)) = q(b,a)`. If `(b,a)` and
  `(1,1)` lie in different `T_r`-classes, a `q` taking different values on those two classes
  (two symbols suffice) makes `Enc(T_r)` fail.
- **(2 => 1)** is immediate.
- **(1 => 3).** Suppose `T_r` identifies `(b,a)` with `(1,1)`, and put
  `T_0 = {(b,a) ~ (1,1)}`, so `T_0` is contained in `T_r`.
  1. **A realization in `Z`.** In additive `Z`, the labelling `x_a = 1`, `x_b = -1` has forward
     values `0, -1, 1, 0` and reverse values `0, 1, -1, 0`. It realizes exactly `T_f` forward and
     `T_0` reverse.
  2. **`Enc(T_0)` holds.** `Z` is residually finite, hence surjunctive
     (`residually-finite-groups-are-surjunctive`). For any rules over any alphabet, `Dec(T_f)` gives
     `sigma tau = id` over `Z` by Lemma 1.2. So `tau` is injective, hence surjective, so
     `tau sigma = id`, which by Lemma 1.2 is `Enc(T_0)`.
  3. **`Enc(T_r)` holds.** `T_r` is coarser than `T_0`, so it inherits `Enc` by Lemma 1.1. QED.

For this table, then, strict rules exist uniformly over every alphabet with at least two symbols,
and the single obstruction is the group identity "a one-sided inverse is two-sided", the
combinatorial shadow of direct finiteness. Other single-coincidence tables are strict for other
reasons (Section 6).

## 5. Larger alphabets and descent (open)

Theorem 2 moves strictness up along multiples. Two questions are not settled here.

- **(Q1) Fixed tables:** does `k` in `Adm(T_f, T_r)` imply `n` in `Adm(T_f, T_r)` for every
  `n >= k`?
- **(Q2) Groups:** if `K` is not `A`-surjunctive for some finite `A`, is `K` not
  `{0,1}`-surjunctive? Here the tables may change. This is
  `surjunctivity-failure-descends-to-binary-alphabet`. Together with
  `every-group-is-binary-surjunctive` it would reduce the conjecture to two symbols, through the
  route `gottschalk-via-binary-alphabet-descent`.

**Attempts, and where each dies.**
- **Retraction.** Put `A` inside a larger `A'` with a retraction `r: A' -> A`, and use
  `mu o r^M`, `nu o r^S`. The fiber of `p(1,1)` is lost.
  - When the class of `(1,1)` meets only relay `1`, relay `1`'s output alone must carry both the
    symbol the rest of the code needs and the position of `p(1,1)` inside its fiber.
  - If the fibers of `r` have unequal sizes, some pattern sends relay `1`'s value into a small fiber
    while `p(1,1)` sits in a large one, so no extension of this shape works.
  - Equal fibers are exactly products, Theorem 2.
- **Erasure symbol.** Put `A' = A` plus a symbol `*`, and let relays output `*` whenever they read
  `*`. The sink then loses the `mu`-value of every relay that reads a starred cell. `Dec(T_f)` uses
  all relays, so `p(1,1)` cannot be recovered in general.
- **Block codes over a finite subgroup `H`.** Suppose `K` has a finite subgroup `H` with
  `2^|H| >= |A|`. The decoding map `x -> ( d((x(g h))_(h in H)) )_g` from `{0,1}^K` to `A^K` is
  equivariant. Encoding, however, needs an equivariant choice of positions inside each coset
  `gH`, which a group does not supply without markers. So an `A`-configuration cannot be written
  equivariantly in binary, and no strict binary automaton is obtained.
- **Sizes with a factor in common.** Theorem 2 covers them only when the new size is a multiple.
  For example, strictness at size `6` gives sizes `12, 18, ...` but says nothing about sizes `7` or
  `3`.

## 6. All single-coincidence 2 x 2 tables

Let `S = {1,a}` and `M = {1,b}`.
- **Forward cells:** `O = (1,1)`, `B = (1,b)`, `A = (a,1)`, `X = (a,b)`, with group values
  `1, x_b, x_a, x_a x_b`.
- **Reverse cells:** `O' = (1,1)`, `A' = (1,a)`, `B' = (b,1)`, `X' = (b,a)`, with group values
  `1, x_a, x_b, x_b x_a`.
- **Transpose:** sends `O, B, A, X` to `O', B', A', X'`.
- **Relays:** forward relay `1` reads `(O, B)` and relay `a` reads `(A, X)`. Reverse relay `1` reads
  `(O', A')` and relay `b` reads `(B', X')`.

**Lemma 6.1 (copy codes, any label sets).** For labels `s0` in `S` and `m0` in `M`, the code
`mu = pi_(m0)`, `nu = pi_(s0)` has forward composite `p(s0,m0)` and reverse composite `q(m0,s0)`.
So over every alphabet with at least two symbols it is strict for `(T_f, T_r)` iff
`(s0,m0) T_f (1,1)` and `(m0,s0)` is not `T_r`-related to `(1,1)`.

*Proof.* Relay `s` outputs `p(s,m0)` and the sink reads relay `s0`. The reverse computation
exchanges the roles. A `q` taking different values on the two separated classes witnesses the
failure. QED.

In a group, `x_(s0) x_(m0) = 1` forces `x_(m0) x_(s0) = 1`, so copy codes never give
counterexamples: their automata are the shifts by `x_(m0)` and `x_(s0)`.

**Theorem 6.2.** Let `T_f` have exactly one coincidence. Strict rules exist for `(T_f, T_r)`
exactly as follows.

| forward coincidence | group reading | strict iff `T_r` | alphabets |
|---|---|---|---|
| `O ~ X` | `x_a x_b = 1` | separates `X'` from `O'` | every `|A| >= 2` (copy code) |
| `O ~ B` | `x_b = 1` | separates `B'` from `O'` | every `|A| >= 2` (copy code) |
| `O ~ A` | `x_a = 1` | separates `A'` from `O'` | every `|A| >= 2` (copy code) |
| `B ~ A` | `x_a = x_b` | separates `A'` from `B'` | every `|A| >= 3`; none with `|A| = 2` |
| `B ~ X` | `x_b = x_a x_b` | never | none |
| `A ~ X` | `x_a = x_a x_b` | never | none |

*Proof, row by row.*
- **`O ~ X`.** This is Section 4.
- **`O ~ B`.**
  - *Strict.* Copy code with `s0 = 1`, `m0 = b`.
  - *Converse.* `Dec` says `nu(mu(c,c), mu(u,v)) = c` for all `c, u, v`. With `g(c) = mu(c,c)`,
    every `r` in the image of `mu` gives `nu(g(c), r) = c`. So `g` is a bijection, the image of `mu`
    is `A`, and `nu(y,r) = g^-1(y)` for all `y, r`. If `q(b,1) = q(1,1) = d`, both reverse relays
    output `g^-1(d)` and the sink returns `g(g^-1(d)) = d`.
- **`O ~ A`.**
  - *Strict.* Copy code with `s0 = a`, `m0 = 1`.
  - *Converse.* `Dec` says `nu(mu(c,w), mu(c,v)) = c` for all `c, w, v`, so `nu` is constant `c` on
    `I_c x I_c`, where `I_c` is the image of `mu(c,.)`. The `I_c` are pairwise disjoint and
    nonempty, hence singletons. So `mu(c,w) = g(c)` for a bijection `g`, and `nu(y,y) = g^-1(y)`.
    If `q(1,a) = q(1,1) = d`, reverse relay `1` outputs `g^-1(d)`, and the sink returns
    `g(g^-1(d)) = d` whatever relay `b` outputs.
- **`B ~ X`.** `Dec` says `nu(mu(c,w), mu(u,w)) = c` for all `c, u, w`.
  1. For fixed `w`, `h_w = mu(.,w)` is injective, hence a bijection, and `nu(y,z) = h_w^-1(y)` for
     every `z` in its image, which is `A`.
  2. So all `h_w` equal one `h`, with `mu = h o pi_1` and `nu = h^-1 o pi_1`.
  3. Every reverse composite returns `h(h^-1(q(1,1))) = q(1,1)`.
- **`A ~ X`.** `Dec` says `nu(mu(c,w), mu(u,u)) = c` for all `c, w, u`.
  1. For `z` in the diagonal image, `nu(.,z)` is constant `c` on `I_c`, so the `I_c` are disjoint
     singletons and `mu = g o pi_1`.
  2. The diagonal image is then `A`, and `nu = g^-1 o pi_1`.
  3. The reverse identity follows as for `B ~ X`.
- **`B ~ A`, repeated coincidence.** In additive `Z` the labelling `x_a = x_b = 1` has forward values
  `0, 1, 1, 2` and reverse values `0, 1, 1, 2`, realizing exactly `T_f` and `{A' ~ B'}`. `Z` is
  surjunctive, so `Dec(T_f)` forces `Enc({A' ~ B'})` as in Section 4, and hence `Enc` on every
  coarser `T_r`.
- **`B ~ A`, two symbols.** `Dec` says `nu(mu(c,w), mu(w,v)) = c` for all `c, w, v`.
  1. For fixed `w`, `h_w = mu(.,w)` is a bijection, and `nu(.,z) = h_w^-1` for `z` in
     `J_w = {mu(w,v) : v}`. If `J_w` meets `J_w'`, then `h_w = h_w'`.
  2. Over `{0,1}`, suppose `h_0 != h_1`. Then `J_0` and `J_1` are disjoint singletons, so
     `mu(u,v) = k(u)` for a bijection `k`, which gives `h_0 = h_1 = k`, a contradiction.
  3. So `h_0 = h_1 = h` and `mu = h o pi_1`. The `J_w` then cover `A`, so `nu = h^-1 o pi_1`, and the
     reverse identity holds on every `T_r`.
- **`B ~ A`, three or more symbols.** Split `A` into blocks `P = {0,1}` and `Q = A \ P`. Put
  `g_P = id` and `g_Q = (0 1)`; both preserve the blocks and are involutions. Write `B(z)` for the
  block of `z`, and use the same rule for both automata:

      mu(u,v) = nu(u,v) = g_B(v)(u).

  - *`Dec` holds.* Relay `a` reads `(w,v)` and outputs `g_B(v)(w)`, which lies in the block of `w`.
    Relay `1` reads `(c,w)` and outputs `g_B(w)(c)`. The sink outputs `g_B(w)(g_B(w)(c)) = c`.
  - *`Enc` fails.* Reverse relay `1` outputs `g_B(e)(d)`, with `d = q(1,1)` and `e = q(1,a)`. Relay
    `b` outputs a symbol in the block of `e' = q(b,1)`, whatever `q(b,a)` is. So the sink outputs
    `g_B(e')(g_B(e)(d))`. Suppose `T_r` separates `A'` from `B'`.
    - If `O' ~ B'`, take `e = 2`, `e' = d = 0`. The sink outputs `(0 1)(0) = 1`.
    - Otherwise take `e = d = 0` and `e' = 2`. This is consistent whether or not `O' ~ A'`. The sink
      outputs `(0 1)(0) = 1`.
    - `X'` enters only through the block of relay `b`'s output, so any identification involving
      `X'` is harmless.

  QED.

**Corollary 6.3 (fixed tables do not descend).** For `T_f = {(1,b) ~ (a,1)}` and discrete `T_r`,
the alphabet sizes admitting strict rules are exactly `n >= 3`. So strictness for fixed tables does
not descend to two symbols, and it is not always available at two symbols when available at some
size. Group-level descent, `surjunctivity-failure-descends-to-binary-alphabet`, lets the tables
change and is not refuted by this.

**Example 6.4 (a triple coincidence).** Let `T_f = {B ~ A ~ X}`, read in groups as
`x_a = x_b = x_a x_b`. Over `A = {0, ..., n-1}` with `n >= 3`, put `h_0 = id`, `h_1 = (0 2)`,
`h_2 = (0 1)` and `h_w = id` for `w >= 3`. Each `h_w` is an involution with `h_w(w) = w`. Take
`mu(u,v) = nu(u,v) = h_v(u)`.
- **`Dec` holds.** Relay `1` outputs `h_w(c)`, relay `a` outputs `h_w(w) = w`, and the sink outputs
  `h_w(h_w(c)) = c`.
- **`Enc` fails.** Take `q(1,1) = q(1,a) = q(b,1) = 0` and `q(b,a) = 2`. Relay `1` outputs
  `h_0(0) = 0`, relay `b` outputs `h_2(0) = 1`, and the sink outputs `h_1(0) = 2`.
  - With `q(1,1) = 2` instead, relay `1` outputs `2`, relay `b` outputs `1`, and the sink outputs
    `h_1(2) = 0`.
  - So the code is strict for every `T_r` that identifies `A'` with `B'` and separates `X'` from
    them. `T_r` separating `A'` from `B'` is covered by the `B ~ A` block code, since `Dec` passes to
    the coarser `T_f`.
- **Converse.**
  - Every code with `Dec(T_f)` has `mu(c,w) = h_w(c)` for bijections `h_w`, has
    `nu(., h_w(w)) = h_w^-1`, and has `w -> h_w(w)` bijective.
  - If `q(1,a) = q(b,1) = q(b,a) = e`, reverse relay `b` outputs the `w` with `h_w(w) = e`, relay `1`
    outputs `h_w^-1(d)`, and the sink returns `h_w(h_w^-1(d)) = d`.
  - So `T_f` is strict for `T_r` iff `T_r` does not contain `{A' ~ B' ~ X'}`, over every alphabet
    with at least three symbols.
- **Two symbols.** Injectivity of `w -> h_w(w)` forces `h_0 = h_1`, so the table is never strict.

Multi-coincidence tables other than Example 6.4 are not classified here. The kill tables need not
be group- or monoid-realized reverse tables. For `O ~ B` the kill table `{O' ~ B'}` is strictly
finer than the reverse table `{O' ~ B', A' ~ X'}` of any monoid labelling with `x_b = 1`.
