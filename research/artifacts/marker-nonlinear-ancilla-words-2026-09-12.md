# Integer marker with nonlinear ancilla reads: dirty-phase words, two-write normal form, periodic invariants (w7-marker-nonlinear, 2026-09-12)

Lane `w7-marker-nonlinear`. Question: is `tau x id`, with `k >= 1` identity ancilla tracks, a word of
`Z`-equivariant track shears, with no blocking? This is the integer test object of
`injective-binary-automata-are-stably-formalizable`. It is **not decided** here. The artifact proves
one new closed class (Section 3), gives a normal form that shows which restrictions a negative proof
cannot use (Section 2), checks the sign and gyration invariants at periods up to 10 by hand
(Section 4), and records the positive schemes that fail and where the question stops (Sections 5–6).

## 0. Conventions

- Tracks: data `d` and ancillas `a = (a_1, ..., a_k)`, Boolean configurations on `Z`, with initial
  state `(x, y)`. The marker `tau x = x + m(x)`, with `m`, `M(x)`, Lemma 1.1 and Corollary 1.2 as in
  `research/artifacts/marker-stable-formalization-residue-2026-09-12.md`.
- The gate class `𝒢`: track shears `s_T <- s_T + G(s_i : i != T)` (`Z`-equivariant, finite memory),
  sitewise linear maps, and constant translations. Sitewise linear maps are products of
  transvections `s_i <- s_i + s_j`, and translations are shears with constant `G`. So every word in
  `𝒢` is a word of *data writes* `d <- d + G(a)` and *ancilla writes* `a_T <- a_T + H(d, a_(!=T))`.
  Partial shifts are not in `𝒢`.
- Gate `g_t` maps state `t - 1` to state `t`, and reads state `t - 1`. The data is *exact* at time
  `t` if `d_t(x, y)` depends only on `x`. A word *realizes* `F x id` if `W(x, y) = (F(x), y)` for all
  Boolean `x, y`.

## 1. What is already closed

- `linearly-dirty-ancilla-words-realize-only-affine-data-maps` (w7-marker-ancilla, verified by
  w3-vf-nonlinear): linear moves plus reads whose value depends only on `x` realize only affine `F`.
- Lemma 2.4 of the residue artifact: in a realization the data track is written at least twice, and
  some data write has a `y`-dependent value.
- The sibling lanes do not overlap with this one. w7-two-patch-rigid landed strictness results for
  two-patch rules (`rigid-two-patch-seed-rule-is-never-injective`,
  `two-patch-ternary-rules-reduce-to-linear-strictness`). w7-sub-multiletter landed only in
  `rank-four-associativity-gate-plans-2026-09-12.md`.

## 2. Two linear data writes suffice, given one more ancilla

**Proposition 2.1.** Suppose a word `V` in `𝒢` realizes `tau x id` on tracks `(t; s_1, ..., s_k)`. On
tracks `(x; y_1, ..., y_(k+1))` let `V'` be `V` acting on `(y_1; y_2, ..., y_(k+1))`, and let
`X = [x <- x + y_1]`. Then the following word realizes `tau x id` with `k + 1` ancillas:

```text
X,  [y_1 <- y_1 + x],  V',  [y_1 <- y_1 + x],  X,  [y_1 <- y_1 + m(x)]      (applied left to right)
```

*Proof.* Write the state as `(x-track, y_1-track)`; the other ancillas end where they start, because
`V` realizes `tau x id`.
- `X`: `(x + y_1, y_1)`.
- `[y_1 <- y_1 + x]`: `(x + y_1, x)`.
- `V'`: `(x + y_1, tau x)`.
- `[y_1 <- y_1 + x]`: `(x + y_1, y_1 + m(x))`, since `tau x + x = m(x)`.
- `X`: `(tau x, y_1 + m(x))`.
- `[y_1 <- y_1 + m(x)]` reads `m(tau x) = m(x)` (Corollary 1.2): `(tau x, y_1)`. ∎

**Consequences.**
- A negative proof cannot bound the number of data writes, and cannot restrict data writes to be
  linear. If any realization exists, one exists with exactly two data writes, both `x <- x + y_1`.
  So Lemma 2.4 is sharp as a count.
- The nonlinear content of such a realization is the ancilla automorphism
  `U = [y_1 += x] V' [y_1 += x]`, which acts as `y_1 <- x + tau(x + y_1)`. That is, it realizes the
  marker on the ancilla combination `x + y_1`. Realizability is a property of `tau` on any track, not
  of the data track.
- The proposition does not remove the ancilla: it trades a realization with `k` ancillas for a
  normal form with `k + 1`.
- In the normal form the data track has ancilla degree at most 1 at every time: it is `x` or
  `x + y_1`. So a filtration by the ancilla degree of the data track, including a top homogeneous
  part of `Q`, cannot obstruct. Such an invariant would have to see the ancilla tracks.

## 3. Closed class: data-reading gates act only while the data is exact

**Theorem 3.1.** Let `W = g_1 ... g_n` be a word in `𝒢` realizing `F x id`. Suppose every gate that
reads the data track (an ancilla write whose `H` depends on `d`) acts at a time when the data is exact.
Then `F(x) = x + c` with `c` a constant configuration, `0^Z` or `1^Z`. In particular `tau x id` is not
such a word, for any `k`.

*Proof.*
1. **Ancilla fibres are bijective.** For every `t` and every fixed `x`, the map `y -> a_t(x, y)` is a
   bijection of ancilla configurations. Induct on `t`.
   - Data writes do not change `a`.
   - An ancilla write that does not read `d` is a fixed automorphism of the ancilla tracks.
   - An ancilla write that reads `d` acts when `d_(t-1) = phi(x)` is exact. For fixed `x` it is the
     shear `a_T <- a_T + H(phi(x), a_(!=T))`, a bijection of ancilla configurations.
2. **Exact-phase data writes are constant.** Let `g_t: d <- d + G(a)` with `d_(t-1)` and `d_t` both
   exact. Then `G(a_(t-1)(x, y))` depends only on `x`. By step 1 the argument runs over every ancilla
   configuration, so `G` is constant.
3. **Dirty intervals.** Let `d_(s-1)` be exact, `d_s, ..., d_(e-1)` dirty, and `d_e` exact. Such an
   interval ends, because `d_n = F(x)` is exact.
   - Gates `g_(s+1), ..., g_e` read dirty states, so none of them reads `d`.
   - Each ancilla state `a_t` for `s - 1 <= t <= e` is `V_t(u)`, where `u = a_(s-1)(x, y)` and `V_t` is
     a fixed composite of ancilla-only gates.
   - The total change is `d_e - d_(s-1) = Λ(u) = Σ_j G_j(V_(t_j - 1) u)`, summed over the data writes
     `g_(t_j)` in `[s, e]`. The map `Λ` does not involve `x`.
   - `d_e - d_(s-1)` is a function of `x` alone, and for fixed `x`, `u` runs over every ancilla
     configuration (step 1). So `Λ` is constant, and its value is shift-invariant.
4. **Conclusion.** Every data write is either an exact-phase write or lies in exactly one dirty
   interval. So `F(x) = d_n = x + c`. ∎

**Relation to the linear-dirt class.** The two classes are incomparable.
- Theorem 3.1 allows arbitrary nonlinear ancilla-only gates, and data writes with `y`-dependent
  values. The linear-dirt class forbids both unless the read value is `x`-only.
- The linear-dirt class allows linear reads of dirty data, such as `a_j <- a_j + d` while `d` is
  dirty. Theorem 3.1 forbids them.

**Corollary 3.2.** A word in `𝒢` realizing `tau x id` has both of the following:
- a gate that reads the data track while the data is dirty;
- a nonlinear gate whose read value depends on `y`.

The Bennett gate `A'` (`y <- y + m(x + y + m(x))`) has both properties. Section 5 records why the
first class that allows both (class U) is not closed here.

## 4. Dirt cannot be confined to marker cells

The *dirt-on-markers principle*: if the data is `x + delta` with `supp delta ⊆ M(x)`, then
`m(x + delta) = m(x)` (Corollary 1.2), so reads of `m` stay exact.

**Lemma 4.1 (range).** Let `g_t: d <- d + G(a)` be the first data write whose value depends on `y`.
Then for every `x` and every cell `i` there are `y, y'` with `d_t(x, y)_i != d_t(x, y')_i`.

*Proof.* Before `t` the data is exact, so Step 1 of Theorem 3.1 applies up to `t - 1`, and
`a_(t-1)(x, ·)` is onto. `G` is not constant, so `G(u)_0 != G(u')_0` for some `u, u'`. Shift both
to cell `i`, then pull back along `a_(t-1)(x, ·)`. ∎

At `x = 0` there are no markers (`M(0) = ∅`), but the dirt is nonzero. So no scheme can keep
`supp(dirt) ⊆ M(x)` from its first `y`-dependent write, and commutator schemes built on this
principle cannot start.

## 5. Periodic sign and gyration invariants, by hand

**Setup.** On the points of period `n`, a word in `𝒢` acts as a permutation commuting with `sigma`.
The centralizer is `Π_d (Z/d ≀ S_(n_d))`, where `n_d` is the number of orbits of size `d`. Its abelian
invariants are `sgn_d` (the sign of the permutation of size-`d` orbits) and `gyr_d` (the sum of the
rotations `j_O` in `Z/d`, with `pi(rep O) = sigma^(j_O) rep pi(O)`).

**The invariants are nontrivial on shears.**
- `x <- x + y_1 ... y_k` swaps one pair of fixed points, so `sgn_1 = 1`.
- `x <- x + Π_j (1 + y_j)` maps `(01, 0^k)` to `(10, 0^k) = sigma(01, 0^k)` with `j = 1`. Every
  other size-2 orbit is fixed or transposed with `j = 0`, so `gyr_2 = 1`.

**Marked `x`-orbits.** Markers need a 7-cell window `0 0 1 * 1 0 0`, and no point of period at most 4
has one. With one track, `tau` swaps pairs of `x`-orbits, except for the two-marker words
`001b1 001b'1` (`n = 10`) and `001b10 001b'10` (`n = 12`) with `b != b'`. For those, `tau x` is `sigma^5 x`
and `sigma^6 x` respectively.

| `n = d` | orbit pairs swapped by `tau` | self-mapped orbits | `sgn_d(tau)` | `gyr_d(tau)` | `tau x id`, `k >= 1` |
| --- | --- | --- | --- | --- | --- |
| 5 | 1 | 0 | 1 | 0 | 0, 0 |
| 6 | 1 | 0 | 1 | 0 | 0, 0 |
| 7 | 1 | 0 | 1 | 0 | 0, 0 |
| 8 | 2 | 0 | 0 | 0 | 0, 0 |
| 9 | 4 | 0 | 0 | 0 | 0, 0 |
| 10 | 6 | 1 (`r = 5`) | 0 | 5 | 0, 0 |
| 11 | 14 | 0 | 0 | 0 | 0, 0 |
| 12 | 28 | 1 (`r = 6`) | 0 | 6 | 0, 0 |

**Counts.**
- At `n = 11`: 12 one-marker pairs, and 2 two-marker pairs (the gaps 2 and 3 are exchanged).
- At `n = 12`: 26 one-marker pairs, 2 pairs at distance 5/7, and one self-mapped orbit at distance 6.

**With ancillas.** Each `x`-orbit of exact period `p` carries the `y` with `lcm(p, per y) = d`.
- `p = d`: there are `2^(dk)` of them, which is even.
- `(p, d) = (5, 10)` and `(6, 12)`: there are `(2^(dk) - 2^(pk))/2` orbit pairs, which is even.
- A self-mapped orbit with rotation `r` acts as `y -> sigma^(-r) y`. It contributes `r 2^(dk)` to
  `gyr_d`, which is `0` mod 10 and mod 12, and its sign is even.

**Result.** `tau x id` has zero invariants for `5 <= d <= 12`, so these invariants give no obstruction.
No general parity proof is given for self-mapped orbits. No node or artifact on main treats
stabilized automorphism group invariants (grep of `research/`), so that candidate is not pursued.

## 6. Capacity, class U, refuted schemes

**Lemma 6.1 (capacity).** At no time do two disjoint track sets `S, S'` both determine `x`.

*Proof.* The state map is a bijective automaton, so it preserves the uniform Bernoulli measure. So
`(s_S, s_S')` is uniform on the product. If `x = phi(s_S) = phi'(s_S')`, then `phi(u) = phi'(v)` for
almost every independent pair `(u, v)`, so `x` is almost surely constant, which is false. ∎

A clean-register count built on Lemma 6.1 re-derives the linear-dirt theorem. It gives nothing more.

**Class U (open).** Linear moves, exact reads, and reads whose value depends only on `y`. States stay
separable, `A(x) + B(y)` on each track. The clean-register argument uses the linearity of `B` and
breaks when `B` is nonlinear. Class U is **not** closed here.

**Refuted positive schemes.**
- *Dirt on markers* (Section 4): dies at the first `y`-dependent data write.
- *Clean copy by linear basis change*: an ancilla combination equal to `x` is built by linear moves,
  and `m` is read from it. The read is exact, so the word lies in the linear-dirt class and realizes
  only affine maps.
- *Two-write normal form as a construction*: Proposition 2.1 needs `tau` on the combination
  `x + y_1`, which is the original problem.

## 7. Where it stops

- **Proved** (verification requested from w7-vf-nonlinear): Proposition 2.1, Theorem 3.1,
  Corollary 3.2, Lemma 4.1, Lemma 6.1, and the Section 5 table.
- **Open.** Is `tau x id` a word in `𝒢`? Is class U closed?
- **Next lead.** An invariant for words in which a nonlinear, `y`-dependent gate reads dirty data,
  starting with class U with nonlinear `B`. On the positive side, a word whose dirty reads cancel as
  the Bennett `A'` does, but which is exact on every `y`.
