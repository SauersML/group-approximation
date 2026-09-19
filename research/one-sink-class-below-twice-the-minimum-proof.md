---
rg: 2
id: one-sink-class-below-twice-the-minimum-proof
kind: route
title: Reprove upset descent by a pinned particle count, then note that every proper upset of every power has at least n0 letters, which below 2 n0 leaves room for one sink class and at n0 + 1 for one transient letter, a singleton class
target: strict-automata-below-twice-the-minimum-have-one-sink-class
requires:
  - transition-digraph-capacity-lifts-give-nonsurjunctive-sizes
---

Complete proof. Notation as in the target. The import is used only in items 3 and 4, for the size conclusions.

## Import, verbatim

`transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`, Theorem, items 2 and 3 (there `τ` is strict on `A^G`,
`|A| = k`, over any group `G`):
- "**Two-level form.** If `U` is an upset with `b = |U|` and `z = k - b`, then `bm + zs ∈ NS(G)` for all `1 <= s <= m`."
- "**Gcd form.** `g(τ)` is also the gcd of all upset sizes. `NS(G)` contains every multiple `d·n'` of `d = g(τ)`
  above some bound. [...] With `g(τ) = 1`, `NS(G)` is cofinite."

There, "An *upset* is `U ⊆ A` closed under `R(τ)`" and "`g(τ) = gcd` of the class sizes", classes being the
strongly connected components of `R(τ)`. Both items are applied below to `Ψ^p`, a strict automaton over the same
`G` with memory `M^p ∋ 1`.

## Step 0. Two elementary facts about powers

- (P1) `Ψ^p` is strict for every `p >= 1`. It is injective as a composite of injections. If `Ψ^p` were onto, then
  `Ψ` would be onto, since `Ψ^p(A^G) ⊆ Ψ(A^G)`.
- (P2) `R(Ψ^(qr)) ⊆ R(Ψ^q)^r`, the `r`-fold relation composite. The pair `(x(g), Ψ^(qr)(x)(g))` is joined by the path
  `x(g) -> Ψ^q(x)(g) -> Ψ^(2q)(x)(g) -> ... -> Ψ^(qr)(x)(g)`, and each step lies in `R(Ψ^q)`.

## Step 1. Upset descent (item 0), by a pinned particle count

This reproves the upset descent theorem of the wave-18 branch (`strict-automaton-upsets-give-smaller-nonsurjunctive-sizes`,
route `upset-restriction-pinned-particle-count`, held and not in this tree), so that nothing here depends on it.

Let `Φ(x)(g) = ν((g^(-1)x)|_N)` be injective with `1 ∈ N`, let `U` be a nonempty upset of `R(Φ)`, and suppose that
`Φ_U = Φ|_(U^G)`, which maps `U^G` into `U^G`, is onto `U^G`. If `G` is finite, `Φ` is an injective self-map of a
finite set and so onto. Assume `G` is infinite.

1. **No particle is created.** Call `g` a particle of `x` if `x(g) ∉ U`. Since `U` is an upset, the particles of `Φ(x)`
   are among those of `x`. For finite `F ⊂ G` put `D_F = {x : x(g) ∈ U for g ∉ F}`. Then `Φ(D_F) ⊆ D_F`.
2. **The far output reads only the far input.** Put `S = F N^(-1)`, a finite set containing `F`. For `g ∉ S` we have
   `gN ∩ F = ∅`, so there is a map `Θ : U^(G \ F) -> A^(G \ S)` with `Φ(x)|_(G \ S) = Θ(x|_(G \ F))` for all `x ∈ D_F`.
   It takes values in `U^(G \ S)`: for `g ∉ S` we have `g ∉ F`, so `x(g) ∈ U` and hence `Φ(x)(g) ∈ U`.
3. **Fibre count.** Fix `t ∈ U^(G \ S)`. `W_t = {w ∈ U^G : w|_(G \ S) = t}` has `|U|^|S|` elements.
   - Since `Φ_U` is a bijection of `U^G`, its preimage `{u ∈ U^G : Θ(u|_(G \ F)) = t} = U^F × Θ^(-1)(t)` has
     `|U|^|S|` elements.
   - So `|Θ^(-1)(t)| = |U|^|S \ F|`.
4. **Each `D_F` is carried onto itself.** Let `y ∈ D_F` and `t = y|_(G \ S)`, which lies in `U^(G \ S)`.
   - `P_t = {x ∈ D_F : Θ(x|_(G \ F)) = t} = A^F × Θ^(-1)(t)`.
   - `Z_t = {z ∈ D_F : z|_(G \ S) = t}`, which is free in `A` on `F`, free in `U` on `S \ F`, and equal to `t` elsewhere.
   - Both have `|A|^|F| |U|^|S \ F|` elements. `Φ` maps `P_t` into `Z_t`, injectively, so onto. Hence `y ∈ Φ(D_F)`.
5. **Onto.** `⋃_F D_F` is dense, since `U ≠ ∅`. `Φ(A^G)` is compact and contains it, so `Φ(A^G) = A^G`. ∎

**Consequence (item 0).** Let `Ψ` be strict and `U` a nonempty proper upset of `R(Ψ^p)`. `Ψ^p` is injective (P1), and it
is not onto. So by Step 1, `(Ψ^p)_U` is not onto. It is injective, hence strict, and it is a cellular automaton over
`G` on the alphabet `U` (memory `M^p`, table the restriction). So `|U| ∈ NS(G)`, and `|U| >= n0`. A one-letter
alphabet carries only the identity, so `1 ∉ NS(G)` and `n0 >= 2`.

## Step 2. Digraph facts

Every letter has an out-arc in `R(Ψ^p)`, because every pattern has an output. So:
- (D1) The forward closure `↑a` of any letter is an upset, and contains a sink class.
- (D2) Every nonempty upset contains a sink class. Distinct sink classes are disjoint, and each one is an upset.
- (D3) A strongly connected digraph of period `d >= 2` has cyclic classes `V_0, ..., V_(d-1)`. They are nonempty,
  partition it, and every arc goes from some `V_i` to `V_(i+1 mod d)`. If the digraph is a sink class `C` of `R(Ψ^p)`,
  there are no arcs out of `C`, so each `V_i` is closed under `R(Ψ^p)^d`. By (P2) it is then closed under
  `R(Ψ^(pd))`, so it is a nonempty proper upset of `R(Ψ^(pd))`.

## Step 3. Items 1 and 2

**Item 1.**
- If `R(Ψ^p)` has `r >= 2` sink classes, each is a proper nonempty upset, so each has at least `n0` letters by item 0.
  They are disjoint, so `r n0 <= m`.
- Let `C` be a sink class of period `d >= 2`. By (D3) and item 0 applied to `Ψ^(pd)`, each cyclic class has at least
  `n0` letters, so `d n0 <= |C|`. For `d = 1`, `n0 <= |C|` holds either way: `|C| ∈ NS(G)` if `C ≠ A`, and
  `|C| = m ∈ NS(G)` otherwise.
- If every `R(Ψ^p)` is strongly connected, a period `d >= 2` of `R(Ψ^p)` would give proper upsets of `R(Ψ^(pd))`. That
  contradicts strong connectivity of `R(Ψ^(pd))`. So every `R(Ψ^p)` is primitive.

**Item 2.** Let `m < 2 n0`.
- Two sink classes would need `2 n0 <= m`, so there is exactly one, `C_p`, which is nonempty by (D1).
- A period `d >= 2` would need `2 n0 <= d n0 <= |C_p| <= m`. So `C_p` is primitive.
- Every nonempty upset contains a sink class (D2), hence contains `C_p`.
- If `C_p ≠ A`, then `C_p` is a proper upset, so `|C_p| ∈ NS(G)` and `(Ψ^p)_(C_p)` is strict, by item 0. There are
  `m - |C_p| <= m - n0 < n0` transient letters.
- **Exact sub-alphabets.** If `V` and `A \ V` are both nonempty upsets of `R(Ψ)`, item 0 gives `|V|, m - |V| ∈ NS(G)`,
  in any size range. Below `2 n0` they would be two disjoint upsets, and each would contain `C_1`. That is
  impossible.

## Step 4. Item 3 (the second failing size)

Let `m < 2 n0` and `NS(G) ∩ (n0, m) = ∅`, and fix `p`. Suppose `R(Ψ^p)` is not strongly connected. Then `C = C_p ≠ A`.
- `|C| ∈ NS(G) ∩ [n0, m)`, which forces `|C| = n0`.
- Put `T = A \ C`, so `|T| = m - n0 >= 1`. For `a ∈ T`, the upset `↑a` contains `C` (item 2) and `a`. So
  `|↑a| > n0`, and `|↑a|` lies in `NS(G) ∪ {m}` (item 0 if proper). The gap forces `|↑a| = m`, i.e. `↑a = A`.
- So every `a ∈ T` reaches every letter. Any two letters of `T` reach each other, and no letter of `C` reaches `T`.
  The classes are exactly `C` and `T`.
- `C` is an upset with `b = n0` and `z = m - n0`. The imported two-level form, applied to the strict `Ψ^p` on `m`
  letters, gives `n0 a + (m - n0) s ∈ NS(G)` for `1 <= s <= a`.
- `g(Ψ^p) = gcd(n0, m - n0) = gcd(n0, m)`. The gcd form gives every large multiple of it, and cofiniteness when it
  is `1`.

## Step 5. Item 4 (one letter above the minimum)

Let `m = n0 + 1`. Since `n0 >= 2`, `m < 2 n0`, and `NS(G) ∩ (n0, n0 + 1) = ∅` trivially, so item 3 applies to every
power. Suppose `Ψ` is not robustly primitive, and pick `p` with `R(Ψ^p)` not strongly connected.
- **Shape.** By item 3 the classes are `C` with `|C| = n0` and `T = {*}`. `C = A \ {*}` is an upset, so `*` is never
  created by `Ψ^p`, and `{*}` is a singleton class.
- **Uniqueness of the letter.** A letter never created by `Ψ^q` is never created by any `Ψ^(qj)`, by induction on `j`.
  Suppose `R(Ψ^q)` is not strongly connected either, with letter `*'`. If `*' ≠ *`, both are never created by `Ψ^(pq)`.
  Then `A \ {*, *'}`, an intersection of two upsets of `R(Ψ^(pq))`, is an upset with `n0 - 1 >= 1` letters, which
  contradicts item 0. So the letter is the same for every such power.
- **Constants.** `Ψ^p` maps each constant `a^G` to a constant, by shift invariance, and injectively, so it permutes
  the constants by some `π`. Since `C` is an upset, `π(C) ⊆ C`, so `π(*) = *` and `Ψ^p(*^G) = *^G`.
- **Destruction.** `*` is destroyed in some context. Otherwise `{*}` is an upset of `R(Ψ^p)` of size `1 ∉ NS(G)`,
  against item 0.
- **The core.** `(Ψ^p)_C` is strict on `n0` letters, by item 0. Any strict `Φ` on `n0` letters is robustly primitive: a
  nonempty proper upset of some `R(Φ^q)` would have size in `NS(G)` below `n0`.
- **Sizes.** `g(Ψ^p) = gcd(n0, 1) = 1`. The two-level form with `b = n0`, `z = 1` gives `n0 a + s ∈ NS(G)` for
  `1 <= s <= a`. For `a >= n0` the interval `[n0 a + 1, n0 a + a]` reaches the start `n0 (a + 1) + 1` of the next one. So
  the union over `a >= n0` is every `n >= n0^2 + 1`, which contains every power of two above `n0^2`.

## Step 6. Item 5

- **(a)** Take `Ψ` as in the second case of item 4. Then `NS(G)` contains `2^j` for every `j` with `2^j > n0^2`.
- **(b)** Under `every-group-is-surjunctive-over-binary-power-alphabets`, no `2^j` lies in any `NS(G)`. So no `NS(G)`
  contains all large multiples of a power of two, and in particular none is cofinite. Hence the second case of item 4
  never occurs, and neither does the two-class case of item 3 when `gcd(n0, m2)` is a power of two. What is left in
  both cases is: every power strongly connected, i.e. robustly primitive (item 1).
- **(c)** Let `Ψ` be injective on `(A ⊔ {*})^G` with `|A| = n0`.
  - If `*` is never destroyed, `{*}` is an upset and `Ψ_{*}` is the identity of the point `*^G`, which is onto. Step 1
    makes `Ψ` onto.
  - If `A` is an upset and `Ψ` is strict, then `R(Ψ)` is not strongly connected. Item 4 applies with `p = 1`, and
    `NS(G)` contains every `n >= n0^2 + 1`.
  - An exact `*`, meaning both `{*}` and `A` are upsets, falls under the first case.

## Remark: strictness is not free in shape (c)

Let `Ψ` be injective with `A` an upset and `Ψ_A` strict. This does not force `Ψ` to be strict. If `Ψ` is bijective,
then `Ψ(x)(g) ∈ {*}` implies `x(g) = *`, so `{*}` is an upset of `R(Ψ^(-1))`. Step 1 then shows only that `Ψ^(-1)` is
onto, which it is. So a witness in case (c) must be strict for some reason beyond its restriction, and the target
records this.

## Checks

`experiments/sink-class-structure-2026-09-17/check_sink_structure.py` checks the digraph part of Steps 2–5
on two sets of digraphs: every digraph with at most 4 vertices, and 60000 random digraphs each on 5 and on 6 vertices.
It tries every admissible set `N` of allowed sizes with minimum `n0`. The digraphs have no vertex without an out-arc,
and all proper forward-closed sets have allowed sizes. The axiom used for powers is the one proved above: cyclic
classes of sink classes must have allowed sizes.
- The checks cover item 1, item 2, the two-class conclusion of item 3, and the shape of item 4. All pass.
- The second alternatives do occur at digraph level. For example, `m = 4`, `n0 = 3` has 7784 admissible digraphs
  that are not strongly connected. So the digraph argument alone cannot remove them, and item 4 needs the capacity
  lift for its conclusion.
