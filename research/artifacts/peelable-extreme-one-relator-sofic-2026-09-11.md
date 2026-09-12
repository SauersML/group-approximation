# Peelable Magnus extremes make one-relator groups sofic

Date: 2026-09-11. Written proof, not a Lean certificate. It closes a class
of one-relator groups and records the exact boundary of the method; it does
not answer Pestov's Question 4.10.

## 1. Setting and statement

Let `G = <a,t | w>` be a two-generator one-relator group with `w` cyclically
reduced and not a proper power in `F = F(a,t)`, so `G` is torsion-free.
Assume the exponent sum of `t` in `w` is zero. Put `a_i = t^(-i) a t^i` and
rewrite a suitable cyclic permutation of `w` as a word

    W_0 = W_0(a_m, ..., a_n)

in the free basis `{a_i}` of `ker(F -> Z)`, with `m` and `n` the least and
greatest indices occurring. Write `W_j` for the shift of `W_0` by `j`.

A **syllable** of a letter `x` in a cyclic word is a maximal cyclic subword
`x^e`, `e != 0`. Call the top letter `a_n` **peelable** when its occurrences
in the cyclic word `W_0` form

* exactly one syllable, or
* exactly two syllables `a_n^e` and `a_n^(+-e)` with the same absolute
  exponent.

Define peelability of the bottom letter `a_m` in the same way.

**Theorem.** If `n > m` and the top letter or the bottom letter of `W_0` is
peelable, then `G` is sofic.

If `n = m`, then `W_0 = a_m^e` and `w` is conjugate to `a^e`; torsion-freeness
forces `e = +-1` and `G` is infinite cyclic. So the theorem covers every case
in which some Magnus rewriting has a peelable extreme.

Examples inside the class: every `BS(k,l)` (the top letter is the single
syllable `a_1^k`); the Baumslag--Gersten group
`<a,t | a_1^(-1) a_0 a_1 = a_0^2>` (two syllables `a_1^(+-1)`); the Berlai
families `<a,b | (a^l)^(a^(b^n)) = a^(l+1)>` (two syllables `a_n^(+-1)`); and
relators such as `a_2 [a_0,a_1] a_2^(-1) [a_1, a_0 a_1]`, whose coefficient
words are not powers of a single letter and whose overlap rank is two.

## 2. Inputs

All standard; none is new here.

1. **Freiheitssatz** (Magnus, 1930; Lyndon--Schupp, *Combinatorial Group
   Theory*, Ch. II, §5). If `W` is cyclically reduced in `F(x_1,...,x_k)`
   and involves `x_1`, then `x_2,...,x_k` freely generate a free subgroup of
   `<x_1,...,x_k | W>`.
2. **Normal forms.** In an amalgam `A *_C B` with injective edge maps, and in
   an HNN extension with injective associated maps, the vertex groups embed.
   Every finite-order element is conjugate into a vertex group.
3. **Sofic permanence.** Amalgams of sofic groups over amenable subgroups are
   sofic (Elek--Szabo, *Sofic representations of amenable groups*,
   arXiv:1010.3424, Theorem 1). HNN extensions of sofic groups over amenable
   associated subgroups are sofic (Ciobanu--Holt--Rees, arXiv:1212.2739,
   Proposition 3.2). Sofic-by-amenable groups are sofic. Directed colimits
   of sofic groups are sofic; the finite-table proof is written out in
   `triangular-bs-chain-proof-2026-09-07.md`, §4.
4. **Kernel presentation.** With `K = <a_i (i in Z) | W_i (i in Z)>`, the
   index shift is an automorphism of `K`, and the split extension
   `E = K rtimes <t>` with `t^(-1) a_i t = a_(i+1)` is isomorphic to `G` by
   Tietze elimination of `a_i`, `i != 0`. The explicit verification is
   `mixed-conjugator-one-relator-proof-2026-09-07.md`, §2. Since `E/K = Z` is
   amenable, `G` is sofic as soon as `K` is.

## 3. One peeling step

Let `T` be a torsion-free group, `F_0 <= T` a free subgroup, and
`B = <F_0, y | W>` a one-relator group in which `W in F_0 * <y>` is cyclically
reduced, is not a proper power, involves at least one letter of `F_0`, and
`y` forms at most two syllables with equal absolute exponent.
Write the cyclic word `W` as one of

    (P1)  y^e U                 (one syllable),
    (P2)  y^e U y^(-e) V        (two syllables, opposite signs),
    (P3)  y^e U y^e V           (two syllables, same sign),

with `U, V` nonempty reduced words in the basis of `F_0`, hence nontrivial
elements of `F_0` and of `T`. Let `T' = (T * <y>)/<<W>>`.

**Lemma 3.1.** `T'` is obtained from `T` by at most two amalgams or HNN
extensions over infinite cyclic subgroups. In particular `T` embeds in `T'`,
`T'` is torsion-free, and `T'` is sofic whenever `T` is.

*Proof.* Every associated subgroup below is infinite cyclic because `T` is
torsion-free and the named generator is nontrivial.

(P1) The relation is `y^e = U^(-1)`, so

    T' = T *_(<U^(-1)> = <y^e>) <y>.

(P2) Put `z = y^e`. The relation `z U z^(-1) = V^(-1)` defines the HNN
extension `L = <T, z | z U z^(-1) = V^(-1)>`, and

    T' = L *_(<z> = <y^e>) <y>.

Eliminating `z` from the presentation of the right side recovers exactly
`W`. The stable letter `z` has infinite order in `L`.

(P3) Put `z = y^e` and `x = zU`. The relation `zUzV = 1` is equivalent to
`x^2 = V^(-1) U`. Here `V^(-1) U != 1`: otherwise `U = V` and
`W = (y^e U)^2` would be a proper power. Put

    L = T *_(<V^(-1)U> = <x^2>) <x>,       T' = L *_(<x U^(-1)> = <y^e>) <y>.

The element `x U^(-1)` has infinite order in `L`: it is nontrivial because
`x` lies outside `T` in the amalgam normal form, and `L` is torsion-free.
Eliminating `x` gives the relation `y^e U y^e = V^(-1)`, which is `W`.

Each step is an amalgam or HNN extension of torsion-free groups over infinite
cyclic subgroups. Item 2 gives embedding and torsion-freeness; item 3 gives
soficity, since `Z` is amenable and free groups are sofic. ∎

## 4. The truncation induction

Assume the top letter `a_n` is peelable; the bottom case follows by
reversing all indices. By item 4 it suffices to prove `K` sofic. By item 3,
`K` is the directed colimit of the truncations

    T_[p,q] = <a_i (i in Z) | W_p, ..., W_q>,      p <= q,

because intervals are cofinal among finite relator sets. Fix `p`. For
`j >= p-1` let `S_j` be the group presented by the generators `a_i` with
`i <= n+j` and the relators `W_p, ..., W_j`. These relators use only those
generators, so

    T_[p,j] = S_j * F(a_i : i > n+j).                                  (4.1)

Put `F_j = <a_(m+j), ..., a_(n+j-1)>` and
`B_j = <a_(m+j), ..., a_(n+j) | W_j>`. The rewritten relator `W_0` is
cyclically reduced in `F(a_m,...,a_n)`: a free cancellation `a_i a_i^(-1)`
would be an adjacent cancellation `a a^(-1)` at equal `t`-level in `w`.
It is not a proper power, since `W_0 = X^k` with `k >= 2` would make `w`
conjugate in `F` to `X^k`. So each `W_j` is cyclically reduced, involves both
`a_(m+j)` and `a_(n+j)`, and is not a proper power.

**Invariant (I_j).** `S_j` is torsion-free and sofic, and the letters
`a_(m+j+1), ..., a_(n+j)` freely generate a free subgroup of `S_j`.

*Base, `j = p-1`.* `S_(p-1)` is free on `{a_i : i <= n+p-1}`, so (I_(p-1))
holds.

*Step.* Assume (I_(j-1)). The Freiheitssatz, omitting `a_(n+j)`, embeds
`F_j` in `B_j`; (I_(j-1)) embeds `F_j` in `S_(j-1)`. The presentations give

    S_j = (S_(j-1) * <a_(n+j)>)/<<W_j>> = S_(j-1) *_(F_j) B_j,          (4.2)

a genuine amalgam, so `B_j` embeds in `S_j`. Peelability of `a_n` in `W_0` is
peelability of `y = a_(n+j)` in `W_j` over `F_j`, so Lemma 3.1 applies with
`T = S_(j-1)` and `F_0 = F_j`. It makes `S_j` torsion-free and sofic.
The Freiheitssatz in `B_j`, omitting `a_(m+j)`, shows that
`a_(m+j+1), ..., a_(n+j)` freely generate a free subgroup of `B_j`, hence of
`S_j`. That is (I_j).

By (4.1) every truncation is a free product of a sofic group with a free
group, hence sofic. The directed colimit `K` is sofic, and so is `G`. ∎

## 5. Consequence for a counterexample

**Corollary.** If a torsion-free two-generator one-relator group
`G = <a,t | w>` is not sofic, then for every free basis `(a,t)` of `F_2` in
which `t` has exponent sum zero in `w`, neither extreme letter of the
Magnus rewriting is peelable: each extreme letter forms at least three
syllables, or exactly two syllables with different absolute exponents.

This adds to the earlier necessary conditions: primitivity rank exactly two,
a nontrivial Linton radical, and nonsoficity localized in the derived core
of that radical.

## 6. Where the method stops, and why

The peeling step works because a peelable extreme letter enters its window
only through cyclic subgroups of the previous window. With three or more
syllables `y^(e_1) U_1 y^(e_2) U_2 y^(e_3) U_3 ...` the new letter is tied to
the free subgroup generated by several coefficients at once. The window step
(4.2) is still the amalgam `S_(j-1) *_(F_j) B_j`, but now `B_j` cannot be
built from `F_j` by cyclic moves. Two natural repairs fail for exact reasons.

* **Unequal two-syllable exponents.** For `y^2 U y^(-3) V`, putting `s = y^2`
  and `u = y^3` forces `y = u s^(-1)`, and substituting back produces a
  relator with four `s`-syllables. The complexity moves instead of dropping.
* **Relative Magnus rewriting.** If the `y`-exponent sum is zero, rewriting
  over the conjugates `y^(-i) T y^i` replaces the free overlap by a free
  product of copies of `T`. That edge group is nonamenable as soon as the
  overlap rank `n-m` is at least two, which is the only case not already
  covered by amenable-edge permanence.

So the unresolved core of Pestov 4.10 is the class in which every Magnus
extreme of every zero-exponent basis is unpeelable.
