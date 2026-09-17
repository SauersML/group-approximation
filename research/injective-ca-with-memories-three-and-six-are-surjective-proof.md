---
rg: 2
id: injective-ca-with-memories-three-and-six-are-surjective-proof
kind: route
title: Enumerate every three-by-six forward table and decide it by Knuth-Bendix, finite quotients, or a free splitting into sofic one-relator factors
target: injective-ca-with-memories-three-and-six-are-surjective
requires:
  - strict-pairs-need-a-memory-with-five-elements
  - gap-tables-first-appear-at-three-by-six-and-four-by-five
  - sofic-groups-are-surjunctive
  - elek-szabo-sofic-permanence
  - partially-positive-one-relator-groups-are-sofic
  - peelable-extreme-one-relator-groups-are-sofic
artifacts:
  - experiments/gottschalk-three-by-six-census-2026-09-17/RESULTS.md
  - experiments/gottschalk-three-by-six-census-2026-09-17/pass1.sh
  - experiments/gottschalk-three-by-six-census-2026-09-17/soficcert.py
  - experiments/gottschalk-three-by-six-census-2026-09-17/verify_sofic.py
  - experiments/gottschalk-three-by-six-census-2026-09-17/finitewitness.py
  - experiments/gottschalk-three-by-six-census-2026-09-17/witness65499.py
  - experiments/gottschalk-three-by-six-census-2026-09-17/census_3x6.jsonl.gz
  - experiments/gottschalk-baumslag-solitar-gap-tables-2026-09-17/enumtables6.c
  - experiments/gottschalk-residual-gap-census-2026-09-17/gapcensus.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/pass2.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/pass3.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/merge.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/verify.py
---

Notation is from `strict-pairs-need-a-memory-with-five-elements-proof`, cited below as `[4x4]`: strict pairs,
forward and reverse tables `T_f`, `T_r`, the rectangle identities `Dec` and `Enc` (Section 1.3), and table groups
`P(T)` (Section 1.4).

## 1. Reduction to exact shape 3x6

By `[4x4]` Sections 1.1 and 1.2 (normalization and padding), a strict pair with `|S| <= 3` and `|M| <= 6` gives a
strict pair with `|S| = 3` and `|M| = 6` exactly. Both memories contain `1` and have distinct labels, so the forward
table `T = T_f(G)` is rook independent.

A strict pair with `|S| <= 6` and `|M| <= 3` needs the transposed shape `6x3`. By the inversion symmetry of `[4x4]`
Section 3, the map `y_a -> x_a^-1` is an isomorphism `P(T^t) -> P(T)`. It matches reverse cells up to inversion,
maps forward cells to forward cells, and preserves NOTCLOSED, RESOLVED and soficity. So a census of `3x6` decides
`6x3`, and it is enough to treat `3x6`.

## 2. A sofic table group hosts no strict pair

**Lemma.** Let `T` be a rook-independent partition of `S x M`. If `P(T)` is sofic, then no group `G` with
`T_f(G) = T` carries a strict pair with memories `S`, `M` over any alphabet.

*Proof.* Suppose `G`, `A`, `mu`, `nu` form a strict pair with `T_f(G) = T`. The labels satisfy the relators, so
`phi: x_a -> a` is a homomorphism `P(T) -> G`.

- **Forward table.** Label `P(T)` by `x_a`. Its forward table contains every coincidence of `T`, since the relators
  hold. It contains no others, since `phi` would carry them to `G`. So `T_f(P(T)) = T`, and `Dec(T)` holds.
- **Reverse table.** `phi` can only merge reverse cells, so `T_r(P(T))` is finer than `T_r(G)`. Coarsening a
  partition keeps `Enc` true, so `not Enc(T_r(G))` gives `not Enc(T_r(P(T)))`.

The rectangle identities of `[4x4]` 1.3 hold for label maps that need not be injective. So the automata over `P(T)`
with rules `mu`, `nu` and labels `x_a` satisfy `sigma tau = id` and `tau sigma != id`. Then `tau` is injective and not
surjective on `A^P(T)`. This contradicts `sofic-groups-are-surjunctive`. QED

It is the argument of the resolution lemma of `[4x4]` Section 2, with `P(T)` itself in place of a finite quotient.
The pullback to a table group is that of `strict-automata-live-on-canonical-table-groups`.

## 3. The three verdicts

Every surviving table gets one verdict.

**NOTCLOSED.** Knuth-Bendix rules are consequences of the relators. If they derive `x_s x_m = x_s' x_m'` for cells in
different classes, or in one row or column, then `T` is realized by no group with distinct labels (`[4x4]` Section 2).

**RESOLVED.** Finite permutation representations of `P(T)` separate every pair of reverse classes. Each class is
derived by Knuth-Bendix, so it is genuine. The resolution lemma applies.

**SOFIC.** `soficcert.py` certifies `P(T)` as sofic in four steps:

1. **Tietze elimination.** A relator in which a generator `g` occurs exactly once is solved for `g`. The solution is
   substituted everywhere, and the relator is dropped. This gives an isomorphic presentation. Every move is logged.
2. **Free splitting.** Group the remaining generators by the relation "occur together in a relator". The reduced
   presentation is the free product of the component presentations and the free group on the unused generators.
3. **Factor certificates.** Each component must be one of these:
   - a single generator, so the factor is cyclic;
   - one relator with a generator of one sign only, which is sofic by
     `partially-positive-one-relator-groups-are-sofic`;
   - one relator `w` on two generators, not a proper power, with a peelable extreme letter.
4. **Assembly.** Free products of sofic groups are sofic (`elek-szabo-sofic-permanence`, Theorem 1.2). So `P(T)` is
   sofic, and the Lemma applies.

In the peelable case, a Nielsen transformation (`b -> b a^k` or `a -> a b^k`, repeated as in the Euclidean
algorithm) gives a word `w'` in which a generator `t` has exponent sum zero. It changes neither the group nor the
proper-power property. The Magnus rewriting of `w'` over `a_i = t^-i a t^i` must then have its top or bottom letter
in one syllable, or in two syllables of equal absolute exponent. The group is then sofic by
`peelable-extreme-one-relator-groups-are-sofic`.

The height of an `a`-letter of `w'` is the `t`-exponent sum of the prefix before it, and that is the Magnus index of
the letter. So the syllables of the extreme letter are the maximal cyclic runs of `a`-letters at the extreme height,
with `t`-letters skipped. The run exponent is the signed count. `verify_sofic.py` rechecks exactly this.

## 4. The pipeline

1. **Enumeration.** `enumtables6 3 6 prune` enumerates 201,106,530 rook-independent partitions of `3 x 6`, up to
   `Sym(S minus 1) x Sym(M minus 1)` (240 symmetries). The difference closure removes 635,604 orbits with a label
   collision and 104,751 non-closed orbits, leaving 68,844 survivors.
   - The closure is sound on partial tables. It is calibrated against the published survivor lists at `3x3`, `3x4`,
     `4x3` and `4x4` (`gap-tables-first-appear-at-three-by-six-and-four-by-five-proof`, Section 2).
2. **Pass 1.** `gapcensus.py reps 3 6` (Knuth-Bendix 200 ms, Sims1 up to degree 5, regular representation when
   finite), in chunks of 4000.
3. **Sofic certificates.** `soficcert.py` on the pass-1 CANDIDATEs.
4. **Pass 2.** `pass2.py` (7 2000 20) on the rest.
5. **Finite witnesses.** `finitewitness.py` on the rest. It asks GAP for `P(T)/<<g^n>>` on the reduced presentation,
   for each remaining generator `g` and `n <= 30`. It skips quotients with infinite abelianization, bounds coset
   enumeration, and keeps quotients of order at most 20000. It pulls a small-degree permutation representation back
   to the original generators through the Tietze substitution words.
6. **Pass 3.** `pass3.py` (Tietze, Sims1 up to degree 10) on anything left.

7. **The last table.** Survivor 65499 is left CANDIDATE by every automatic stage. After Tietze moves, its table
   group is `<x2, x3, x7 | u x2 u x2 u, u x2^-1 u^-1 x2^-2>` with `u = x7 x3^-1`. The Nielsen change `x7 -> u x3` shows
   that it is `Z * Z/9` with `x2 = u^3`. `witness65499.py` sends `u` to a 9-cycle and `x3` to a random permutation of
   degree 12. The first trial separates all 18 reverse cells.

| stage | decided | CANDIDATE left |
|---|---|---|
| pass 1 | 54,334 RESOLVED, 13,231 NOTCLOSED | 1,279 |
| soficity certificates | 891 SOFIC | 388 |
| pass 2 | 360 RESOLVED | 28 |
| finite quotients and pass 3 | 9 + 18 RESOLVED | 1 |
| survivor 65499 | 1 RESOLVED | 0 |

The final census has 13,231 NOTCLOSED, 54,722 RESOLVED and 891 SOFIC records, 68,844 in all. In chunks 0-9, pass 3
ran before the finite-quotient stage. The per-chunk counts are in `RESULTS.md`.

## 5. Verification

- **Separation witnesses.** `verify.py 3 6 census_3x6.jsonl.gz` prints `verified 54722 failed 0`. This is
  the unchanged independent checker of `[4x4]`. It checks that each witness satisfies every relator of `P(T)` and
  that the witnesses split the reverse cells into exactly the recorded classes.
- **Soficity certificates.** `verify_sofic.py 3 6 census_3x6.jsonl.gz` prints `verified 891 failed 0`. It is
  pure Python and imports nothing from the census code. For each record it:
  - rebuilds the relators from the pass-1 relations of the record;
  - replays every logged Tietze move, requiring the named generator to occur exactly once in the named relator, and
    compares the final relators and substitution words;
  - recomputes the free splitting and the free generators;
  - rechecks each factor certificate, re-deriving the Nielsen word and the peel test.
- **Trusted.**
  - Knuth-Bendix soundness (libsemigroups), for NOTCLOSED verdicts and reverse classes.
  - The difference closure, as in `[4x4]`.
  - The written proofs of the two one-relator soficity theorems and of Elek-Szabo permanence.
- **Not trusted.** GAP's coset enumeration and `IsomorphismPermGroup` are not trusted. Their output is only a
  candidate witness that `verify.py` replays.

## 6. Conclusion

A strict pair of shape `3x6` has a rook-independent forward table `T`, and some relabeling carries `T` to a
survivor. Relabeling preserves all three verdicts.

- A NOTCLOSED survivor is not realized.
- A RESOLVED survivor hosts no strict pair by `[4x4]` Section 2.
- A SOFIC survivor hosts no strict pair by Section 2.

Tables rejected by the closure are not realized. So no strict pair of shape `3x6` exists. By Section 1, none of
shape at most `3x6` or at most `6x3` exists either.
