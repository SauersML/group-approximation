---
rg: 2
id: strict-pairs-need-a-memory-with-five-elements-proof
kind: route
title: Enumerate every four-by-four forward table up to symmetry and separate its reverse table in finite quotients of its table group
target: strict-pairs-need-a-memory-with-five-elements
requires:
  - surjunctivity-is-axiomatized-by-rectangle-clauses
artifacts:
  - experiments/gottschalk-residual-gap-census-2026-09-17/enumtables.c
  - experiments/gottschalk-residual-gap-census-2026-09-17/gapcensus.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/pass2.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/pass3.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/merge.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/verify.py
  - experiments/gottschalk-residual-gap-census-2026-09-17/census_4x4.jsonl.gz
  - experiments/gottschalk-residual-gap-census-2026-09-17/rejected_sample_4x4.jsonl.gz
  - experiments/gottschalk-residual-gap-census-2026-09-17/RESULTS.md
---

## 0. Notation

`G` is a group, `A` a finite alphabet with `|A| >= 2`, `tau` a cellular automaton on `A^G` with memory `M`
and local rule `mu: A^M -> A`, so `(tau x)(g) = mu((x(gm))_m)`, and `sigma` one with memory `S` and rule `nu`.
The pair is *strict* when `sigma tau = id` and `tau` is not surjective. Every injective automaton has a left
inverse automaton (compactness), and an injective automaton with a left inverse `sigma` is surjective iff
`tau sigma = id`. So Gottschalk's conjecture for automata with memory sizes `(k, l)` is the statement that no
strict pair with `|S| <= k`, `|M| <= l` exists.

## 1. Reductions

**1.1 Normalization.** If `sigma tau = id` then `1` lies in `SM`: otherwise `(sigma tau x)(1)` does not read
`x(1)`. Choose `s0 m0 = 1`. With the right translation `(R_h x)(g) = x(gh)` (an automaton with memory `{h}`),
`tau' = R_(s0) tau` has memory `s0 M`, which contains `1`, and `sigma' = sigma R_(s0)^-1` has memory `S s0^-1`,
which contains `1`. Then `sigma' tau' = id` and `tau' sigma' = R_(s0) (tau sigma) R_(s0)^-1 != id`. The sizes are
unchanged. So both memories contain `1`.

**1.2 Padding.** Finite groups are surjunctive, so `G` is infinite. Adding unread addresses to `S` or `M` keeps a
strict pair strict. So it suffices to treat `|S| = |M| = 4` exactly, with `S = {1, s1, s2, s3}` and
`M = {1, m1, m2, m3}` sets of distinct elements.

**1.3 Rectangle data.** Configurations restricted to `SM` are arbitrary, so `sigma tau = id` is the identity
`nu((mu((p(s, m))_m))_s) = p(1, 1)` for every `p: S x M -> A` constant on the classes of the *forward table*
`T_f(G)`, the partition of `S x M` by the value of `sm` in `G`. Call this `Dec(T_f(G))`. Likewise
`tau sigma = id` is the identity `mu((nu((q(m, s))_s))_m) = q(1, 1)` for every `q: M x S -> A` constant on
the classes of the *reverse table* `T_r(G)`, the partition of `M x S` by `ms`. Call this `Enc(T_r(G))`.
(This is `surjunctivity-is-axiomatized-by-rectangle-clauses`.) If a partition `E` is coarser than `E'`, then
`Dec(E')` implies `Dec(E)`, and `not Enc(E)` implies `not Enc(E')`: coarser partitions admit fewer patterns.
Distinct labels make `T_f(G)` *rook independent*: no class has two cells in one row or one column.

**1.4 Table groups.** For a rook-independent partition `T` of `S x M` put

```text
P(T) = < x_a (a in S u M, a != 1), x_1 = 1 | x_s x_m = x_s' x_m'  for (s, m), (s', m') in one class of T >.
```

Here `x_(s_i)` and `x_(m_j)` are different letters even if `s_i = m_j` in `G`.

## 2. The resolution lemma

**Lemma.** Let `T` be a rook-independent partition of `S x M`. Suppose there are homomorphisms
`psi_1, ..., psi_r` from `P(T)` to finite groups such that for any two reverse cells with
`x_m x_s != x_m' x_s'` in `P(T)` some `psi_i` separates them. Then for no group `G` with `T_f(G) = T` and
no finite alphabet is there a strict pair with memories `S`, `M` realizing labels in `G`.

*Proof.* Suppose `G`, `A`, `mu`, `nu` give a strict pair with `T_f(G) = T`. The relators of `P(T)` hold for the
labels in `G`, so `phi: x_a -> a` is a homomorphism `P(T) -> G`. Hence `T_r(P(T))` is finer than `T_r(G)`, and
`not Enc(T_r(G))` gives `not Enc(T_r(P(T)))`. Let `Q` be the image of `P(T)` in `F_1 x ... x F_r` under
`(psi_i)_i`. `Q` is finite. Its labels `psi(x_a)` need not be distinct; the rectangle formulas of 1.3 hold
verbatim for label maps `S -> Q`, `M -> Q` that are not injective, because every function on the set of
products is still the restriction of a configuration. `T_f(Q)` is coarser than `T` (the relators hold), so
`Dec(T_f(Q))`. `T_r(Q) = T_r(P(T))` by the separation hypothesis (merges in `P(T)` persist in `Q`), so
`not Enc(T_r(Q))`. The automata over `Q` given by `mu`, `nu` and these labels satisfy `sigma tau = id` and
`tau sigma != id`. But `A^Q` is finite and `tau` is injective on it, hence bijective, so `sigma = tau^-1` and
`tau sigma = id`. Contradiction. QED

The alphabet and the rules never enter. This is the finite-target case of
`two-rectangle-surjunctive-images-kill-all-designs` and Lemma 3 of
`research/artifacts/canonical-table-groups-for-automaton-designs-2026-09-12.md`, applied to `P(T)` itself rather than
to a window of a fixed ambient group. No priority is claimed for the lemma. The new content is that it is applied
to *every* four-by-four table, so no ambient group is fixed.

**Unrealizable tables.** If `P(T)` derives `x_s = x_s'` (`s != s'`) or `x_m = x_m'`, or derives
`x_s x_m = x_s' x_m'` for cells in different classes of `T`, then no group with distinct labels has
`T_f(G) = T`, since `phi` would force the same equality in `G`. Such tables need no separation.

Call `T` *resolved* when the Lemma applies and *unrealizable* in the second case. A table that is neither is a
*gap table*: some pair of reverse cells is distinct in `P(T)` but merged in every finite quotient. Only gap
tables can host a counterexample of that shape.

## 3. Symmetries

The census runs over orbits of 72 symmetries.

- **Relabeling.** `Sym(S minus 1) x Sym(M minus 1)` permutes rows and columns other than the label `1`, and
  induces an isomorphism of table groups carrying reverse cells to reverse cells.
- **Inversion.** For `T` on `S x M` let `T^t` be the partition of `M x S` with `(m, s) ~ (m', s')` iff
  `(s, m) ~ (s', m')`. The map `y_a -> x_a^-1` is an isomorphism `P(T^t) -> P(T)`: it sends the relator
  `y_m y_s = y_m' y_s'` to `(x_s x_m)^-1 = (x_s' x_m')^-1`. The reverse cell `y_s y_m` of `T^t` goes to
  `(x_m x_s)^-1`. So `T^t` is resolved (unrealizable) iff `T` is. For `|S| = |M|` this is a symmetry of the
  census.

Resolved and unrealizable are properties of the isomorphism class of the pair (table group, labelled cells),
so it suffices to decide one representative per orbit.

## 4. Difference-closure prefilter

`enumtables.c` enumerates the rook-independent partitions of `4 x 4` as restricted growth strings
(17,427,192 partitions), keeps the lexicographically minimal image under the 72 symmetries (246,595 orbits),
and removes tables that are unrealizable for a reason visible in the following closure.

Nodes are the differences `D_S(a, b) = b^-1 a` (`a, b` in `S`) and `D_M(a, b) = b a^-1` (`a, b` in `M`), with
all `D(a, a) = 1`. A relator `sm = s'm'` says `D_S(s, s') = D_M(m, m')`. Two rules hold in every group:

- **R1.** `D(a, b) = D(c, d)` implies `D(b, a) = D(d, c)` (inverses).
- **R2.** `D(a, b) = D(c, d)` and `D(b, e) = D(d, f)` imply `D(a, e) = D(c, f)`, on either side, because
  `D_S(a, e) = D_S(b, e) D_S(a, b)` and `D_M(a, e) = D_M(b, e) D_M(a, b)`.

The closure (union-find until nothing changes) rejects a table when a difference `D(a, b)` with `a != b` joins
the class of `1` (a label collision), or when `D_S(s, s') = D_M(m, m')` for cells `(s, m)`, `(s', m')` in different
classes of `T`. Both rejections are consequences of the relators, so the rejected tables are unrealizable. 21,252
orbit representatives survive (167,350 collisions, 57,993 non-closed).

*Calibration.* On shape `3 x 4` the same program keeps 909 of 2,591 orbits. An independent Python enumeration
(`gapcensus.py ns nm ...`, which canonicalizes separately) resolves 837 orbits there. All 837 survive the
prefilter, so the prefilter lost no resolved table at that shape.

## 5. Deciding the surviving tables

`gapcensus.py reps 4 4 ...` treats each survivor.

1. **Derivation.** Knuth-Bendix completion for `P(T)` with a time cap. Every rewriting rule it holds is a
   consequence of the relators, so normal-form equalities are genuine equalities in `P(T)`, even when completion
   has not finished.
2. **Unrealizable.** If forward cells in different classes, or in one row or column, get equal normal forms, the
   table is unrealizable (Section 2).
3. **Reverse classes.** Reverse cells are grouped by normal form. Its merges are genuine, so this partition is finer
   than or equal to `T_r(P(T))`.
4. **Separation.** For each pair of classes, a finite permutation representation of `P(T)` separating the pair:
   - if completion finished and `P(T)` is finite, its right regular representation built from the normal forms;
   - transitive representations of degree at most 5 from low-index subgroup enumeration (Sims1);
   - in the second pass (`pass2.py`), regular representations of the finite quotients obtained by killing a subset
     of generators and imposing `g^n = 1` (`n <= 12`) on the others, when completion finishes with order at most
     5000, then Sims1 up to degree 7 with a time cap;
   - in the third pass (`pass3.py`), Tietze elimination of every generator occurring once in some relator, Sims1 up
     to degree 10 on the reduced presentation, and pullback of each representation to the original generators
     through the elimination words.
   When every pair is separated, the normal-form partition is exactly `T_r(P(T))` and the table is resolved.

## 6. Results and verification

**Counts.**

| shape | orbits | prefilter survivors | resolved | unrealizable (NOTCLOSED) | gap tables |
|---|---|---|---|---|---|
| 3x3 | 109 | 74 | 74 | 0 | 0 |
| 3x4 | 2,591 | 909 | 837 | 72 | 0 |
| 4x3 | 2,591 | 909 | 837 | 72 | 0 |
| 4x4 | 246,595 | 21,252 | 14,014 | 7,238 | 0 |

At `4x4` the resolved tables split as follows. Pass 1 resolved 13,828, of which 1,731 used a regular representation
of a finite `P(T)` (largest degree 896). Pass 2 resolved 177 of the remaining 186. Pass 3 resolved the last nine.
After Tietze elimination those nine are two-generator one-relator groups with relators of length 8, and their
separating representations have degree 8. No table stays unresolved.

**Theorem (from Sections 1-2).** By 1.1 and 1.2, a strict pair with `|S|, |M| <= 4` gives a strict pair with
`|S| = |M| = 4`, both memories containing `1`, and distinct labels. Its forward table `T = T_f(G)` is rook
independent, so some symmetry carries it to one of the 246,595 orbit representatives. If that representative
is rejected by the prefilter or classified NOTCLOSED, no group realizes `T` with distinct labels, a
contradiction. Otherwise it is resolved, and the Lemma gives a contradiction. So no such strict pair exists.

**Cross-check of the prefilter at `4x4`.** Every rejected orbit whose orbit index is divisible by 97 (2,339 tables)
was passed to pass 1 independently. Knuth-Bendix classifies all 2,339 as NOTCLOSED
(`rejected_sample_4x4.jsonl.gz`).

**Reproduction.** The commands are in `RESULTS.md`. `verify.py 4 4 census_4x4.jsonl.gz` prints
`verified 14014 failed 0`, and the same check passes for `3x3`, `3x4` and `4x3`.

**Verification tiers.**

- `verify.py` is pure Python and independent of libsemigroups. For every resolved record it checks that each
  witness is a tuple of permutations satisfying every relator of `P(T)`, and that the product of the witnesses
  splits the reverse cells into exactly the recorded classes.
- **Trusted.** Normal-form merges come from libsemigroups' Knuth-Bendix implementation (soundness of derived rules).
  The prefilter's rejections are sound by Section 4, and its implementation was calibrated on `3 x 4`.
