---
rg: 2
id: injective-ca-with-memories-three-and-six-are-surjective
kind: claim
title: Over every group and alphabet, an injective automaton whose memory and left-inverse memory have at most three and at most six elements is surjective, past the first gap shape
distinct_from:
  gap-tables-first-appear-at-three-by-six-and-four-by-five: that proves the finite-quotient census stops at three by five because three by six carries gap tables; this decides every three-by-six table anyway, by adding soficity certificates of the table group, so the Gottschalk case moves from memory sizes three and five to three and six.
  strict-pairs-need-a-memory-with-five-elements: that decides every table up to four by four by finite quotients alone; this reaches shape three by six, where finite quotients provably fail, and decides the gap tables there through one-relator soficity theorems.
  three-point-decoder-memory-injective-ca-are-surjective: that open claim allows any encoder memory; this proves the case of an encoder memory with at most six points, and also the transposed case of a three-point encoder memory with a decoder memory of at most six points.
  nonsofic-one-relator-group: that asks for a one-relator group that is not sofic, which a strict pair over a one-relator table core would supply; this shows that no three-by-six table supplies one, since every one-relator core met at that shape is partially positive or has a peelable extreme letter.
  strict-automata-live-on-canonical-table-groups: that pulls a strict pair back to the table group of a minimal forward-sufficient partition; this uses the pullback to the table group of the full forward table and certifies all 68,844 of them at one shape, by a finite quotient or by soficity.
artifacts:
  - experiments/gottschalk-three-by-six-census-2026-09-17/RESULTS.md
  - experiments/gottschalk-three-by-six-census-2026-09-17/pass1.sh
  - experiments/gottschalk-three-by-six-census-2026-09-17/soficcert.py
  - experiments/gottschalk-three-by-six-census-2026-09-17/verify_sofic.py
  - experiments/gottschalk-three-by-six-census-2026-09-17/finitewitness.py
  - experiments/gottschalk-three-by-six-census-2026-09-17/witness65499.py
  - experiments/gottschalk-three-by-six-census-2026-09-17/census_3x6.jsonl.gz
---

**ESTABLISHED** by `injective-ca-with-memories-three-and-six-are-surjective-proof`. It is
computer-assisted: every separation witness and every soficity certificate is replayed by an independent
pure-Python checker, and the soficity certificates rest on written (not Lean-checked) one-relator theorems.

**Theorem.** Let `G` be any group, `A` any finite alphabet, and `tau`, `sigma` cellular automata on `A^G` with
memories `M` and `S` such that `sigma tau = id`. If `|S| <= 3` and `|M| <= 6`, or `|S| <= 6` and `|M| <= 3`, then
`tau` is surjective.

Before this, the best bound of this form was `3` and `5`
(`gap-tables-first-appear-at-three-by-six-and-four-by-five`). The shape `3x6` is a minimal gap shape: it carries
tables whose table group is `BS(2,3)`, where no finite quotient separates the reverse cells. So the finite-quotient
census method provably cannot give this theorem.

**How every `3x6` table is decided.** The enumeration of `gap-tables-first-appear-at-three-by-six-and-four-by-five`
leaves 68,844 rook-independent tables up to relabeling. Each one ends in one of three states.

| state | tables | meaning |
|---|---|---|
| NOTCLOSED | 13,231 | Knuth-Bendix derives a forward coincidence outside `T`, so no group realizes `T` |
| RESOLVED | 54,722 | finite permutation quotients of `P(T)` separate every distinct reverse pair |
| SOFIC | 891 | after logged Tietze moves, `P(T)` is a free group of rank at most 2, free product with either a cyclic group or a two-generator one-relator group that is partially positive or has a peelable extreme letter |

No CANDIDATE remains. In the SOFIC case, a strict pair with forward table `T` gives a strict pair over `P(T)`
itself. That is impossible, since sofic groups are surjunctive.

**The certificate mix.** Of the 891 SOFIC tables, 359 have a cyclic factor, 274 a partially-positive one-relator factor and 258 a
peelable-extreme one-relator factor. 87 of the factors are Baumslag-Solitar relators `t b^p t^-1 b^q`. In 31 of them,
`{|p|,|q|} = {2,3}`, so the group is not residually finite.

The 1,279 tables left CANDIDATE after pass 1 were decided as follows:

- 891 by soficity;
- 360 by pass 2 (Sims1 up to degree 7);
- 9 by finite quotients `P(T)/<<g^n>>`;
- 18 by pass 3 (Sims1 up to degree 10);
- 1 (survivor 65499, `P(T) = Z * Z/9`) by a degree-12 witness.

`verify.py` prints `verified 54722 failed 0` and `verify_sofic.py` prints `verified 891 failed 0`.

**What stays open.**

- *Shape `4x5`.* This is the other minimal gap shape, and its closure census is much larger. The same three-state
  pipeline applies unchanged.
- *How many `3x6` tables are gap tables.* Soficity is tried before the deeper finite-quotient passes, so this census
  does not count the gap tables. It shows only that each one has a sofic table group. The 31 SOFIC tables with a
  `BS(2,±3)` factor are the natural candidates.
- *Non-sofic table groups at `3xN`.* For the bounded cases of `three-point-decoder-memory-injective-ca-are-surjective`,
  one must find the first `N` where a `3xN` table group escapes every soficity certificate. At `N = 6` none does.
