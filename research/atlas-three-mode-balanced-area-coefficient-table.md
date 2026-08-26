---
rg: 2
id: atlas-three-mode-balanced-area-coefficient-table
kind: claim
title: Export the balanced-area Laurent coefficient table of the usable Atlas packet
distinct_from:
  atlas-steinberg-rank-five-translation: that proves and verifies the usable 4648-word packet and records the scripts which generate it; this asks for the much smaller moment data needed by the three-label rotation test and notes that the cited merged word JSON is not present in the repository.
  atlas-three-label-mode-two-unitary-moment-reduction: that gives the formula for one arbitrary literal word; this asks to instantiate that formula on the complete usable packet and collect the balanced Weyl coefficients.
  atlas-order-one-weyl-atlas-is-one-laurent-common-root-test: that proves how the resulting Laurent polynomials decide the order-one Weyl family; this is the missing finite input table, not the common-root decision itself.
---

**OPEN FINITE DATA TARGET.**  Let `T_St` be the established usable packet of
4,648 words.  For each `s in T_St` and integer `A`, define

```text
kappa_(s,A)=sum_({i,j : a(M_s(i,j))=b(M_s(i,j))=0,
                         Area(M_s(i,j))=A}) c_s(i,j).  (BAT1)
```

Export the finite sparse table of all nonzero `kappa_(s,A)`, with exact
rational/algebraic coefficients and the source relator name.  It gives

```text
f_s(t)=sum_A kappa_(s,A) t^A.                          (BAT2)
```

This is the **smallest missing coefficient table** for the Laurent
common-root route.  The full operator expansion in the `3^(2l)` sector words
is unnecessary after the balanced exponent and area classes have been
collected.  For a negative decision it is enough to export relators until
the gcd has no admissible unit-circle root, together with an exact Bezout/gcd
certificate; a positive decision must verify `(BAT2)` for the whole usable
packet.

### Repository audit

`atlas-steinberg-rank-five-translation-proof` cites a merged artifact named
`atlas-rank5-T_St.json`, but that file is absent from the repository.  The
literal words are reproducible rather than lost:

- `experiments/atlas_relator_rank5_full_family.py` emits the 4,612 full
  Steinberg relations;
- `experiments/atlas_relator_rank5_involutivity.py` merges the 24 new
  involutivity relations;
- `experiments/atlas_relator_rank5_reverse.py` constructs and verifies the
  twelve reverse-dictionary words, but currently has no JSON-emission option.

The apparent `4,636` versus `4,648` discrepancy is now audited exactly.  The
historical `--emit-merged atlas-rank5-T_St.json` command merges only the first
two bullets, hence `4,612 + 24 = 4,636`; all existing warm-start and flip
statistics use that probe list.  The proved usable packet additionally contains
the twelve reverse-dictionary relators, hence `4,636 + 12 = 4,648`.  An
all-reference object audit (`git rev-list --objects --all`) finds neither the
generated 4,636-word JSON, a fully merged 4,648-word JSON, nor a balanced-area
table under another tracked path or reachable commit.  The generator provenance
is exact: the full family entered at commit `0c8e3b3cf`, the involutivity merge
at `0701ceb90`, and the reverse dictionary at `0c30ee812`.

`experiments/atlas_relator_rank5_complete_packet.py` now provides the missing
deterministic serializer.  Its lightweight assembly audit finds that eight of
the twelve named reverse relations reduce freely to the empty word.  Hence the
proved presentation ledger has 4,648 entries but only 4,640 reduced nonempty
words; the four nonempty reverse relations are new.  Its ordered-list SHA-256
is `9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99`.

No checked-in artifact or script exports `(BAT1)`.  Therefore the common-root
gcd cannot presently be computed from repository data without adding the
balanced-area collector to the now-complete packet exporter.  Substituting
the six-row or fourteen-word Atlas surrogates would not decide the positive
criterion because those lists are not the complete usable packet.

The table construction is exact finite symbolic arithmetic.  It should not
materialize dense `20160 by 20160` matrices: use the sparse algebra generated
by left translations, the outer permutation `W`, and the rank-one reset
`E=|delta_1><delta_1|`, while simultaneously collecting Weyl normal-form
states `(a,b,A)`.
