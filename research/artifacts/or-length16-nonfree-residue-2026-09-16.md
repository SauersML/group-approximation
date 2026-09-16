# Length-16 unpeelable residue: collapse certificates for virtual fibring (2026-09-16)

Lane: swarm-one-relator-groups-sofic. Hole worked: `unpeelable-extreme-one-relator-groups-sofic`.

This artifact supports the following nodes:
- `non-proper-power-one-relator-complexes-are-aspherical`, with its citation route (literature check, §6);
- `virtual-fibring-collapse-certificate-gives-rf-sofic`, with `virtual-fibring-collapse-certificate-proof`;
- `length16-residue-classes-virtually-free-by-cyclic`, with `length16-residue-virtual-fibring-certificates`.

The proofs are in the route nodes. This file holds:
- the word lists;
- the search ranges;
- the negative results and unlanded side computations;
- the commands to reproduce everything.

All paths below are repository-relative.

- `E = experiments/or-length16-nonfree-residue-2026-09-16`
- `A = research/artifacts/one-relator-linton-graph-certificates-scripts`
- `S = research/artifacts/or-length15-residue-scripts`
- `C = research/artifacts/or-unpeelable-census-scripts-2026-09-12`

## 0. Outcome

Of the 211 length-16 unpeelable residue classes (`REST` lines of `A/census3_16.out`), 172 have a
collapse certificate. `verify.py` and the independently written `recheck.py` both accept each one.
So each of these 172 groups `<a, t | w>` has a finite-index subgroup `F_n ⋊ Z` and is residually
finite and sofic.

The 172 include all 107 classes that no Linton graph certificate covers: neither the landed
letter-once version nor this lane's primitive-piece transport (§4) applies to them.

The other 39 classes have no collapse certificate in the searched range (§3). Each of them has a
Linton graph certificate: 37 through the landed node
`length15-16-free-piece-residue-classes-hyperbolic-special` and 2 through the unlanded transport of
§4.

So every one of the 211 length-16 residue classes carries at least one certificate. Only the 172 are
landed as sofic. The claim `unpeelable-extreme-one-relator-groups-sofic` covers all lengths, so it
stays open.

## 1. Inputs and the split

- `A/census3_16.out` (md5 `26b721a1e47eedcbb971190afbe59991`): 211 `REST` lines, the survivors of
  `census3.py 16 16` after the partial-positivity search. The header line records 230 survivors
  and 211 remaining.
- `A/lg_words16.out` (md5 `fe7ff51a0210708897c7477843659780`): 70 words ending `-> PASS`, landed as
  hyperbolic and virtually special, and 141 `NONFREE` words.
- `E/pieces.out` and `E/primcert.out` split the 141 `NONFREE` words by the Whitehead algorithm on the
  Magnus piece `W_0` (every one has 3 levels and level gcd 1):
  - 105 have a non-primitive piece (`NONPRIM`);
  - 36 have a primitive piece. On these, the transported Linton certificate gives 34 `PASS`, one
    `FAIL(alternating cycle)` (`TTAATaTAATTatAta`) and one `PASS_HLOOP` (`TTAATaTAATaTAtta`).
- The **open** words are the 105 `NONPRIM` words together with these 2, which makes 107.

`E/accounting.py` asserts every count in this section, and its output is `E/accounting.out`.

## 2. The 172 certified words

A certificate is a `CERT` line of `S/vfib.py`:

    CERT w k=K a=[...] t=[...] c=[...] pot=[...] cp=[...] delta=[...]

- `a` and `t` list the images `α(i)` and `τ(i)` for `i = 0, …, k−1`.
- `cp` is the certificate cocycle: first the `a`-edges `0, …, k−1`, then the `t`-edges.
- `c` and `pot` record how `vfib.py` found `cp`, as `cp = c + δ(pot)`.
- `delta` is the Alexander polynomial.

`recheck.py` reads only `w`, `a`, `t` and `cp`, and checks (V0)–(V3) of
`virtual-fibring-collapse-certificate-gives-rf-sofic`. In the tables, `k` is the index, `S` the
window span and `n = 1 − χ(X[0,S])` the fibre rank. `verify.py` and `recheck.py` agree on all three
values, line by line (asserted by `accounting.py`).

Index distribution:

| Class | Index 2 | Index 3 | Index 4 | Index 5 | Index 6 | Index 7 | Index 8 | Total |
|---|---|---|---|---|---|---|---|---|
| Open | 102 | – | 3 | 1 | 1 | – | – | 107 |
| Transported `PASS` | 30 | 1 | – | – | 1 | – | – | 32 of 34 |
| Landed `PASS` | 8 | 4 | 4 | 4 | 10 | 1 | 2 | 33 of 70 |

Over all 172 certified words, the fibre rank `n` ranges from 3 to 79. The largest is
`TTTATAttaaTAAtaa`, with `k = 6`, `S = 29` and `n = 79`. Among the open words the largest is
`TTATaattAAttaatA`, with `k = 4`, `S = 18` and `n = 44`.

### 2.1 The 107 open words

| # | relator `w` | class | `k` | `S` | `n` | certificate file |
|---|---|---|---|---|---|---|
| 1 | `TTAATaTAATTatAta` | open (primitive piece, FAIL(alternating_cycle)) | 2 | 3 | 4 | `vf4.out` |
| 2 | `TTAATaTAATaTAtta` | open (primitive piece, PASS_HLOOP) | 2 | 6 | 7 | `vf4.out` |
| 3 | `TTAATTaaTAATatta` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 4 | `TTAATTaaTATAtata` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 5 | `TTAATTaaTAtATata` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 6 | `TTAATTaaTAtAtata` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 7 | `TTAATTaaTAttATaa` | open (non-primitive piece) | 4 | 5 | 11 | `vf4.out` |
| 8 | `TTAATTaatAATatta` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 9 | `TTAATTaatATTAtaa` | open (non-primitive piece) | 2 | 10 | 14 | `vf4.out` |
| 10 | `TTAATTaatAtATata` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 11 | `TTAATTatATaaTAta` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 12 | `TTAATTatATaatAta` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 13 | `TTAATaTAttaaTAta` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 14 | `TTAATaTaTATAttaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 15 | `TTAATaTatAATTata` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 16 | `TTAATaTatATAttaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 17 | `TTAATaaTAATTatta` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 18 | `TTAATaaTAtATTata` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 19 | `TTAATaatAATTatta` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 20 | `TTAATaatATTAttaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 21 | `TTAATaatAtATTata` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 22 | `TTAATatATTaaTAta` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 23 | `TTAATatATTaatAta` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 24 | `TTAAtaTAttATAtaa` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 25 | `TTAAtaTaTATAttaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 26 | `TTAAtaTatAATTata` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 27 | `TTAAtaaTAtATTata` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 28 | `TTAAtatATATAttaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 29 | `TTAAtatATTAtAtaa` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 30 | `TTATATTaTaTAAtaa` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 31 | `TTATATTaTatAATaa` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 32 | `TTATATTaTatAAtaa` | open (non-primitive piece) | 2 | 4 | 5 | `vf4.out` |
| 33 | `TTATATTaaTAtAtaa` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 34 | `TTATATTaatAATata` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 35 | `TTATATTaatATAtaa` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 36 | `TTATATTaatAtAtaa` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 37 | `TTATATaTaTAAttaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 38 | `TTATATaTatAATTaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 39 | `TTATATaTatAAttaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 40 | `TTATATaaTAAttaTa` | open (non-primitive piece) | 2 | 4 | 5 | `vf4.out` |
| 41 | `TTATATaaTAtAttaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 42 | `TTATATaatAATTata` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 43 | `TTATATaatAAttaTa` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 44 | `TTATATaatATAttaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 45 | `TTATATaatAtATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 46 | `TTATATataTAAttaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 47 | `TTATAtaTaTAATTaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 48 | `TTATAtaTaTAAttaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 49 | `TTATAtaTatAATTaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 50 | `TTATAtaaTAAttaTa` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 51 | `TTATAtaaTAtATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 52 | `TTATAtaatAAttata` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 53 | `TTATAtaatATATTaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 54 | `TTATAtaatAtATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 55 | `TTATAtataTAATTaa` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |
| 56 | `TTATAttaTaTAATaa` | open (non-primitive piece) | 2 | 5 | 7 | `vf4.out` |
| 57 | `TTATAttaTaTAAtaa` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 58 | `TTATAttaTatAATaa` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 59 | `TTATAttaaTAtATaa` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 60 | `TTATAttaatAAtata` | open (non-primitive piece) | 2 | 3 | 5 | `vf4.out` |
| 61 | `TTATAttaatATATaa` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 62 | `TTATAttaatAtAtaa` | open (non-primitive piece) | 2 | 2 | 4 | `vf4.out` |
| 63 | `TTATTATTaaTAAtaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 64 | `TTATTATTaatAAtaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 65 | `TTATTATaaTAAttaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 66 | `TTATTATaatAATTaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 67 | `TTATTATaatAAttaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 68 | `TTATTAtaaTAATTaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 69 | `TTATTAtaaTAAttaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 70 | `TTATTAtaatAATTaa` | open (non-primitive piece) | 2 | 5 | 7 | `vf4.out` |
| 71 | `TTATTAttaaTAATaa` | open (non-primitive piece) | 2 | 5 | 7 | `vf4.out` |
| 72 | `TTATTAttaaTAAtaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 73 | `TTATTAttaatAATaa` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 74 | `TTATaTAATTaTAtaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 75 | `TTATaTAATTatATaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 76 | `TTATaTAATTatAtaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 77 | `TTATaTAATaTAttaa` | open (non-primitive piece) | 2 | 4 | 5 | `vf4.out` |
| 78 | `TTATaTAATatATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 79 | `TTATaTAATatAttaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 80 | `TTATaTAAtaTATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 81 | `TTATaTAAtaTAttaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 82 | `TTATaTAAtatATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 83 | `TTATaTAAttaTATaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 84 | `TTATaTAAttaTAtaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 85 | `TTATaTAAttatATaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 86 | `TTATaaTAATTaattA` | open (non-primitive piece) | 2 | 5 | 7 | `vf4.out` |
| 87 | `TTATaaTTAATTaatA` | open (non-primitive piece) | 6 | 5 | 17 | `vfrest.out` |
| 88 | `TTATaaTTAAttaaTA` | open (non-primitive piece) | 2 | 4 | 5 | `vf4.out` |
| 89 | `TTATaaTTAAttaatA` | open (non-primitive piece) | 4 | 6 | 13 | `vf4.out` |
| 90 | `TTATaatAATTaattA` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 91 | `TTATaatAAttaattA` | open (non-primitive piece) | 2 | 2 | 3 | `vf4.out` |
| 92 | `TTATaattAATTaatA` | open (non-primitive piece) | 5 | 4 | 10 | `vfrest.out` |
| 93 | `TTATaattAAttaatA` | open (non-primitive piece) | 4 | 18 | 44 | `vf4.out` |
| 94 | `TTATatAATTaTAtaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 95 | `TTATatAATTatATaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 96 | `TTATatAATTatAtaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 97 | `TTATatAATaTAttaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 98 | `TTATatAATatATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 99 | `TTATatAAtaTATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 100 | `TTATatAAtatATTaa` | open (non-primitive piece) | 2 | 8 | 12 | `vf4.out` |
| 101 | `TTATatAAttaTATaa` | open (non-primitive piece) | 2 | 6 | 6 | `vf4.out` |
| 102 | `TTTAAtataaTATAtA` | open (non-primitive piece) | 2 | 4 | 5 | `vf4.out` |
| 103 | `TTTATAAtaTatAATA` | open (non-primitive piece) | 2 | 3 | 4 | `vf4.out` |
| 104 | `TTTATAAtaaTAtATA` | open (non-primitive piece) | 2 | 4 | 5 | `vf4.out` |
| 105 | `TTTATAAtataTatAA` | open (non-primitive piece) | 2 | 3 | 4 | `vf4.out` |
| 106 | `TTTATAAtataaTAtA` | open (non-primitive piece) | 2 | 4 | 5 | `vf4.out` |
| 107 | `TTTATAtATATaatAA` | open (non-primitive piece) | 2 | 6 | 7 | `vf4.out` |

### 2.2 The 32 certified transported-`PASS` words

| # | relator `w` | class | `k` | `S` | `n` | certificate file |
|---|---|---|---|---|---|---|
| 1 | `TTTATAAATTatAATA` | transported PASS | 2 | 3 | 4 | `vf34.out` |
| 2 | `TTTATAAATATaattA` | transported PASS | 2 | 4 | 5 | `vf34.out` |
| 3 | `TTTATAAtaaatAATA` | transported PASS | 3 | 6 | 8 | `vf34.out` |
| 4 | `TTTATAAtaaattATA` | transported PASS | 2 | 4 | 5 | `vf34.out` |
| 5 | `TTTATAAtataTTAAA` | transported PASS | 2 | 6 | 9 | `vf34.out` |
| 6 | `TTTATAttataaTAAA` | transported PASS | 2 | 4 | 5 | `vf34.out` |
| 7 | `TTATATTaaTATAtaa` | transported PASS | 2 | 2 | 4 | `vf34.out` |
| 8 | `TTATATTaaTAAtata` | transported PASS | 2 | 3 | 5 | `vf34.out` |
| 9 | `TTATATTaatAAtata` | transported PASS | 2 | 3 | 5 | `vf34.out` |
| 10 | `TTATATaaTATAttaa` | transported PASS | 2 | 4 | 5 | `vf34.out` |
| 11 | `TTATATaaTAAttata` | transported PASS | 2 | 3 | 5 | `vf34.out` |
| 12 | `TTATATaatATATTaa` | transported PASS | 2 | 8 | 12 | `vf34.out` |
| 13 | `TTATATatatAATTaa` | transported PASS | 2 | 6 | 7 | `vf34.out` |
| 14 | `TTATAAtaTTAAtata` | transported PASS | 2 | 3 | 4 | `vf34.out` |
| 15 | `TTATAAtaaTAAtata` | transported PASS | 6 | 3 | 9 | `vf34.out` |
| 16 | `TTATAtATATaTAAta` | transported PASS | 2 | 4 | 5 | `vf34.out` |
| 17 | `TTATAtATATaatAta` | transported PASS | 2 | 6 | 7 | `vf34.out` |
| 18 | `TTATAtATaTAAtata` | transported PASS | 2 | 6 | 7 | `vf34.out` |
| 19 | `TTATAtaaTATAttaa` | transported PASS | 2 | 8 | 12 | `vf34.out` |
| 20 | `TTATAtaaTAATTata` | transported PASS | 2 | 3 | 5 | `vf34.out` |
| 21 | `TTATAtaatAATTata` | transported PASS | 2 | 3 | 5 | `vf34.out` |
| 22 | `TTATAtatatAATTaa` | transported PASS | 2 | 6 | 7 | `vf34.out` |
| 23 | `TTATAtatatAAttaa` | transported PASS | 2 | 6 | 7 | `vf34.out` |
| 24 | `TTATAttaaTATATaa` | transported PASS | 2 | 2 | 4 | `vf34.out` |
| 25 | `TTATAttaaTATAtaa` | transported PASS | 2 | 2 | 4 | `vf34.out` |
| 26 | `TTATAttaaTAATata` | transported PASS | 2 | 3 | 5 | `vf34.out` |
| 27 | `TTAATTaatATATata` | transported PASS | 2 | 6 | 7 | `vf34.out` |
| 28 | `TTAATTaatATAtata` | transported PASS | 2 | 6 | 7 | `vf34.out` |
| 29 | `TTAATTataTAAtata` | transported PASS | 2 | 8 | 12 | `vf34.out` |
| 30 | `TTAATataTATAttaa` | transported PASS | 2 | 6 | 7 | `vf34.out` |
| 31 | `TTAATatatAATTata` | transported PASS | 2 | 2 | 4 | `vf34.out` |
| 32 | `TTAAtaTatatAtata` | transported PASS | 2 | 3 | 4 | `vf34.out` |

### 2.3 The 33 certified landed-`PASS` words

| # | relator `w` | class | `k` | `S` | `n` | certificate file |
|---|---|---|---|---|---|---|
| 1 | `TTTATATTaaTAAtaa` | landed PASS | 5 | 5 | 12 | `vf70.out` |
| 2 | `TTTATATTaatAATaa` | landed PASS | 6 | 4 | 11 | `vf70.out` |
| 3 | `TTTATATTaatAAtaa` | landed PASS | 4 | 8 | 20 | `vf70.out` |
| 4 | `TTTATAAATTattATA` | landed PASS | 6 | 12 | 31 | `vf70.out` |
| 5 | `TTTATAAATATTattA` | landed PASS | 5 | 20 | 50 | `vf70.out` |
| 6 | `TTTATAAtaTattATA` | landed PASS | 3 | 6 | 9 | `vf70.out` |
| 7 | `TTTATAAtataTTAtA` | landed PASS | 6 | 11 | 35 | `vf70.out` |
| 8 | `TTTATAtATaattATA` | landed PASS | 6 | 5 | 13 | `vf70.out` |
| 9 | `TTTATAtaaTAAttaa` | landed PASS | 2 | 4 | 5 | `vf70.out` |
| 10 | `TTTATAttaaTAAtaa` | landed PASS | 6 | 29 | 79 | `vf70.out` |
| 11 | `TTTATAttaaattATA` | landed PASS | 3 | 10 | 14 | `vf70.out` |
| 12 | `TTTATAttaatAATaa` | landed PASS | 2 | 5 | 7 | `vf70.out` |
| 13 | `TTTAATTaTaTAAtaa` | landed PASS | 6 | 8 | 22 | `vf70.out` |
| 14 | `TTTAATTaTatAATaa` | landed PASS | 6 | 5 | 15 | `vf70.out` |
| 15 | `TTTAATTaTatAAtaa` | landed PASS | 8 | 7 | 31 | `vf41k8.out` |
| 16 | `TTTAATTaaTATAtaa` | landed PASS | 4 | 11 | 20 | `vf70.out` |
| 17 | `TTTAATTaaTAtAtaa` | landed PASS | 6 | 5 | 15 | `vf70.out` |
| 18 | `TTTAATTataTAAtaa` | landed PASS | 4 | 8 | 17 | `vf70.out` |
| 19 | `TTTAATTatatAATaa` | landed PASS | 6 | 4 | 15 | `vf70.out` |
| 20 | `TTTAATaTatAAttaa` | landed PASS | 2 | 5 | 7 | `vf70.out` |
| 21 | `TTTAATaatATAttaa` | landed PASS | 2 | 10 | 14 | `vf70.out` |
| 22 | `TTTAAtaTaTAAttaa` | landed PASS | 2 | 8 | 10 | `vf70.out` |
| 23 | `TTTAAtaatAATTata` | landed PASS | 7 | 7 | 25 | `vf42k7.out` |
| 24 | `TTTAAtaatAAttata` | landed PASS | 2 | 5 | 7 | `vf70.out` |
| 25 | `TTTAAtaatAtAttaa` | landed PASS | 2 | 8 | 10 | `vf70.out` |
| 26 | `TTTAAtataTTATAtA` | landed PASS | 4 | 8 | 17 | `vf70.out` |
| 27 | `TTTAAtataTatattA` | landed PASS | 3 | 9 | 14 | `vf70.out` |
| 28 | `TTTAAtatatAAttaa` | landed PASS | 5 | 10 | 24 | `vf70.out` |
| 29 | `TTTAAttaatAAtata` | landed PASS | 2 | 5 | 7 | `vf70.out` |
| 30 | `TTTAtATATaatattA` | landed PASS | 6 | 6 | 19 | `vf70.out` |
| 31 | `TTATAtATATTatAta` | landed PASS | 3 | 8 | 13 | `vf70.out` |
| 32 | `TTATAtATATaTAtta` | landed PASS | 8 | 3 | 11 | `vf41k8.out` |
| 33 | `TTAtATTatatAtata` | landed PASS | 5 | 5 | 11 | `vf70.out` |


## 3. The 39 words without a collapse certificate

Search parameters: `vfib.py WORD KMAX 1 2 KMIN`. For each index, the search:
- goes over all transitive representations up to conjugacy;
- tries characters with coefficients `|λ_i| ≤ 2` in a basis of `H^1(X_H; Z)`;
- applies the unit-end Alexander filter;
- tries potentials in `[−1, 1]^{k−1}`;
- runs a greedy collapse.

"Searched" means `vfib.py` finished that index without finding a `CERT`.
- Indices 1–6 were covered by `E/vf34.out` and `E/vf70.out`, where no word timed out.
- Index 7 was covered by `E/vf42k7.out`, on all 42 words then uncertified; no word timed out, and
  `TTTAAtaatAATTata` was certified.
- Index 8 was covered by `E/vf41k8.out`, on the remaining 41 words, with 13 s per word. Two words
  were certified, six timed out and the other 33 finished without a certificate.

A search that does not find a certificate is not evidence that the group does not virtually fibre.
The character and potential bounds and the greedy collapse can all miss certificates.


| # | relator `w` | class | searched (index, all complete unless noted) |
|---|---|---|---|
| 1 | `TTTATAAtataaTAAA` | transported PASS | 1–8 |
| 2 | `TTTATAAtataaatAA` | transported PASS | 1–8 |
| 3 | `TTTATATaaTAAttaa` | landed PASS | 1–7; index 8 timed out after 13 s |
| 4 | `TTTATATaatAATTaa` | landed PASS | 1–7; index 8 timed out after 13 s |
| 5 | `TTTATATaatAAttaa` | landed PASS | 1–7; index 8 timed out after 13 s |
| 6 | `TTTATAAtaTTAtATA` | landed PASS | 1–8 |
| 7 | `TTTATAAtataTattA` | landed PASS | 1–8 |
| 8 | `TTTATAtATATTatAA` | landed PASS | 1–8 |
| 9 | `TTTATAtATATaattA` | landed PASS | 1–8 |
| 10 | `TTTATAtaaTAATTaa` | landed PASS | 1–8 |
| 11 | `TTTATAtaatAATTaa` | landed PASS | 1–8 |
| 12 | `TTTATAttaaTAATaa` | landed PASS | 1–8 |
| 13 | `TTTATAttataTTAAA` | landed PASS | 1–8 |
| 14 | `TTTATAttataTatAA` | landed PASS | 1–8 |
| 15 | `TTTATAttataaTAtA` | landed PASS | 1–8 |
| 16 | `TTTAATTaaTAAtata` | landed PASS | 1–8 |
| 17 | `TTTAATTaatATATaa` | landed PASS | 1–8 |
| 18 | `TTTAATTaatATAtaa` | landed PASS | 1–8 |
| 19 | `TTTAATTaatAATata` | landed PASS | 1–7; index 8 timed out after 13 s |
| 20 | `TTTAATTaatAAtata` | landed PASS | 1–8 |
| 21 | `TTTAATTaatAtATaa` | landed PASS | 1–8 |
| 22 | `TTTAATTaatAtAtaa` | landed PASS | 1–8 |
| 23 | `TTTAATTatatAAtaa` | landed PASS | 1–8 |
| 24 | `TTTAATaTaTAAttaa` | landed PASS | 1–8 |
| 25 | `TTTAATaaTATAttaa` | landed PASS | 1–7; index 8 timed out after 13 s |
| 26 | `TTTAATaaTAAttata` | landed PASS | 1–8 |
| 27 | `TTTAATaaTAtAttaa` | landed PASS | 1–8 |
| 28 | `TTTAATaatAATTata` | landed PASS | 1–8 |
| 29 | `TTTAATataTAAttaa` | landed PASS | 1–8 |
| 30 | `TTTAAtaaTATAttaa` | landed PASS | 1–8 |
| 31 | `TTTAAtaaTAATTata` | landed PASS | 1–7; index 8 timed out after 13 s |
| 32 | `TTTAAttaaTAATata` | landed PASS | 1–8 |
| 33 | `TTATAAtaTTAttata` | landed PASS | 1–8 |
| 34 | `TTATAtATTatAtata` | landed PASS | 1–8 |
| 35 | `TTATAtATaTAttata` | landed PASS | 1–8 |
| 36 | `TTATAttaTTAAtata` | landed PASS | 1–8 |
| 37 | `TTATAttaTatAtata` | landed PASS | 1–8 |
| 38 | `TTATAttaaTAttata` | landed PASS | 1–8 |
| 39 | `TTAtATATaTATAtta` | landed PASS | 1–8 |

## 4. Side computations, not landed as nodes

**4.1 Linton certificate on primitive Magnus pieces (`E/pieces.py`, `E/primcert.py`).**

The landed `linton-graph-certificate-for-free-magnus-pieces` needs an interior letter that occurs
exactly once in `W_0`. For the 141 `NONFREE` words this fails in every basis tried. Suppose instead
that `W_0` is primitive in `F(a_0, a_1, a_2)`.
- A Whitehead descent gives an automorphism `φ` with `φ(W_0)` conjugate to `x_i^{±1}`.
- Killing `x_i` gives `ρ`, and `ρφ` induces an isomorphism `B_0 = F(3)/<<W_0>> → F(2)`.
- The HNN data `A = <a_0, a_1>`, `B = <a_1, a_2>` and `ψ(a_h) = a_{h+1}` transport to `K = F(2)`,
  and `lintongraph.certify(2, A, B)` is run on them.

`primcert.py` checks each of these steps:
- `φ(W_0)` cyclically reduces to one letter;
- the images `φ(x_j)` fold to the rose, so `φ` is onto;
- `ρφ(W_0) = 1`.

**Results.**
- 36 of the 141 pieces are primitive and 105 are not.
- Of the 36, the certificate gives 34 `PASS`, 1 `FAIL(alternating cycle)` and 1 `PASS_HLOOP`.

**Calibration (`E/calib.py`).**
- The same transported pipeline was run on all 100 landed letter-once `PASS` classes: 30 of length
  15 and 70 of length 16.
- The certificate data are invariant under automorphisms of `K`.
- The comparison gives `agree=100 disagree=0` on (`sZ`, depth, `|V|`, `H`, `t`, `hloops`,
  `tloops`, cycle flag, verdict).

**Why it is not landed.**
- A soundness node for the transport, a variant of `linton-graph-certificate-soundness-proof` for a
  primitive piece, has not been written.
- Soficity from "hyperbolic and virtually special" would still need a node chaining the landed
  Linton claim, `hyperbolic-cubulated-groups-are-residually-finite` (or Haglund–Wise) and the
  passage to finite-index overgroups.

Of the 34 transported `PASS` words, 32 are certified in §2 anyway.

**Module version.** `primcert.py` and `calib.py` import `A/lintongraph.py` as it is now on disk
(md5 `c288ce8b984a32afd38a63a65455e0e0`). The landed route `length15-16-free-piece-residue-via-linton-certificates`
records md5 `61fb8fe94a71be996a307db09f7e037a` for the MSI run. The file was added in commit
`345733f30`, the orphan sweep. The calibration shows that the on-disk version reproduces all 100
landed verdicts. None of this affects the §2 certificates.

**4.2 Other zero-exponent bases (`E/shiftcert.py`, `E/shiftcert3.out`).**
- The Nielsen moves `t ↦ t a^j` with `|j| ≤ 3` keep the `t`-exponent sum zero.
- On the 107 open words this gives 749 images:
  - 735 have a non-primitive piece;
  - the other 14 are the seven images each of the two primitive open words, which reproduce
    `FAIL(alternating cycle)` and `PASS_HLOOP`.
- Result: `OPEN 107`.

**4.3 Wider partial-positivity search (`E/ppwide.py`, `E/ppwide34.out`).**
- A breadth-first search over the moves `census.WH` (`x ↦ xy^{±1}`, `y^{±1}x`, `y^{∓1}xy^{±1}`), on
  cyclic words of length at most `|w| + 34 = 50`, with a cap of `2 000 000` nodes.
- None of the 107 open words reaches a partially positive image.
- Each search exhausts its component, with between 260 and 724 nodes, well below the cap. Result:
  `NOPP_EXHAUSTED 107`.

So `partially-positive-one-relator-groups-are-sofic` does not reach the open words through images
found by these moves, within length 50. This is not a proof that no such image exists: the moves are
not the full Whitehead set, and no peak-reduction argument was checked.

**4.4 Where the other approaches stop.**
- *Linton certificate on open words.* 105 pieces are non-primitive, so `B_0` is a one-relator group
  of rank 3, not visibly free. The certificate has no free vertex group to run on.
- *`FAIL(alternating cycle)` class.* The criterion itself fails in this basis.
- *`PASS_HLOOP` class.* An H-loop is present, so the certificate does not apply.
- *Collapse search.* 39 words remain in the searched range (§3). Six of them time out at index 8,
  within the 13 s per-word budget.

## 5. Reproduction and trust surface

Everything was run single-threaded, with `timeout 600` per run, from directory `E`.

    A=../../research/artifacts/one-relator-linton-graph-certificates-scripts
    S=../../research/artifacts/or-length15-residue-scripts
    timeout 600 python3 pieces.py $A/lg_words16.out > pieces.out
    timeout 600 python3 primcert.py $A/lg_words16.out > primcert.out
    timeout 600 python3 shiftcert.py primcert.out 3 > shiftcert3.out
    timeout 600 python3 calib.py $A/lg_l15.out $A/lg_words16.out > calib.out
    timeout 600 python3 ppwide.py primcert.out 34 2000000 > ppwide34.out
    timeout 600 ./vfsweep.sh primcert.out 4 20 vf4.out
    for w in TTATaaTTAATTaatA TTATaattAATTaatA; do
      timeout 600 python3 $S/vfib.py $w 6 1 2 5 >> vfrest.out 2>&1   # plus a RUN line per word
    done
    awk '$1=="PRIMPASS"{print $2}' accounting.out > words34.txt       # the 34 transported PASS words
    timeout 600 ./vfwords.sh words34.txt 6 1 60 vf34.out
    awk '$1=="VERDICT" && /-> PASS$/ {print $4}' $A/lg_words16.out > words70.txt
    timeout 600 ./vfwords.sh words70.txt 6 1 20 vf70.out
    # words42.txt: the words of words34.txt and words70.txt without a CERT so far
    timeout 600 ./vfwords.sh words42.txt 7 7 12 vf42k7.out
    # words41.txt: words42.txt minus TTTAAtaatAATTata
    timeout 600 ./vfwords.sh words41.txt 8 8 13 vf41k8.out
    for f in 4 rest 34 70 42k7 41k8; do timeout 600 python3 $S/verify.py vf$f.out > verify$f.out; done
    timeout 600 python3 recheck.py controls16.txt > recheck_controls.out
    timeout 600 python3 recheck.py vf4.out vfrest.out vf34.out vf70.out vf42k7.out vf41k8.out > recheck16.out
    timeout 600 python3 accounting.py $A/census3_16.out $A/lg_words16.out primcert.out \
      vf4.out,vfrest.out,vf34.out,vf70.out,vf42k7.out,vf41k8.out \
      verify4.out,verifyrest.out,verify34.out,verify70.out,verify42k7.out,verify41k8.out \
      recheck16.out > accounting.out

`vfsweep.sh` and `vfwords.sh` run `vfib.py` sequentially under a per-word `timeout`, and record
`TIMEOUT` lines. The `RUN` lines of `vfrest.out` report exit code 0 in 2 s and 0 s. `recheck.py`
takes about 1 s on all 172 certificates. The docstring of `recheck.py` was corrected
(`(V1)-(V4)` to `(V0)-(V3)`) after the first run. Both `recheck` outputs were then regenerated and
are byte-identical to the originals.

| File | md5 | Role |
|---|---|---|
| `E/recheck.py` | `119076e93da7071db82d0b5c7ae4ba47` | trusted checker of (V0)–(V3) |
| `E/accounting.py` | `548c4f28fdfdc0a02398eb88bddc26da` | trusted bookkeeping |
| `S/verify.py` | `0dc9f9b191f43dbb6e96cac3126ebd09` | second checker (length-15 lane) |
| `S/vfib.py` | `1a36c9ac84cd2e7f2431eb40bd7bab7e` | search only |
| `E/vfsweep.sh` | `e4d3af239be64c5d77224ae6a71a0993` | driver |
| `E/vfwords.sh` | `e4c8adfe01396cf76ff903f66e711029` | driver |
| `E/pieces.py` | `e13938445163eced3e03fafee3a0a01c` | §4 only |
| `E/primcert.py` | `ce3700155974939db79864dc18f832a4` | §1 split, §4 |
| `E/shiftcert.py` | `762ad95011303e4462ff934229c91e8d` | §4 only |
| `E/ppwide.py` | `4f6a93ff7cc8ade68215215adf9073a7` | §4 only |
| `E/calib.py` | `dba1575f834cd09d07241dc9e2ea1431` | §4 only |
| `C/census.py` | `37778ebd03ce3021530d927f173646ef` | imported by §4 scripts |
| `C/census2.py` | `b5ecec7b7e131fb90b5bcaf2bfe14227` | imported by `ppwide.py` |
| `A/lintongraph.py` | `c288ce8b984a32afd38a63a65455e0e0` | imported by §4 scripts |
| `A/census3_16.out` | `26b721a1e47eedcbb971190afbe59991` | word list |
| `A/lg_words16.out` | `fe7ff51a0210708897c7477843659780` | 70 / 141 split |

**Controls (`E/controls16.txt`, `E/recheck_controls.out`).**
- *Accepted.* `atataTAAT` at `k = 1`, with `χ = −1` (Brown-fibred).
- *Rejected.*
  - `taTAA` (`BS(1,2)`) with `cp = [0, 1]`: bottom collapse fails.
  - `taTAA` with `cp = [0, −1]`: top collapse fails.
  - `taaTAAA` (`BS(2,3)`): top collapse fails.
  - `atataTAAT` with `cp = [0, 2]`: gcd is 2.
  - The proper power `atATatAT`: word test fails.
  - The first `vf4.out` certificate with `cp[0]` changed by 1: not a cocycle.
  - `taTAA` on an index-2 cover with a gcd-2 character: gcd is 2.
  - `taTAA` with a representation on which `w` acts nontrivially: relator test fails.

**Referee checker (2026-09-16).** `E/referee_check.py` (md5 `abaccb0f09878c49718cb0aaa3ffb61e`) was
written from the statement of `virtual-fibring-collapse-certificate-gives-rf-sofic` alone. It shares
no code with `recheck.py` or `verify.py`.
- It tries collapses in sorted order first, then under up to 30 seeded random orders.
- As a sanity check, it also computes `dim H_1(X[0,S]; F_p)` and `dim H_2(X[0,S]; F_p)` with
  `p = 1000003`.

    timeout 600 python3 referee_check.py vf4.out vfrest.out vf34.out vf70.out vf42k7.out vf41k8.out > referee172.out
    timeout 600 python3 referee_check.py controls16.txt > referee_controls.out
    # referee_neg_k1.txt: CERT lines k=1 a=[0] t=[0] with cp = ±φ, one pair per census word whose
    # index-1 vfib.py line reports monic=0 (166 words, 332 lines; md5 7076ff53aefd8ca8d6d10fc1fc7823f0)
    timeout 600 python3 referee_check.py referee_neg_k1.txt > referee_neg_k1.out
    echo '--- recheck.py on the same file:' >> referee_neg_k1.out
    timeout 600 python3 recheck.py referee_neg_k1.txt >> referee_neg_k1.out

Results:
- `referee172.out`: `REFOK ... OK` on all 172 lines (`COUNT 172`), with the same `k`, `S` and
  `n = 1 − χ` as `recheck16.out`. Each line has `h0 = 1`, `h1 = n` and `h2 = 0`.
- `referee_controls.out`: the same accept/reject verdicts as `recheck_controls.out`.
- `referee_neg_k1.out`: both checkers reject all 332 non-monic characters at the collapse stage.

## 6. Literature gate (2026-09-16)

**Sources read.**
- Linton and Nyberg-Brodda, *The theory of one-relator groups: history and recent progress*,
  arXiv:2501.18306v1. The TeX source was read.
  - Theorem "Asphericity" (source lines 1708–1713), with its definitions (lines 1636–1653), is pinned
    verbatim in `non-proper-power-one-relator-complexes-aspherical-citation`.
  - Source line 932 says that residual finiteness is in general significantly weaker than being
    free-by-cyclic among one-relator groups, and that its decidability for one-relator groups is
    open. The TeX source contains no occurrence of "sofic".
- M. Linton, *One-relator hierarchies*, arXiv:2202.11324v3. Read for the graph-certificate
  background.

**Searched and checked for overlap.** None of the following settles Pestov 4.10 or treats these
words.
- An arXiv API search on one-relator groups together with sofic, residually finite and virtually
  free-by-cyclic.
- Berlai, arXiv:2502.05064.
- Wang–Zhang, arXiv:2607.21493.
- Fournier-Facio, arXiv:2608.02025.
- The problem index aimath.robertj1.com.

**Primary sources cited by the survey but not read.**
- W. H. Cockcroft, Proc. London Math. Soc. (3) 4 (1954), 375–384.
- R. C. Lyndon, Ann. of Math. (2) 52 (1950), 650–665.

**Repository imports used.**
- `kochloukova-euler-zero-cyclic-quotient-kernels-have-cd-drop` (Kochloukova 2006), in place of
  Bieri's theorem, which the length-15 artifact cited without a node.
- `finitely-generated-rf-automorphism-mapping-torus-is-rf`.

## 7. Remarks

**Relation to Attempt 6.** Attempt 6 of `unpeelable-extreme-one-relator-groups-sofic` used the same
kind of certificate on the length-15 residue (`research/artifacts/or-length15-residue-2026-09-13.md`),
but no node carries the implication. `virtual-fibring-collapse-certificate-gives-rf-sofic` is that
node. It replaces Bieri's theorem by the landed Kochloukova import and states the move rules exactly
as `recheck.py` tests them.

**Remark (not a claim).** The 39 words of §3 are hyperbolic and virtually special by Linton
certificates. With Haglund–Wise and residual finiteness passing to finite-index overgroups, they
would be residually finite. That chain is not landed here, so they are not claimed sofic.
