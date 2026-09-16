---
rg: 2
id: length16-residue-virtual-fibring-certificates
kind: route
title: Search, verify and independently recheck collapse certificates on the 211 length-16 residue classes
target: length16-residue-classes-virtually-free-by-cyclic
requires:
  - virtual-fibring-collapse-certificate-gives-rf-sofic
artifacts:
  - research/artifacts/or-length16-nonfree-residue-2026-09-16.md
  - research/artifacts/or-length15-residue-scripts/vfib.py
  - research/artifacts/or-length15-residue-scripts/verify.py
  - research/artifacts/one-relator-linton-graph-certificates-scripts/census3_16.out
  - research/artifacts/one-relator-linton-graph-certificates-scripts/lg_words16.out
  - experiments/or-length16-nonfree-residue-2026-09-16/primcert.out
  - experiments/or-length16-nonfree-residue-2026-09-16/vfsweep.sh
  - experiments/or-length16-nonfree-residue-2026-09-16/vfwords.sh
  - experiments/or-length16-nonfree-residue-2026-09-16/vf4.out
  - experiments/or-length16-nonfree-residue-2026-09-16/vfrest.out
  - experiments/or-length16-nonfree-residue-2026-09-16/vf34.out
  - experiments/or-length16-nonfree-residue-2026-09-16/vf70.out
  - experiments/or-length16-nonfree-residue-2026-09-16/vf42k7.out
  - experiments/or-length16-nonfree-residue-2026-09-16/vf41k8.out
  - experiments/or-length16-nonfree-residue-2026-09-16/verify4.out
  - experiments/or-length16-nonfree-residue-2026-09-16/verifyrest.out
  - experiments/or-length16-nonfree-residue-2026-09-16/verify34.out
  - experiments/or-length16-nonfree-residue-2026-09-16/verify70.out
  - experiments/or-length16-nonfree-residue-2026-09-16/verify42k7.out
  - experiments/or-length16-nonfree-residue-2026-09-16/verify41k8.out
  - experiments/or-length16-nonfree-residue-2026-09-16/recheck.py
  - experiments/or-length16-nonfree-residue-2026-09-16/controls16.txt
  - experiments/or-length16-nonfree-residue-2026-09-16/recheck_controls.out
  - experiments/or-length16-nonfree-residue-2026-09-16/recheck16.out
  - experiments/or-length16-nonfree-residue-2026-09-16/accounting.py
  - experiments/or-length16-nonfree-residue-2026-09-16/accounting.out
  - experiments/or-length16-nonfree-residue-2026-09-16/referee_check.py
  - experiments/or-length16-nonfree-residue-2026-09-16/referee172.out
  - experiments/or-length16-nonfree-residue-2026-09-16/referee_controls.out
  - experiments/or-length16-nonfree-residue-2026-09-16/referee_neg_k1.txt
  - experiments/or-length16-nonfree-residue-2026-09-16/referee_neg_k1.out
---

**Argument.** For each of the 172 words in the target claim, the files below contain a `CERT`
line `(w, α, τ, c)` that `recheck.py` accepts. `recheck.py` checks exactly (V0)–(V3) of
`virtual-fibring-collapse-certificate-gives-rf-sofic`, with the moves as stated there. That claim
then gives:
- a subgroup `H` of index `k`;
- a surjection `H → Z` whose kernel is free of rank `n = 1 − χ(X[0,S])`;
- `H ≅ F_n ⋊ Z`;
- `G` residually finite and sofic.

The values of `k`, `S` and `n` for each word are listed in §2 of the artifact.

**Inputs.**
- `census3_16.out` (md5 `26b721a1e47eedcbb971190afbe59991`): 211 `REST` words.
- `lg_words16.out` (md5 `fe7ff51a0210708897c7477843659780`): 70 words ending `-> PASS` and 141
  `NONFREE` words.
- `primcert.out`: splits the 141 `NONFREE` words into 34 transported-certificate passes and 107
  open words. This split only organises the search. The certificates do not depend on it.

**Search.** Each run used `vfib.py WORD KMAX 1 2 [KMIN]`, with `vfib.py` md5
`1a36c9ac84cd2e7f2431eb40bd7bab7e`. For each index `k`, it:
- enumerates the transitive degree-`k` representations up to conjugacy;
- tries the characters with coefficients in `[−2, 2]` on a basis of `H^1(X_H; Z)`;
- keeps a character only if its Alexander polynomial has unit end coefficients;
- searches vertex potentials in `[−1, 1]^{k−1}` for a representative `cp` whose windows collapse.

All runs were sequential, under `timeout`.

| Run | Words | Index range | Timeout per word (s) | `CERT` lines | `TIMEOUT` lines |
|---|---|---|---|---|---|
| `vfsweep.sh primcert.out 4 20 vf4.out` | 107 open | 1–4 | 20 | 105 | 0 |
| `vfib.py WORD 6 1 2 5 >> vfrest.out` | the other 2 open words | 5–6 | 600 | 2 | 0 |
| `vfwords.sh words34.txt 6 1 60 vf34.out` | 34 | 1–6 | 60 | 32 | 0 |
| `vfwords.sh words70.txt 6 1 20 vf70.out` | 70 `PASS` | 1–6 | 20 | 30 | 0 |
| `vfwords.sh words42.txt 7 7 12 vf42k7.out` | 42 uncertified | 7 | 12 | 1 | 0 |
| `vfwords.sh words41.txt 8 8 13 vf41k8.out` | 41 uncertified | 8 | 13 | 2 | 6 |

That gives 172 `CERT` lines, on 172 distinct words.

**Verification, twice.**
1. `verify.py` (md5 `0dc9f9b191f43dbb6e96cac3126ebd09`, landed with the length-15 residue and
   sharing no code with `vfib.py`) reports `VERIFIED` on all 172 lines, in `verify*.out`.
2. `recheck.py` (md5 `119076e93da7071db82d0b5c7ae4ba47`) was written in this lane and shares no
   code with `verify.py` or `vfib.py`.
   - It reads only `w`, `a=`, `t=` and `cp=`.
   - It rebuilds `X[0,S+1]`, `X[−1,S]` and `X[0,S]` from scratch.
   - It checks each move condition explicitly: the only alive edge at the vertex, not a loop, no
     alive 2-cell through the vertex; and for an edge, a single alive 2-cell with multiplicity 1.
   - It never removes a piece of `X[0,S]`.
   - On the six files, `recheck16.out` reports `RECHECKED` on all 172 lines (`CHECKED 172`).

**Controls.** `recheck.py` on `controls16.txt` gives `recheck_controls.out`:
- **Positive.** It accepts `atataTAAT` at `k = 1` with `χ = −1`.
- **Negative.** It rejects 8 certificates:
  - `BS(1,2)` with `φ = ±χ`: bottom and top collapse fail;
  - `BS(2,3)`: top collapse fails;
  - a gcd-2 character, both at `k = 1` and on an index-2 cover;
  - a proper-power relator;
  - a `vf4.out` certificate with one edge value altered, which is no longer a cocycle;
  - a representation on which the relator acts nontrivially.

**Accounting.** `accounting.py` (md5 `548c4f28fdfdc0a02398eb88bddc26da`) produces
`accounting.out`. It asserts:
- the 70 + 141 words of `lg_words16.out` are exactly the 211 `REST` words, and the 141 are exactly
  the words of `primcert.out`;
- every verified word has exactly one `CERT` line, which is on the word itself and not an image;
- every verified word passes the (V0) word test;
- `verify.py` and `recheck.py` accept the same 172 words with the same `k`, `S` and fibre rank;
- all 107 open words are verified.

It also lists the 39 words without a certificate.

**Trust surface.**
- `recheck.py` and `accounting.py`, in full.
- The Python standard library.
- The census files, only as the source of the word list.

`vfib.py` is trusted only to have produced the lines. A wrong search could lose certificates, but
it cannot create a false one, because the checkers rebuild everything. `verify.py` was written
by the length-15 residue lane (2026-09-13) and `recheck.py` by this lane (2026-09-16).

**Referee check (2026-09-16).**
- `recheck.py` was read line by line against (V0)–(V3). The review covered:
  - the right action;
  - tail heights on backward letters;
  - the window cells;
  - edge multiplicity counted in both orientations;
  - loops excluded through vertex–edge multiplicity 2;
  - the final complex must equal `X[0,S]`.
  No defect was found.
- A third checker, `referee_check.py` (md5 `abaccb0f09878c49718cb0aaa3ffb61e`), was written from the
  claim statement alone. It shares no code with the other two.
  - On the six certificate files, `referee172.out` accepts all 172 lines, with the same `k`, `S`
    and `n` as `recheck.py`.
  - As a sanity check, it also computes `dim H_1(X[0,S]; F_p) = n` and `H_2(X[0,S]; F_p) = 0`, with
    `p = 1000003`. Both hold on all 172.
  - On `controls16.txt` it gives the same verdicts as `recheck.py` (`referee_controls.out`).
- **Bulk negative control.** `referee_neg_k1.txt` holds the 166 census words whose index-1
  character has a non-monic Alexander polynomial (`monic=0` lines of `vfib.py`), with `±φ`, which
  gives 332 lines. Such a character cannot be fibred. Both `referee_check.py` and `recheck.py`
  reject all 332 lines at the collapse stage (`referee_neg_k1.out`).
- `verify.py`, `recheck.py` and `accounting.py` were rerun, and they reproduce `verify*.out`,
  `recheck16.out`, `recheck_controls.out` and `accounting.out` byte for byte.

Commands to reproduce are in §5 of the artifact.
