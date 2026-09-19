# Cone-lemma certificates for the 509 radius-6 census classes (w11-107, 2026-09-18)

Node: `research/bmw-census-radius6-cone-lemma-certificates.md` (proof in `...-proof.md`).

`experiments/bmw-cone-trees-2026-09-18` (w10-107) left 509 of the 994 *remaining* census classes
(`remaining.json` there) without a certificate: those whose positive-cone instance is first UNSAT on
the radius-6 ball with short 4 (products `u w` with `|u| ≤ 4` or `|w| ≤ 4`). Tree-like cone
refutations are too large there (a C++ port of `dtree2.py`, `ctree.cpp`, did not finish `50_30` #14
in 900 s), so each class gets a DAG proof instead: a list of *cone lemmas* "`S_i ⊄ P`", checked in
group language by `verify_lemmas.py` from the census squares alone.

## Pipeline (not part of the proof)

| file | role |
|---|---|
| `ctree.cpp`, `ctree.py` | radius-`R`, short-`k` positive-cone CNF of one class (env `CNF=file`: writes `file` and `file.map`, var -> word, inverse var). `g++ -O2 -o ctree ctree.cpp`. Same instance as `lo_census.lo_sat` (608014 clauses for a `(5,3)` class at `R = 6`, short 4). Without `CNF` it is the tree search. |
| `gsolve.py` | Glucose 4 (pysat) with a DRUP proof |
| drat-trim (`github.com/marijnheule/drat-trim`, backward mode, `-L`) | LRAT proof, trimmed to the core |
| `lrat2cone.py` | LRAT -> cone lemmas: clause `C` becomes `S(C) = {x : -x ∈ C} ∪ {x^{-1} : x ∈ C}`, each hint a product, square or lemma step |
| `runlem.py` | runs the above for every class of `remaining.json` without a w10 tree; log `run_lem.jsonl` (`(5,3)`), `run_lemB.jsonl` (the rest) |

Reproduce: `DRAT_TRIM=/path/drat-trim python3 runlem.py 6 4 log.jsonl [patterns]`
(single-threaded; about 5 s per `(4,3)`, 15 s per `(4,4)`, 30 s per `(5,3)` class).

## Proof artifacts

| file | content |
|---|---|
| `certs.jsonl.gz` | one certificate per class: `{pat, cls, R, short, els, lemmas}`; `els` is a word table, lemma `i` is `{S, steps, end}` over indices into it |
| `verify_lemmas.py` | the checker (normal form and critical pairs copied from w10's `verify_cone.py`; nothing from the pipeline) |
| `verify_certs.log` | `python3 verify_lemmas.py certs.jsonl.gz`: one line per class and `summary: ...` |
| `mutate_lemmas.py`, `mutate_lemmas.log` | six corruptions of a valid certificate, all rejected |
| `coverage.py`, `coverage.log` | the 485 w10 trees and these certificates are disjoint and cover `remaining.json` exactly |

Steps of a lemma proof, starting from `Q = S_i` (everything in `Q` is in `P` by assumption):
`[z, u, w]` (`z = u w`, `u, w ∈ Q`), `["sq", z, u]` (`u = z z ∈ Q`, so `z ∈ P`), `["L", j, z]`
(`j < i`, `S_j \ Q = {z^{-1}}`, so `z ∈ P`). End: `[x, y]` with `x y = 1`, or `["L", j]` with
`S_j ⊆ Q`. The last lemma has `S = ∅`.
