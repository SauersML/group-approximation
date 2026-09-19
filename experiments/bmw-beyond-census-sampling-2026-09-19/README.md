# Beyond the census: BMW parity kernels in degrees (5,4), (6,3), (5,5) and with non-involutive letters

Claim: `research/bmw-parity-kernel-vertex-groups-are-never-convex.md`, with proof route
`research/bmw-parity-kernel-vertex-groups-are-never-convex-proof.md`. Target lane:
`bmw-44-sat-survivor-parity-kernels-not-left-orderable`.

The helper modules `lo_census.py`, `vh_enum.py` and `irred_tw.py` are imported from
`../bmw-census-left-orders-2026-09-17/`.

## 1. Sampling batch (`batch.sh`, `batch.jsonl`, `tally.py`)

`sample.py m pA n pB seed 1 out.jsonl` draws one random one-vertex complete VH complex. There are `m`
horizontal letters, `pA` of which are pairs of mutually inverse letters and the rest involutions, and
likewise `n`, `pB` vertically. It then runs the census pipeline with no solver answer trusted:
1. It checks confluence.
2. It certifies reducibility when both automaton images are finite (cap 4000).
3. It counts Klein pairs.
4. It searches for a radius-4 cone tree (`ctree`, a C++ port of `dtree2.py`) and checks the tree
   independently.
5. If there is no R4 tree, it searches for a radius-6 short-4 cone tree.
6. If that fails too, it runs `cone.py`. Glucose 4 proposes DRAT lemmas, `rup` (`rup.cpp`, our own unit
   propagation) checks every lemma and trims to a core, and the core is re-checked. The CNF itself is
   re-derived clause by clause from the rewriting normal form (`semcheck`).

The batch covers 8 patterns with 8 seeds each (100..107), under `nice`, single-threaded, at most 1200 s
per sample.

| pattern | reducible | R4 cone tree | R6s4 cone tree | R6s4 RUP cone lemmas | Klein chain (§4) |
|---|---|---|---|---|---|
| 50_40 | 4 | 2 | 0 | 1 | 1 (seed 107) |
| 60_30 | 4 | 2 | 2 | 0 | 0 |
| 50_50 | 1 | 5 | 0 | 2 | 0 |
| 51_41 | 4 | 3 | 1 | 0 | 0 |
| 61_31 | 3 | 5 | 0 | 0 | 0 |
| 52_42 | 5 | 3 | 0 | 0 | 0 |
| 63_31 | 3 | 5 | 0 | 0 | 0 |
| 52_52 | 3 | 5 | 0 | 0 | 0 |
| total | 27 | 30 | 3 | 3 | 1 |

"Reducible" means both automaton images were certified finite. Trees are in `trees/` and cone-lemma cores
in `certs/` (lemmas written as signed words). Several classes closed by cone trees have no Klein pair in
the radius-4 ball (`klein=0` in `tally.py` output), so Klein chains cannot be the universal certificate.

## 2. Which of the four certificate types is universal

The four types of `bmw-census-solver-free-parity-kernel-certificates` are Klein chains, Klein-power
chains, cone-propagation trees and cone lemmas.

**Cone trees and cone lemmas are universal.** By compactness, `Γ^+` is not left-orderable iff, for some
`R`, the positive-cone instance on the ball of radius `R` is unsatisfiable. A complete branching on
"`x` or `x^{-1}`" is then a cone tree, and any resolution refutation gives RUP cone lemmas. This does not
bound `R`. In practice they closed 36 of the 37 samples not certified reducible. The exception, 50_40 seed 107,
is still SAT at R8s2, yet a Klein chain of four pure words of length at most 6 refutes it (§4).

**Klein chains and Klein-power chains are not universal.** A chain needs Klein pairs
`a b a^{-1} = b^{-1}` (or power relations) in `Γ^+`. The census classes 31_30 #26 and 31_31 #12 have none in the radius-6 ball,
and 19 of the 36 samples certified above have no Klein pair in the radius-4 ball (`klein=0`). All of these are refuted by cone trees or
cone lemmas.

## 3. Quotients by normal closures of vertex groups (`qsphere.py`, `qcross.py`, `qtally.py`)

Theorem 2 of the claim shows the following. A convex subgroup containing a finite-index subgroup of `B^+`
contains `N_B`, and `Γ^+/N_B ≅ Q_B = A^+/⟨⟨orbit relations on S_2(T_A)⟩⟩`.

`qsphere.py` computes the orbits and then `Q_A`, `Q_B`. When the action is transitive with degree at
least 3 it gives `Q = 1` directly (Step 5). Otherwise it uses GAP: abelian invariants, plus coset
enumeration capped at 200000.

`qcross.py` recomputes `Γ^+/N_B` directly from the full presentation of `Γ` as a cross-check. It agrees on
30_30 #10 and #16, and on 40_30 #14 and #16.

Result over the 1201 census classes that are not certified reducible:
- Both `Q` finite: 141.
- Exactly one infinite: 902.
- Both infinite: 158.

## 4. The one sample the cone pipeline misses: 50_40 seed 107 (`surv*.jsonl`, `kchain.py`, `kverify.py`)

The record is `surv.jsonl`. The horizontal local action is `S_5`, and the Thompson–Wielandt test at radius 2
succeeds on the horizontal side (`localsum.py`), so the class is irreducible. The vertical local action has
order 2 and is intransitive. `Q_B = 1` and `Q_A^{ab} = ℤ^2`.

The positive-cone instance is SAT at R4 (no tree), at R6s4 (1364572 clauses) and at R8s2
(`surv_R8s2.jsonl`: 3360572 clauses, 218900 variables, semantics re-derived).

`kchain.py surv.jsonl 0 L` searches for Klein chains among pure `h`-words and `v`-words of even length at most `L`.
- `L = 4`: 460 nodes and 788 edges, no cycle.
- `L = 6` (`surv_kchain6.jsonl`): 6552 nodes and 26628 edges. It finds the cycle

  `x_0 = v2v0v1v2 → x_1 = h2h3 → x_2 = v0v2v0v1v2v0 → x_3 = h0h1 → x_0`, with `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}`.

By Lemma 1 of `bmw-40-40-193-281-332-klein-chain-proof` (with `a = x_{i+1}`, `b = x_i`), `|x_0| < |x_1| < |x_2| < |x_3| < |x_0|` in any left
order of `Γ^+`. So `Γ^+` is not left-orderable.

`kverify.py` checks the chain independently, from the squares alone, with no code shared with the search
(`surv_kverify.log`). It checks the bijection, local confluence, membership in `Γ^+`, normal form, and the four
inversion identities. It rejects the reversed chain, a reordered chain and a one-letter mutation.

So all 64 samples are settled: 27 are reducible and 37 are not left-orderable. The chain involves words of letter
length 6 and products such as `x_{i+1} x_i` of length up to 12. These lie outside the balls the cone pipeline
reached (radius 6 with short factor 4, and radius 8 with short factor 2). So on this class a non-universal
certificate type succeeds where the universal ones fail at every radius that was feasible.

## 5. Subgroup-cone search in any degree (`sgen.py`, `sgcert.py`, `sgverify.py`)

These generalize `../bmw-44-survivor-left-orders-2026-09-17/gen_search.py` and `verify_cert.py` to arbitrary degrees
and inverse maps.

Calibration: `sgcert.py cal281.jsonl 0 4 2 0 1 3 0 1 3` regenerates the #281 certificate
(`certs/cal_40_40_281.json`: 880 elements, 109 RUP lemmas). `sgverify.py` accepts it and rejects a corrupted
relation and a truncated lemma list.

On the 50_40 survivor, about half of the 360 subgroups were tried at R4s2 with no hit before the Klein chain made
the search unnecessary. No claim rests on this search.
