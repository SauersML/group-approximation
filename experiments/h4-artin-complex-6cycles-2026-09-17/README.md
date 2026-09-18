# H_4 bottom-triple search (w4-042)

Target: `research/h4-deligne-complex-bottom-triples-have-upper-bounds.md`, the H_4 case of
Conjecture `conj:compareB` (arXiv:2405.12068, Conj. 2.33; Hoda–Huang arXiv:2602.17983 Def. 1.8,
special 6-cycles with base `s_1`). The diagram is `s1 - s2 - s3 =5= s4`, types
`ŝ1 < ŝ2 < ŝ3 < ŝ4`, `X = {s2,s3,s4}` (H_3), `Y = {s1,s2,s3}` (A_3), `Z = X ∩ Y` (A_2).

**Statement tested.** For any three vertices `x1, x2, x3` of type `ŝ1` that are pairwise upper
bounded, some vertex is adjacent to all three. You may assume every upper bound has type `ŝ4`,
because the link of an `ŝ2` or `ŝ3` vertex is a join. So `z = uA_Y` is adjacent to `gA_X` exactly
when `u ∈ g A_X A_Y`.

## 1. Finite core: the Coxeter complex (exhaustive, exact)

`coxcheck.py`. The Coxeter complex `C_W` sits inside the Artin complex `Δ` as the positive
apartment `{lift(w) A_T}`. The projection `π : Δ → C_W` (quotient by the pure Artin group) is a
type-preserving simplicial retraction onto it. So a triple in `C_W` that is pairwise upper bounded
but has no common upper bound in `C_W` has none in `Δ` either: it would be a counterexample.
Conversely, a counterexample in `Δ` that lies inside one apartment `g·C_W` projects to a
counterexample in `C_W`.

```
python3 coxcheck.py A2 A3 B3 B3r H3 H3r A4 B4 D4 H4 H4r
```

| diagram (ordered toward the last node) | pairwise-bounded `ŝ1` triples | without common upper bound |
|---|---|---|
| A2 | 1 | 1 |
| A3 | 4 | 0 |
| B3 (`s1-s2=4=s3`) | 8 | 0 |
| B3r (`s1=4=s2-s3`) | 32 | 8 |
| H3 (`s1-s2=5=s3`) | 20 | 0 |
| H3r (`s1=5=s2-s3`) | 140 | 20 |
| A4 | 10 | 0 |
| B4 | 32 | 0 |
| D4 | 32 | 0 |
| **H4** (`s1-s2-s3=5=s4`) | **1200** | **0** |
| H4r (`s1=5=s2-s3-s4`) | 152400 | 22800 |

For H4 there are 120 vertices of type `ŝ1` and 600 of type `ŝ4`, each `ŝ1` vertex has 20 `ŝ4`
neighbours, and every pairwise-bounded triple in the apartment has a common upper bound.

**What this rules out:** any counterexample to the H_4 statement that lies in a single apartment.
The wrong orientations (B3r, H3r, H4r) already fail in the apartment, so the check can tell the
orientations apart.

## 2. Artin-group balls (Garside normal forms)

- `garside.py`: exact left-greedy normal forms `Δ^k p` for spherical Artin groups.
- `search.py` / `search2.py`: the Python search, used for calibration.
- `dump.py`: writes the Coxeter tables and coset-representative balls.
- `tsearch.c`: the C search.
- `selfpy.py`: cross-checks the C and Python multiplication, inverse and membership tests
  (0 mismatches on `self_c.txt`).

**Model** (cycle-to-word translation, Def. 7.2 of arXiv:2405.12068):
- By transitivity on chambers, `x1 = A_X`, `y1 = A_Y`, `x2 = aA_X`, `y2 = abA_Y`, `x3 = abcA_X`.
- Here `a ∈ R_Y(La)`, `b ∈ R_X(Lb)`, `c ∈ R_Y(Lc)`. `R_T(L)` is one representative of each
  coset `gA_Z` with `g` a product of at most `L` signed Garside simples of `A_T`. The explicit lists
  are in `data/<PREFIX>.reps`.
- The pair `{x1,x3}` is bounded by `uA_Y` (`u ∈ R_X(Lu)`) iff `u^{-1}abc ∈ A_Y A_X`.
- `uA_Y` is a common upper bound iff also `u^{-1}a ∈ A_YA_X`. `y2` is one iff `ab ∈ A_XA_Y`.

**Membership test.** `in_product(g)` checks `Δ_Y^{2K} g Δ_X^{2K} ∈ A_Y^+ A_X^+` by stripping the
maximal left `A_Y^+` divisor.
- A positive answer is an exact certificate that `g ∈ A_Y A_X`.
- A negative answer is only relative to the padding `K`.
- So every "found" is a rigorous certificate. A pair adjacency missed at padding `K` only removes
  that triple from the tested family.

**Procedure.** For each `(a,b,c)` with `x3 ≠ x1` and `y2` not already a common bound, scan `u`.
- Some `u` certifying both adjacencies: **found**.
- Some `u` certifying only the `{x1,x3}` adjacency: **candidate**, rescanned over `R_X(Lu2)` at
  padding `K2`.
- Still no common bound: **unresolved**.

Usage:
```
python3 dump.py H4 La Lb Lc Lu Lu2 data/PREFIX
gcc -O2 -o tsearch tsearch.c
A0=0 A1=36 ./tsearch data/PREFIX K K2 > PREFIX.out
```
The `data/` files are regenerable with `dump.py`, which takes seconds to minutes.

### Calibration (known cases)

All calibration runs use `(La,Lb,Lc,Lu,Lu2) = (2,2,2,2,4)`, `K = 4`, `K2 = 5`.

| diagram | truth | bounded nontrivial triples | found | candidates | unresolved |
|---|---|---|---|---|---|
| B3 (`s1-s2=4=s3`) | true (Haettel, Thm 2.37 of 2405.12068) | 942 | 926 | 16 | **0** |
| H3 (`s1-s2=5=s3`) | true (Huang, Thm 7.1 of 2405.12068) | 928 | 928 | 0 | **0** |
| A3 (`s1-s2-s3`) | not covered by the conjecture (no label ≥ 4); induced 6-cycles generally lack quasi-centres (Deligne, remark after Thm 1.3 of 2405.12068) | 1252 | 965 | 287 | **245** |

- The known-true cases resolve completely. A3 leaves 245 persistent candidates (not certified
  counterexamples).
- The candidate stage is not vacuous: B3 has 16 candidates, all resolved at `Lu2 = 4`.
- The Python search (`results2.jsonl`) reproduces the same picture.

### H_4 results

| run | ball sizes `(R_Y(La), R_X(Lb), R_Y(Lc), R_X(Lu), R_X(Lu2))` | K, K2 | triples | bounded nontrivial | found | candidates | unresolved |
|---|---|---|---|---|---|---|---|
| `H4_11112.out` | (7, 39, 7, 40, 1811) | 3, 5 | 1911 | 480 | 480 | 0 | 0 |
| `H4_21212.out` | (36, 39, 36, 40, 1811) | 3, 5 | 50544 | 4520 | 4520 | 0 | 0 |
| `H4_22222.out` (one JSON line per `a`; `batch3.sh`, resumed by `batch3r.sh` after a restart) | (36, 1810, 36, 1811, 1811) | 4, 5 | 4300560 | 168240 | 168240 | 0 | **0** |

- In the runs with `b ∈ R_X(1)`, `max_u_index_used` shows that every common upper bound lies in
  `R_X(1) A_Y` or is `y2`.
- With `b ∈ R_X(2)`, witnesses up to index 1802 of `R_X(2)` are used.
- Padding saturation: `H4_21212_K4.out` and `H4_21212_K6.out` give identical counts at
  `K = 3, 4, 6`.

### Single-edge configurations (pure balls)

Huang's H_3 proof (Lemma 7.3 of arXiv:2405.12068) cases on the shape of `π(ω)` in the Coxeter
complex. Case 1, where `π(ω)` is a single edge, is the one needing the CAT(0) auxiliary
arrangement. In that case `a, b, c` have images in `W_Z`, so modulo `A_Z` they are pure.

`dumppure.py` builds balls of products of at most `L` standard pure generators `A_t = w s² w^{-1}`,
one per reflection `t = wsw^{-1}` of `W_T`. These are much longer elements than the simple-letter
balls. They are taken modulo `A_Z`, with the `u`-balls as before.

| run | truth | sizes `(PY(La), PX(Lb), PY(Lc), R_X(Lu), R_X(Lu2))` | K, K2 | bounded nontrivial | found | unresolved |
|---|---|---|---|---|---|---|
| `PA3_22224.out` | A3, no conjecture | (25, 25, 25, 15, 96) | 5, 6 | 2148 | 2072 | **76** |
| `PB3_22224.out` | B3, true | (25, 49, 25, 31, 446) | 5, 6 | 2464 | 2464 | **0** |
| `PH3_22224.out` | H3, true | (25, 81, 25, 53, 1366) | 5, 6 | 3232 | 3232 | **0** |
| `PH4_21212.out` | **H4** | (69, 25, 69, 40, 1811) | 4, 5 | 7934 | 7934 | **0** |
| `PH4_22212.out` (one line per `a`; `batch4.sh` + `batch4r.sh`) | **H4** | (69, 709, 69, 40, 1811) | 4, 5 | 164002 (all 69 a, 4305048 triples) | 164002 | **0** |

In `PH4_21212` every common upper bound found lies among the first 6 elements of `R_X(1)`.

The ball files may contain one redundant representative of the trivial coset `A_Z`. `coset_key`
depends on its padding `Nb`, so the key used for the identity can differ from the key computed
for elements of `A_Z`. Such an `a` gives `x2 = x1`, a degenerate triple that is always "found"
(via `y3`). This only inflates the counts.

**What the negative result rules out.** Take any `a ∈ R_Y(La)`, `b ∈ R_X(Lb)`, `c ∈ R_Y(Lc)`
and `u ∈ R_X(Lu)` from the listed balls such that the adjacencies `A_X ~ A_Y ~ aA_X ~ abA_Y ~ abcA_X ~ uA_Y ~ A_X`
are certified at padding `K`. Then `A_X, aA_X, abcA_X` have a common `ŝ4` neighbour, and the
explicit witness is certified. So no counterexample to the H_4 bottom-triple statement is a 6-cycle
whose words lie in these balls.
