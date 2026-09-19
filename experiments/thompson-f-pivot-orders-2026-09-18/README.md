# Private pivot orders for the positive monoid of Thompson's `F`: tail splitting and the staircase law

Claims: `thompson-f-stubborn-sets-split-off-the-tail` (OPEN — established on 2026-09-18 and demoted
the same day at landing, when two of three referee lenses refuted item 4, the "strictly stronger
than `Λ_S(D) >= 2`" corollary; the reduction and every computation below were verified and
reproduced by all three lenses, in three independent implementations),
`thompson-f-staircase-sets-have-stubborn-layers` (OPEN).
Predecessor experiment: `experiments/thompson-f-2026-09-17/`.

## What is computed

For a finite homogeneous `S ⊆ M_d` of the positive monoid `M` of `F`, a *stubborn* set in a layer
forbids every private-pivot (triangular doubling) order for `S`
(`thompson-f-p22-monomials-admit-no-private-pivot-order`, item 1). Tail splitting says the question
lives in the finite *prefix worlds* `P_a = {forests with K(S) roots and a carets}`: a private pivot
order exists iff `core(P_a) = ∅` for every `a`. These scripts compute `core(P_a)`.

## Build and run

```sh
g++ -O2 -std=c++17 -o prefix_core prefix_core.cpp

python3 selftest.py ./prefix_core                  # forest model, K(S), letter bound,
                                                   # tail splitting, agreement with forests.py
                                                   # and with the published 1092-point core
python3 prefix_census.py ./prefix_core verify      # reproduces stubborn_census.jsonl  (~10 s)
python3 prefix_census.py ./prefix_core survivors 20000000   # the two sets with no stubborn layer
python3 prefix_census.py ./prefix_core family 20000000      # the staircase family X_m..X_(m+d-1)
python3 core_atoms.py                              # the 24-point core is a minimal stubborn set
python3 law_test.py ./prefix_core                  # the law at a = 13, both directions
python3 law_test.py ./prefix_core 4,2              # the largest test: a = 12 and a = 13, 1.7 GB
python3 small_set_census.py ./prefix_core letters2 # all 57 degree-2 sets with letters <= 2
python3 small_set_census.py ./prefix_core letters3 # all 1013 with letters <= 3 (slow)
python3 small_set_census.py ./prefix_core deg3
```

`prefix_core a "i1,i2;j1,j2;..."` takes one layer and one monomial set in normal form, and prints a
JSON line. It exits nonzero if the survivor set fails the independent stubbornness re-verification.
Peak memory is about `8 |P_a| + |B_a|` bytes: 500 MB at `|P_a| = 33 · 10^6`, 1.7 GB at
`|P_a| = 122 · 10^6`.

## Files

| file | what |
|---|---|
| `forests.py` | forest model of `M`, graft/peel, a slow reference `stubborn_core` |
| `prefix_core.cpp` | the fast core computer: lattice-path ranking, no stored adjacency |
| `prefix_census.py` | census drivers: `verify`, `survivors`, `family` |
| `law_test.py` | falsifiable test of `2 a_min + 1 = 3^(d-1)(2m+1)`, at `a_min - 1` and `a_min` |
| `core_atoms.py` | minimality and mirror symmetry of the first cores |
| `small_set_census.py` | does EVERY finite monomial set have a stubborn layer? exhaustive small scan |
| `selftest.py` | the checks listed above |
| `verify.jsonl` | reproduction of the published census |
| `survivors.jsonl` | new empty layers for `S(2,3)` (to `a = 12`) and all degree-2 letters `<= 5` (to `a = 11`) |
| `family.jsonl` | the staircase family |
| `law_test.jsonl` | `a_min(1,3) = a_min(0,4) = a_min(4,2) = 13`, each empty one layer below |
| `small_set_census_letters2.jsonl` | all 57 sets resolved, `a_min` 1 to 10, none survives |
| `small_set_census_letters3.jsonl` | 961 sets (every one of size 2 to 7, plus 4 of size 8), each searched through `a = 10`; 572 resolved, none survives. Re-running the script covers all 1013. |
| `small_set_census_deg3.jsonl` | six degree-3 sets, `a_min <= 7` |
| `core_atoms.json`, `selftest.out` | their outputs |

Claims: `thompson-f-monomial-sets-all-have-stubborn-layers` (OPEN) is the class kill the last three
files support; `thompson-f-staircase-sets-have-stubborn-layers` (OPEN) is the exact law on the
staircase family.
