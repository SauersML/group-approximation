# Naive permutation search for Thompson F almost-solutions (2026-09-13)

**Verdict: uninformative.** A simulated-annealing search for pairs `(A, B)` in `Sym(n)` that nearly
satisfy the two Thompson relators while keeping `d(AB, BA) >= eps` never got below random-level relator
defect, for `n` from 64 to 1024. The method is too weak to say anything about stability or soficity of
`F`. It is recorded so that nobody repeats it expecting evidence.

## Setup

- Relators `R_1 = [ab^-1, a^-1ba]`, `R_2 = [ab^-1, a^-2ba^2]`, commutator `[x,y] = x^-1 y^-1 x y`.
- Objective `E = d(R_1, id) + d(R_2, id) + 4 max(0, eps - d(AB, BA))`, normalized Hamming distance.
- Moves: a random transposition applied to `A` or `B`, with full recomputation. Temperature linear
  from 0.05 to 1e-4. Random starts. `400 n` iterations. Two seeds, `eps` in `{0.25, 0.5}`.
- MSI job 708928 (agsmall, Python 3.6.8, numpy 1.19.5). Script and log sit next to this file:
  `thompson-f-sofic-anneal-2026-09-13-search/anneal.py`, `.../anneal.sbatch`, `.../anneal.708928.log`.

## Results (best relator defect `d(R_1) + d(R_2)` among states with `d(AB,BA) >= eps`)

| n | eps | seed 1 | seed 2 |
|---|---|---|---|
| 64 | 0.25 | 1.422 | 1.453 |
| 256 | 0.25 | 1.777 | 1.801 |
| 256 | 0.5 | 1.777 | 1.801 |
| 512 | 0.25 | 1.895 | 1.895 |
| 512 | 0.5 | 1.895 | 1.895 |
| 1024 | 0.25 | 1.961 | 1.967 |
| 1024 | 0.5 | 1.961 | 1.967 |

The defect grows toward 2, the value for random pairs, as `n` grows. The commutator stayed near 1,
so the penalty never bound.

## Why this carries no information

- A transposition changes the image of two points, but a relator is a word of length 12 to 16. So
  most single moves barely change the defect, and the landscape is flat at the random level.
- A meaningful search has to start near structure: near-commuting pairs (defect 0, commutator 0)
  pushed toward a fixed commutator, or permutation models built from `F`'s action on finite pieces of
  the dyadic tree. Neither was run.
- Upper bounds from any search can never certify stability. Only a structured construction with
  defect tending to 0 and commutator bounded below would matter, and that would prove `F` sofic by
  `thompson-f-sofic-iff-relator-system-unstable`.
