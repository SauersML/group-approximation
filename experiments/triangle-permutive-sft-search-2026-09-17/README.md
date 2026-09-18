# Exhaustive small-window search for aperiodic sub-SFTs of quasigroup spacetimes

This experiment serves the claim `research/small-window-quasigroup-sub-sfts-have-periodic-points.md`. Its
correctness argument is in `research/small-window-quasigroup-sub-sfts-have-periodic-points-proof.md`. The question
is the focus hole `free-minimal-triangle-permutive-sft-exists`: does some finite quasigroup spacetime
`X_⋆ = {x : x(z+e_2) = x(z) ⋆ x(z+e_1)}` contain a nonempty sub-SFT with no periodic point?

## Method

- **Normal form.** Every sub-SFT with forbidden shapes inside the upward triangle `Δ_L` is
  `Ω(A) = {x ∈ X_⋆ : all length-L row words lie in A}`. This covers every `w × h` box with `w + h - 1 <= L`.
- **Periodic points.** `Ω(A)` has a periodic point iff `A ⊇ W_C` for some `F`-cycle `C` of spatially periodic rows.
- **Emptiness.** `Ω(A) = ∅` iff some level shift `Z_n(A)` is empty. These shifts are presented by trimmed and
  minimized automata `G_n`.
- **Search.** Branch and bound over `(IN, OUT)` word assignments, with three sound tools:
  - an emptiness prune;
  - a language prune (an essential `A` lies inside the `L`-language of `Z_8(A_max)`);
  - certification of long-period cycles read off closed walks of `G_n`.
- **Candidates.** A candidate is a leaf that stays alive to level 60 with no certified periodic row. It would be the
  window set of a possibly aperiodic sub-SFT.

## Results (one quasigroup per isomorphism class)

| order k | quasigroups | window L | P (enumerated periods) | nodes | candidates | log |
|---|---|---|---|---|---|---|
| 2 | 1 (Ledrappier, `Z/2`) | 6 (covers L <= 5) | 16 | 10725 | **0** | run3.log |
| 3 | 5 | 3 (covers L = 2) | 10 | 2765 | **0** | run3.log |
| 4 | 35 | 2 | 8 | 3359 | **0** | run3.log |

Every emptiness certificate needed level at most 7. For `k = 2`, `L = 6`, eight nodes were closed only by
certifying cycles of period larger than 16.

## What it rules out

For each listed `(k, L)`, no quasigroup of order `k` has a nonempty sub-SFT without periodic points whose forbidden
patterns fit inside translates of `Δ_L`. That includes all `w × h` boxes with `w + h <= L + 1`. In particular, no
free minimal sub-SFT of Ledrappier's shift is cut out by patterns on boxes with `w + h <= 7`. A free example needs
larger windows or a larger alphabet.

It does not rule out:

- larger windows or larger alphabets;
- sofic or effective subshifts;
- sub-SFTs in a recoding that is not a quasigroup spacetime.

## Reproduce

```sh
nice -n 10 timeout 1200 python3 search.py 2 6 16 60   # about 10 min
nice -n 10 timeout 1200 python3 search.py 4 2 8 60    # about 1 min
nice -n 10 timeout 1200 python3 search.py 3 3 10 60   # about 30 s
python3 validate.py                                   # random cross-checks of facts (P) and (E)
```

Usage: `search.py k L P NMAX [--all-squares]`. Requires numpy. Single-threaded.

## History

- A first version without certification reported 77 alive leaves at `k = 2`, `L = 5`. Each one had a periodic row
  of period larger than `P = 16`.
- Certification closes such leaves soundly, because `legal_cycle` iterates `F` exactly on the periodic row.
