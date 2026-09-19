# Split-basis rose of (C2): passes (T0), fails the gluing rank

The scripts need the w11 directory `../c2-free-by-cyclic-2026-09-18`, which supplies `fbc.py`, `fold2.py`
and `cert.py`. Set `W11DIR` to point elsewhere. Each run is single-threaded.

| script | checks | time |
|---|---|---|
| `pcheck.py` | the four words are in `T_8` after one `φ`; `[U] = [F1] + 2[F2] + 2[F3]` in `H_1(T_8)`; `(pSr, rP, sR, q)` is a basis | 2 s |
| `closure.py` | the support closure has 41 prefixes in 6 coset classes, with 0 undecided pairs | 2 s |
| `cplx.py` (library) | `C_0` has `χ = −7`, with 6 vertices, 16 edges and 3 cells | — |
| `minrank.py` | 72 zero-sum partitions; least forced rank 7 `(E, V, comp) = (21, 15, 1)`, unique | <1 s |
| `dcell.py` | the only `d`-lift inside `C_0` is at class 2 (`Nq⁻¹`); 0 closed lifts in the rank-7 gluing | <1 s |
| `family.py 1` | 49 bases `(a,b,c,w1 q w2)`, `|w_i| ≤ 1` | 1 min |

## Output of `family.py 1`

- **Excluded, 42 bases.** The least rank is 7 and the `d`-cell never closes. These are the bases with
  `w2 ∈ {1, b, c, A, B, C}`, for all 7 choices of `w1`.
- **Undecided, 7 bases.** These are the bases with `w2 = a`. For each of them, one coset pair is
  undecided, for example `ABCbaBcbaaDcABCda` against `AB`.
  - The difference is not found in `T_8` with `|k| ≤ 8`, nor in `T_12` with `|k| ≤ 6`, nor in `T_16`
    with `|k| ≤ 4`.
  - The `S_9` cover does not separate it either.
  - A low-index enumeration of the overgroups of `H` up to index 14 did not finish in 20 minutes.

## The rank-7 gluing (`dcell.py`)

In the rank-7 gluing, each of `h_0b, h_0c, h_3a, h_3c, h_4b` splits into two `K`-edges. The split
of `h_3a, h_3c, h_4b` separates the `a`-cell copies from the `c`-cell copies. The `d`-boundary
`t_2 · c b a · t_0⁻¹ · d⁻¹` is forced along the `c`-cell copies of `h_3c h_4b h_3a`. It arrives at the
origin of the `K`-edge over `t_0`. That edge is not a loop in the gluing, so the path cannot continue
along `t_0⁻¹`.
