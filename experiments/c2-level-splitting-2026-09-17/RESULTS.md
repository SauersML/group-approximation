# c2 level splittings (w17-048, 2026-09-19)

Supports `research/c2-mapping-torus-realizations-are-free-factor-level-splits.md`.

## Running

The scripts import `fbc.py` and `fold2.py` from the sibling directory
`../c2-free-by-cyclic-2026-09-18`. To use another copy, set `W11DIR`.

Each script runs single-threaded in seconds to a few minutes:

```
python3 check1.py    # u0, u1, r trivial in G; a = DDeddEbcB; levelized r and level ranges
python3 split3.py    # the width-3 splitting: F_4 words of the level generators, free-factor tests
python3 fftest.py    # depth-2 Whitehead neighbours of width <= 3: edge group A never a free factor
python3 nsearch.py   # beam search for the least level width (about 10 min)
```

## Files

- `hlib.py`: the embedding `H → G`, the one-relator `r`, the exponents `ε`, and levelization.
- `ff.py`: Stallings cores, and Whitehead peak reduction over `F(p,q,r,s)`.
  - `is_free_factor(gens)` returns `(bool, rank, minimal core size)`.
  - `is_ffs(groups)` tests a family of subgroups for being a free factor system up to conjugacy. It
    reduces the disjoint union of the cores to distinct-letter roses.
  - Built-in checks: `{⟨p,q⟩, ⟨qrQ⟩}` is a free factor system, and `{⟨p⟩, ⟨pqpQ⟩}` is not.
- `nsearch.py`: Whitehead automorphisms of `F(b,c,d,e)` that fix `d`, applied to `r`. `width` computes
  the Moldavanskii edge-group rank `W = Σ_g (ν_g − μ_g)` for the stable letter `d`.

## Output

- `check1.py`: all relators are trivial in `G`. Levels are `b ∈ [−1,0]`, `c ∈ [2,3]`, `e ∈ [−2,0]`, so
  `W = 4`.
- `nsearch.py`: the start has `W = 4`. The best `W` is 3 at every depth from 1 to 6, over up to 104233
  states. No presentation of width at most 2 was found. The search is a beam, so this is heuristic.
- `fftest.py`: 48 presentations of width at most 3. Each edge group `A` has rank 3 and minimal core
  size 8, so none is a free factor.
- `split3.py`, on `r' = eDDEddCBeDDEddbDcd` with `c' = cB`:
  - `e_{-2} = pQ`, `e_{-1} = qR`, `e_0 = rS`;
  - `c'_2 = SrpQsRRsq`, `c'_3 = b_0⁻¹ f b_0 c'_2 f` with `f = e_0 e_{-2}⁻¹`;
  - `A = ⟨e_{-2}, e_{-1}, c'_2⟩` is not a free factor (core 8);
  - `⟨e_{-2},e_{-1}⟩` and `⟨e_{-2},e_{-1},e_0⟩` are free factors, and `c'_2` is primitive;
  - `{⟨e_{-2},e_{-1}⟩, ⟨c'_2⟩}` and `{⟨e_{-2},e_{-1},e_0⟩, ⟨c'_2⟩}` are not free factor systems.

## Tier

- `check1.py` and `split3.py` are exact.
- `fftest.py` is exact on the 48 listed presentations.
- The claim "least width 3" is a heuristic beam search.
