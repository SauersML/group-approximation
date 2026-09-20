# Marked finite Lie witness

All calculations use exact standard-library Python arithmetic over F7.

## Reproduce

```sh
python3 experiments/hrf-wave4-four-generator-2026-09-20/eliminate.py --class-bound 5 --export experiments/hrf-wave4-four-generator-2026-09-20/class_five_lie_witness.json
python3 experiments/hrf-wave4-four-generator-2026-09-20/verify_finite_witness.py
```

The first command constructs the quotient after exact filtered elimination.
The second reads only the exported finite data. It does not import the
constructor, inspect its rank calculation, or use a checkpoint.

Classes four and six can be replayed by changing `--class-bound`. Optional
`--checkpoint PATH --work-seconds 20` bounds individual ideal-closure runs.
Completed receipts are `class_4.json`, `class_5.json`, `class_6.json`.

## Export schema

`class_five_lie_witness.json` contains:

- `prime`: 7.
- `dimension`: 28, with basis indexed 0 through 27.
- `class_bound`: 5.
- `brackets`: records `{i,j,value}` for nonzero `[e_i,e_j]` with `i<j`.
  `value` is a length-28 vector modulo seven. Reversed brackets follow by
  antisymmetry; omitted brackets, including diagonal brackets, are zero.
- `vertex_generators`: the six length-28 vectors named `U0,V0,U1,V1,U2,V2`.
- `mark`: the length-28 vector for the canonical central generator's logarithm.
- `basis_pivot_words`: tensor-word provenance of each selected basis vector.
  The standalone verifier does not use this provenance.

The verifier checks the Lie axioms, nilpotency class, generation, the three
vertex presentations, centrality and nonvanishing of the mark, and all six
marked face equations. It derives BCH independently from a two-letter
tensor exponential/logarithm and checks its conversion to nested Lie
brackets as an associative identity.

The completed verification gives lower-central dimensions
`[28,24,21,17,11,0]`. BCH turns this algebra into an explicit group of
order `7^28`, with central mark of order seven. It detects the specified
canonical class. It does not supply central orders `7^n` for unbounded n.

The proof that elimination preserves the entire presentation is in
`research/artifacts/hyperbolic-rf-wave4-filtered-elimination-2026-09-20.md`.
