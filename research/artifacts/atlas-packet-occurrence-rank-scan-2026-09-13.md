# Atlas packet occurrence census and nuisance-quotient rank scan (2026-09-13)

Lane `solve-nh-atlas-scan`, for `atlas-half-block-root-face-full-packet-model-exists`.
It automates, over all 4,648 packet entries, the hand census that ended at
packet entries 3261–3262 and the first common-RHS return star.

## Method

`experiments/atlas_packet_occurrence_rank_scan.py`:

1. Reconstructs the packet with `atlas_relator_rank5_complete_packet.assemble`
   and asserts the ordered word-list SHA-256
   `9e751115287b18fbe847309379d2710ffa0b1466c836d32ff4ec24446e6c2b99`.
2. Recovers the root-level factors of each entry:
   - `root_ij_rs`, `orth_ij_kl_rs`, `st3_ijk_rs` and `inv_ij_a` come from the
     names emitted by the source generators;
   - the twelve reverse rows come from `atlas_relator_rank5_reverse.generate_relators`.

   Census: root 200, orth 2980, st3 1432, inv 24, reverse 12.
3. Linearizes each entry in the free rectangular language of
   `atlas-mixed-minor-needs-nuisance-quotient-rank`:
   - a root is `x_kl(w)=1+iota_k w p_l`, and `(1+N)^(-1)=1-N`;
   - the commutator convention is the packet's `x y x^-1 y^-1`;
   - a reverse entry is read blockwise as generator = product of factors.

   Dynamic programming over composable letters gives the exact blockwise
   expansion.
4. With exact `F_2` elimination (or rational elimination with
   `--characteristic 0`), computes `rank[C D]-rank(D)` for every
   right-hand-side star. The desired columns are the star's path monomials;
   every other column met by the star is nuisance. It also checks common-mode
   survival, i.e. that the constant vector satisfies every meeting row.
5. Asserts the hand-checked validations: entries 3261,3262 give increment 0,
   and the star 3261,3336,3409 gives increment 2.

Reproduce on MSI, not locally:

```text
python3 experiments/atlas_packet_occurrence_rank_scan.py --characteristic 2 --out scan-char2.json
python3 experiments/atlas_packet_occurrence_rank_scan.py --characteristic 0 --out scan-char0.json
```

Each run takes under ten seconds on an MSI compute node.

## Results in characteristic two (the packet field)

- **Projected equations:** 1,448 nonzero ones (equation-list SHA-256
  `46558e0bd4e476368359cb85a29fef002bd37ad1fdec3f625c14ba6bf5e648bb`):
  - 1,432 `st3` rows, each two terms `P=R`;
  - 16 reverse block rows, each two terms `G_ab=M_ab`.
- **Vanishing rows:** root and orth rows project to zero. The 24 involutivity
  rows project to `2N` and vanish in characteristic two.
- **Every nonzero equation equates two monomials.** The constant assignment on
  each connected component of the incidence graph satisfies the whole packet,
  so no literal entry pins a common mode.
- **Two-letter stars:** 320 of them, all of size three and all `st3`, each with
  increment `2` and a surviving common mode.
- **One-letter stars:** 100 of them, with increments `{1: 20, 4: 48, 5: 32}`.
  - The first in canonical order above two is `x_13(e)`, entries
    `3182,3186,3356,3360,3425`, with increment 4.
  - These factor one-letter occurrences through displayed constant
    coefficients or reverse one-factor seams.
  - Every common mode survives.

## Characteristic zero, for comparison

The same 1,432 `st3` and 16 reverse equations appear with coefficients
`(+1,-1)`. The 24 involutivity rows survive as `2N=0`, which fixes one-letter
roots only when the field is ignored. So characteristic zero is not the packet
semantics.

- **Two-letter stars:** unchanged (increment 2, common mode surviving).
- **One-letter stars:** increments `{1: 20, 4: 48, 5: 8, 6: 24}`; the 24 stars
  that reach 6 are exactly those meeting an involutivity row.

## Verdict

**Fence.** No family of literal packet entries raises any common-RHS star
above the rank needed for common-mode authentication. Two-letter stars stop
at increment 2, exactly as in the hand checks. The increments above two
occur only on constant-coefficient one-letter stars, and they control path
differences, never the common mode. The missing third direction for
`atlas-half-block-root-face-full-packet-model-exists` must come from
normal-closure consequences, or from ring relations among coefficient letters,
which the free language does not impose. The Morita-rectangular model realizes
every literal equation even with the Leavitt relations imposed.

## Files

- `scan-char2.json`, `scan-char2.log`: characteristic-two run, with the full
  per-star tables.
- `scan-char0.json`, `scan-char0.log`: characteristic-zero comparison.
