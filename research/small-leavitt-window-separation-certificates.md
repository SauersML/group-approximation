---
rg: 2
id: small-leavitt-window-separation-certificates
kind: route
title: Replay a character or a small permutation image of each window's table group, then apply table-realization transfer
target: small-leavitt-invariant-output-windows-have-finite-separations
requires:
  - strict-pairs-transfer-to-table-realizations
artifacts:
  - research/artifacts/gottschalk-small-window-screen-2026-09-12.md
  - experiments/gottschalk-small-presentations/window_table_screen.py
  - experiments/gottschalk-small-presentations/nine_leaf_corner_rep.py
---

1. **Build the relators exactly.**
   `experiments/gottschalk-small-presentations/window_table_screen.py` builds `S`, `M`
   and the relators of `U` from normal-form products in the shared checker
   `experiments/nonsofic-certificates/leavitt.py`. The indexing of generators is
   deterministic: keys sorted by `repr`.
2. **Characters.** For a character `chi: U -> Z/p` the witness is the vector of values
   on the generators. `--verify` checks that `chi` vanishes on every relator vector
   mod `p` and that `chi(x_h) != 0`.
3. **Permutation images.** GAP 4.14 finds an epimorphism onto PSL(3,2), or a coset
   action of index at most 6, after Tietze simplification. The witness lists the images
   of the ORIGINAL generators as permutations of degree `n` at most 7. GAP checks every
   relator under `MappedWord`. `--verify` then recomputes the relators independently
   and checks, in Python, that every relator maps to the identity and `x_h` does not.
   For `eld-full-order2` at `1:1`, `nine_leaf_corner_rep.py` writes the witness in
   the same format instead. It lists the images of the original generators under the
   GL(6,2) corner representation of the claim, as permutations of the 63 nonzero row
   vectors. The script checks every relator in Python, and GAP 4.14 (sage 10.7)
   checks them under `MappedWord`, before the witness is written.
4. **Transfer.** A homomorphism `psi: U -> K` with `psi(x_h) != 1`:
   - realizes the products of `S x M` and `<h> x M`, which are exactly its relators;
   - keeps `1` and `h` apart;
   - does both for every sub-window `S' <= S`, `M' <= M` with `hM' = M'`.

   An invariant-output pair has the two-cell Garden of Eden `{1, h}`. So Corollary 3
   of `strict-pairs-transfer-to-table-realizations` excludes every strict pair on
   these windows.

**Replay.** From the directory `experiments/gottschalk-small-presentations`, with the
checker at `LEAVITT_LIB`:

    python window_table_screen.py --verify runs/res-a.json --gap-dir runs/wit
    python window_table_screen.py --verify runs/res-b.json --gap-dir runs/wit
    python window_table_screen.py --verify runs/res-c.json --gap-dir runs/wit

All three exited 0 on MSI on 2026-09-12: 32, 12 and 1 windows, all OK.
