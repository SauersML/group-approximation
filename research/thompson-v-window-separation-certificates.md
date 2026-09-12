---
rg: 2
id: thompson-v-window-separation-certificates
kind: route
title: Replay a character or a small permutation image of each V window's table group, then apply table-realization transfer
target: thompson-v-small-windows-have-finite-separations
requires:
  - strict-pairs-transfer-to-table-realizations
artifacts:
  - research/artifacts/thompson-v-window-screen-2026-09-12.md
  - experiments/gottschalk-thompson-v/v_window_screen.py
  - experiments/gottschalk-thompson-v/runs/results-excluded.json
---

1. **Build the relators exactly.**
   - `experiments/gottschalk-thompson-v/v_window_screen.py` builds `S`, `M` and the
     relators of `U` from reduced tree-pair products.
   - Reduced forms are unique, so equal products are detected exactly.
   - Generators are indexed deterministically: keys sorted by `repr`.
   - `--selftest` checks associativity, inverses, the action on words, canonical
     reduction, the orders of all named elements, the Cannon–Floyd–Parry relators of
     `F`, and `|GL(3,2)| = 168`.
2. **Characters.** The witness for `chi: U -> Z/p` is its vector of values on the
   generators. `--verify` checks that `chi` vanishes mod `p` on every relator vector
   and that `chi(x_h) != 0`.
3. **Permutation images.**
   - After Tietze simplification, GAP 4 (`sagemath/10.7` on MSI) finds an epimorphism
     onto `A5` or `PSL(3,2)`, or a coset action of index 3.
   - The witness lists the images of the ORIGINAL generators as permutations of degree
     at most 7, and GAP checks every relator under `MappedWord`.
   - `--verify` then recomputes the relators independently, and checks in Python that
     every relator maps to the identity and `x_h` does not.
4. **Transfer.** Let `psi: U -> K` have `psi(x_h) != 1`. Then `psi` realizes the
   products of `S x M` and `<h> x M`, which are exactly the relators of `U`, and keeps
   `1` apart from `h`.
   - The same holds for every sub-window `S' <= S`, `M' <= M` with `1` in both and
     `hM' = M'`.
   - Where a cell of `S'M'` coincides with a cell `hm'`, the two values agree through
     the relator `(s, m) ~ (1, hm')` and the symmetry relator `x_h x_(m') = x_(hm')`.

   An invariant-output pair has the two-cell Garden of Eden `{1, h}`. So Corollary 3
   of `strict-pairs-transfer-to-table-realizations` excludes every strict pair on
   these windows.

**Replay.** From `experiments/gottschalk-thompson-v`, with the witness directory at
`runs/wit`:

    python3 v_window_screen.py --selftest
    python3 v_window_screen.py --verify runs/results-excluded.json --gap-dir runs/wit

Both exited 0 on MSI on 2026-09-12: `selftest OK`, then `VERIFY_DONE bad=0` over all
50 windows. The transcript is `runs/verify-excluded.txt`. Replaying the full
`runs/results.json` exits 1, and correctly so: six windows have no witness, the not-covered
cases of the target.
