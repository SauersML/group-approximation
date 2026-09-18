# SMART-type machines with exact m-fold branching for odd m (lane gq-affq, free mode, 2026-09-18)

**Goal.** `BS(1,m) ≤ 3V` for every odd `m`, by SMART's pipeline: a reversible machine with an exact `m`-fold
crossing hierarchy, induced on its genuine level-0 moves, then a brick-local height-`m` renormalization, then
`renormalizable-thompson-elements-give-baumslag-solitar`. `crossing-move-hierarchies-have-odd-branching` allows
every odd branching number. Earlier searches (lane gq-nv-obstruct) saw only 3 and 9.

**Format.** This is SMART's format.
- There are two shapes, `F` (filled) and `H` (hollow), a direction, and a phase.
- In phase 2 the head moves one cell in its direction.
- In phase 1 it reads a symbol `s` and applies a rule `(shape, s) → (s', shape', flip?)`, then returns to phase 2.
- Every table whose map `(shape, s) ↦ (shape', s')` is injective is reversible, and the format is mirror-symmetric.

**Crossing test.** Start in `(F, right, phase 2)` on cell 0, which holds `s+ = 1`; all other cells are 0.
- `T(L)` is the time of first arrival at cell `L+1`.
- The run is rejected if the head goes left of cell 0, or if the tape is not restored at an arrival (cell 0 must
  still be `s+`, cells `1..L` must be 0).

## 1. Searches (MSI, single core, C; calibrated)

| class (shapes × symbols) | method | tables / DFS nodes | exact branchings found |
|---|---|---|---|
| 2 × 3 | exhaustive | 46,080 | b = 3 only (SMART and relabelings; calibration: SMART reported with `T = 3^{L+1} − 2`) |
| 2 × 4 | exhaustive | 10,321,920 | b = 3 only |
| 3 × 3 | exhaustive | 185,794,560 | b = 3 only |
| 2 × 5 | lazy DFS | 18,875,211 nodes | b = 3 (216), **b = 5 (1422)** |
| 2 × 6 | lazy DFS (70 s cap) | partial | b = 5 |
| 3 × 5 | lazy DFS (70 s cap) | partial | b = 5 |

The lazy DFS reproduces the exhaustive results on 2 × 3 and 2 × 4 (only b = 3). The smallest quintic table has
7 pairs: `F0>H1f F1>H2f F2>F0 F3>H0f F4>H3f H0>H4 H1>F1f`, with `T = 1, 11, 61, 311, 1561, …`.

## 2. The family M_m (guessed from that table, then verified)

For `m = 2j+1`, on the alphabet `{0, …, 2j}`:
- `F0 → (1, H, flip)`;
- `F_i → (i+1, H, flip)` for `1 ≤ i ≤ j−1`;
- `F_j → (0, F, pass)`;
- `F_{j+1} → (0, H, flip)`;
- `F_i → (i−1, H, flip)` for `j+2 ≤ i ≤ 2j`;
- `H0 → (2j, H, pass)`;
- `H1 → (1, F, flip)`.

A reversible completion is `H_s → (s, F, flip)` for `s ≥ 2`, which is also the bounce rule. With it, `(H, s)` for
every `s ≠ 0` keeps `s`, turns filled, and flips.

**Verified** (`family.c`, output below). For `m = 3, 5, 7, 9, 11` and `L ≤ 7`: `T(L+1) = m·T(L) + (m+1)` exactly,
`T(0) = 1`, i.e. `T(L) = (2m^{L+1} − (m+1))/(m−1)`, with every arrival clean. For `m = 3` this is SMART's timing.

```
m=3 bad=0 T: 1 7 25 79 241 727 2185 6559  exact T(L+1)=3*T(L)+4: YES
m=5 bad=0 T: 1 11 61 311 1561 7811 39061 195311  exact T(L+1)=5*T(L)+6: YES
m=7 bad=0 T: 1 15 113 799 5601 39215 274513 1921599  exact T(L+1)=7*T(L)+8: YES
m=9 bad=0 T: 1 19 181 1639 14761 132859 1195741 10761679  exact T(L+1)=9*T(L)+10: YES
m=11 bad=0 T: 1 23 265 2927 32209 354311 3897433 42871775  exact T(L+1)=11*T(L)+12: YES
```

**Mechanism at level 1** (by hand, `m = 5`). The head crosses cell 1 five times, `→ ← → ← →`. The mark on cell 1
counts `0 → 1 → 2 → 0`. The head bounces on `s+` in the hollow shape (`H1`) and passes after the mark returns
to 0 (`F2 → (0, F, pass)`). In general the far-end mark counts `0 → 1 → ⋯ → j → 0`, and the hollow shape's
fresh mark `2j` descends `2j → ⋯ → j+1 → 0`.

## 3. Scripts

`branch_search.c` (exhaustive), `branch_dfs.c` (lazy DFS) and `family.c` are in MSI
`/projects/standard/hsiehph/sauer354/gqsrc/gq-affq/`. `family.c` in full:

```c
/* Guessed family M_m, m = 2j+1, alphabet 0..2j, shapes F=0, H=1 (SMART format, mirror-symmetric):
 *   F0 -> (1,H,flip);  F_i -> (i+1,H,flip) for 1<=i<=j-1;  F_j -> (0,F,noflip);
 *   H0 -> (2j,H,noflip);  F_i -> (i-1,H,flip) for j+2<=i<=2j;  F_{j+1} -> (0,H,flip);  H1 -> (1,F,flip).
 * Prints T(L) (first arrival at cell L+1 from F-right on s+ = 1) and checks T(L+1) = m T(L) + c, clean tape.
 * usage: family m LMAX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
  int m = atoi(argv[1]), L = atoi(argv[2]), j = (m-1)/2, A = m;
  int def[2][64] = {{0}}, ns[2][64], nsym[2][64], nf[2][64];
#define SET(s,i,sym,sh,f) (def[s][i]=1, nsym[s][i]=(sym), ns[s][i]=(sh), nf[s][i]=(f))
  SET(0,0,1,1,1); for (int i = 1; i <= j-1; i++) SET(0,i,i+1,1,1); SET(0,j,0,0,0);
  SET(1,0,2*j,1,0); for (int i = j+2; i <= 2*j; i++) SET(0,i,i-1,1,1); SET(0,j+1,0,1,1); SET(1,1,1,0,1);
  static unsigned char tape[1<<16]; memset(tape,0,sizeof tape); int off = 8, h = off, sh = 0, dir = 1, ph = 2, next = 1;
  tape[off] = 1; long t = 0, T[40]; int bad = 0;
  while (next <= L + 1 && t < 2000000000L) {
    if (ph == 2) { h += dir; ph = 1; t++; if (h < off) { bad = 1; break; }
      if (h == off + next) { int clean = tape[off] == 1; for (int i = 1; i < next; i++) if (tape[off+i]) clean = 0;
        if (!clean) { bad = 2; break; } T[next-1] = t; next++; } }
    else { int s = tape[h]; if (!def[sh][s]) { printf("undefined pair %c%d at t=%ld\n", sh?'H':'F', s, t); bad = 3; break; }
      tape[h] = nsym[sh][s]; if (nf[sh][s]) dir = -dir; sh = ns[sh][s]; ph = 2; t++; }
  }
  printf("m=%d bad=%d T:", m, bad); for (int i = 0; i < next-1; i++) printf(" %ld", T[i]);
  if (next-1 >= 3) { long c = T[next-2] - m*T[next-3]; int ok = 1; for (int i = 1; i+1 < next-1; i++) if (T[i+1] != m*T[i] + c) ok = 0;
    printf("  exact T(L+1)=%d*T(L)+%ld: %s", m, c, ok ? "YES" : "no"); }
  printf("\n"); return 0;
}
```

## 4. The SMART pipeline transfers to M_5 (MSI evidence)

**Inducing set.** SMART's genuine level-0 moves are
`Y = {filled at phase 2 with a nonzero source cell} ∪ {hollow at phase 2 with a nonzero target cell}`
(`smart-induced-on-genuine-moves-has-exact-tripling`). The level-`L` crossing contains exactly `m^L` steps in `Y`,
counted by `ycount.c`:

| machine | `N_Y(L)`, `L = 0..5` |
|---|---|
| SMART (calibration) | 1, 3, 9, 27, 81, 243 |
| `M_5` | 1, 5, 25, 125, 625, 3125 |
| `T1 = F0>F2f F1>H2f F2>F1f F3>F0 F4>H0f H0>H3 H1>F4f H2>F3f` (a SMART-like quintic) | 1, 5, 25, 125, 625, 3125 |

**Locally readable eigenvalues of the induced map `S`** (`eigm.c`: offset union-find over direction-relative
windows of radius `r`, 40 random tapes, `P(0) = 0.4`, 20,000 `S`-steps each; X = no eigenfunction at radius `r`):

| machine | `n = 2` | `n = 3` | `n = 5` | `n = 9` | `n = 25` | `n = 4` |
|---|---|---|---|---|---|---|
| SMART (calibration; matches the proved `Z/2 × Z_3` factor) | r ≥ 0 | r ≥ 1 | — | r ≥ 2 | — | none up to 7 |
| `M_5` | r ≥ 0 | none up to 5 | r ≥ 1 | — | r ≥ 2 | — |

So `M_5` shows exactly SMART's pattern with 3 replaced by 5:
- direction alternation gives `-1`;
- the phase mod `5^j` is read at radius `j`, which is item 2 of
  `renormalization-return-times-tend-to-zero-adically` with `b = 1`;
- there is no 3-torsion eigenvalue.

This is evidence for a factor onto `Z/2 × Z_5`, not a proof.

(A first version of `eigm.c` hashed the state and the first cell by XOR without mixing, so they collided. It
failed the SMART calibration, and it was fixed before these runs.)

## 5. A height-5 renormalization of M_5's induced map (MSI evidence)

`phim.c` does four things:
- it learns the phase `χ: radius-1 windows → Z/m` with `χ(Sy) = χ(y)+1`;
- for each class `A = χ^{-1}(a)`, it collects every pair `(e, e')` of one-cell edits with
  `S(e(y)) = e'(S^m y)`. Equality is exact: hashes of state plus the full tape within ±580 cells of the head, on
  arrays of 3000 cells, so the earlier `R_EQ > W` bug cannot recur. An edit deletes no cell or one cell at
  direction-relative offset −2..2, shifts the head by −2..2, and sets the shape and a direction flip;
- it constraint-propagates a rule `radius-2 window → edit`;
- it validates the rule on fresh random tapes with `P(0) ∈ {0.3, 0.5, 0.7, 0.9}`.

| machine | classes | training points | windows | empty after propagation | validation |
|---|---|---|---|---|---|
| SMART (calibration) | all 3 | 3000 each | 216 | 0 | 6000/6000 each, 0 unseen |
| `M_5` | all 5 | 12000 each | ~1830 | 0 | 10931–11316 ok, **0 bad** per class; 684–1069 validation windows unseen in training |

**SMART's rule is recovered.** In class 0 the learned rule's main edits are:
- edit 15, "delete the cell ahead of the head, keep the state" (108 windows);
- edit 38, "delete the head cell, step back, become hollow" (54 windows).

These are the two main cases of the proved rule of `smart-induced-map-has-brick-local-height-3-renormalization`.

**M_5's rule** (class 1) uses only one-cell deletions at or ahead of the head:
- SMART's edits 15 (430 windows) and 38 (234);
- deletion of the head cell with the shape or direction changed: edits 14, 44 and 74 (106, 287 and 229 windows);
- deletion ahead of the head with a head shift and a flip: edit 111 (331 windows);
- rarer variants.

The "lowest edit" choice is not canonical, so equivalent edits are split across labels.

**Not yet checked:**
- that `φ: A → Y` is a bijection;
- the ~7% of windows unseen in training;
- any proof.

So `BS(1,5) ≤ 3V` is supported, not established.
