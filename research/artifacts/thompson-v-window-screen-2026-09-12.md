# Thompson's V: a rule-free window screen, and the radius where it goes blind

Lane `gottschalk-thompson-v`, 2026-09-12. Supports `thompson-v-nonsurjunctive`,
`thompson-v-surjunctive` and `large-window-table-groups-present-the-ambient-group`.

## 0. Summary

- **What was run.** A V-native version of the rule-free invariant-output screen
  (`experiments/gottschalk-thompson-v/v_window_screen.py`, commit 4f02729ac), with
  exact reduced tree-pair arithmetic. It covers 14 generator families at radii
  `1:1, 1:2, 2:1, 2:2`, so 56 windows.
- **Stage 1 (characters).** 24 windows are excluded. 32 survive: every window whose
  symmetry has order 3 in a CFP family, and almost every window with a perfect finite
  corner (`A_5` or `GL(3,2)` on leaves).
- **Stage 2 (GAP quotients and low index).** Among the 32 survivors:
  - 26 separate onto `A5`, `PSL(3,2)` or cosets of index 3. Python replays all 26
    witnesses and the 24 characters (`--verify`: 50 OK).
  - 5 survive every target through `PSL(2,11)` and every coset action of index at most 6.
    Four of them also survive stage 2c (p-quotients of class at most 4, eleven larger simple
    targets, index 7 to 9); the fifth is still running.
  - 1 (gl32-leaves-f-order2 `1:1`) timed out at 1500 s. It is rerunning (stage 2d).

  See Section 4.
- **Theorem (Section 5).** Above the radius `max(ceil(L/2), r_m, |h|)`, where `L` bounds
  the relator lengths of a finite presentation of `V` on the generators, the table group
  of a window IS `V`. Since `V` is simple, such windows have no finite image, and a
  realization amounts to an embedding of `V` into a surjunctive group.
- **Consequence.** A rule-free screen over `V` can only exclude windows below that
  radius. It cannot decide `thompson-v-surjunctive` in either direction. Above that
  radius, a counterexample search has to work at the level of local rules.

## 1. What is screened

`V = G_(2,1)`. An element is a bijection between complete prefix codes, stored in reduced
form: sibling pairs `(c0 -> d0, c1 -> d1)` are merged into `c -> d` until none remain.
The reduced form is unique, so elements are equal iff their keys are equal. Products
compose maps: `(g * f)(w) = g(f(w))`.

`--selftest` checks, on MSI (Python 3.8.3):
- associativity, inverses and the action on random words, over 300 random triples;
- canonicity of reduced forms under leaf splitting;
- the orders of all named elements;
- the two Cannon–Floyd–Parry relators of `F`, which hold in the left convention;
- `|<E_ij>| = 168` for the `GL(3,2)` leaf group.

A window is `(S, M, <h>)` with `S = B_(r_s)(X)` and `M = <h> . B_(r_m)(X)`. Its table
group `U` has generators `x_a` (`a` in `S u M`, `x_1 = 1`) and relators

    x_s x_m = x_s' x_m'   whenever  s m = s' m'  in V,
    x_k x_m = x_(km)      for k in <h>, m in M.

By Corollary 3 of `strict-pairs-transfer-to-table-realizations`, a homomorphism `U -> K`
into a finite group with `x_h != 1` excludes every invariant-output strict pair on the
window, whatever the local rules and the alphabet.

## 2. Generator families

Named elements, written as prefix replacements:

| Name | Codes | Order |
|---|---|---|
| `A` | `0, 10, 11 -> 00, 01, 1` | infinite |
| `B` | `0, 10, 110, 111 -> 0, 100, 101, 11` | infinite |
| `C` | `0, 10, 11 -> 11, 0, 10` | 3 |
| `p0` | `0, 10, 11 -> 10, 0, 11` | 2 |
| `p1` | `0, 10, 110, 111 -> 0, 110, 10, 111` | 2 |
| `s` | `0, 1 -> 1, 0` (half turn, in `T`) | 2 |
| `t4`, `c4` | transposition `(00 01)` and 4-cycle on the leaves `00, 01, 10, 11` | 2, 4 |
| `c5`, `c3`, `d22` | 5-cycle, 3-cycle and `(12)(34)` on the leaves `00, 010, 011, 10, 11` | 5, 3, 2 |
| `e_ij`, `r3` | transvections and the coordinate 3-cycle of `GL(3,2)` on the eight depth-3 leaves | 2, 3 |

| Family | `X` | `h` |
|---|---|---|
| t-cfp-order3 | `A, B, C` | `C` |
| t-cfp-half-turn | `A, B, s` | `s` |
| f-plus-p0 | `A, B, p0` | `p0` |
| v-cfp-order2 | `A, B, C, p0` | `p0` |
| v-cfp-order3 | `A, B, C, p0` | `C` |
| v-cfp-p1 | `A, B, C, p0, p1` | `p1` |
| v-torsion-2-3 | `p0, C` | `p0` |
| v-torsion-2-3-order3 | `p0, C` | `C` |
| sym4-leaves-f | `t4, c4, A, B` | `t4` |
| alt5-leaves-f-order3 | `c5, c3, A, B` | `c3` |
| alt5-leaves-f-order2 | `c5, c3, A, B` | `d22` |
| gl32-leaves-f-order2 | six `e_ij`, `A, B` | `e01` |
| gl32-leaves-f-order3 | six `e_ij`, `A, B` | `r3` |
| gl32-leaves-v-order2 | six `e_ij`, `p0, C` | `e01` |

`A, B, C, p0` generate `V`, and `A, B, C` generate `T`.

## 3. Stage 1: characters

All products are exact. Each character witness is stored in `results.json` and replayed
by `--verify`.

| Family | 1:1 | 1:2 | 2:1 | 2:2 | largest `|S|`, `|M|` |
|---|---|---|---|---|---|
| t-cfp-order3 | Z/3 | Z/3 | Z/3 | survives | 33, 60 |
| t-cfp-half-turn | Z/2 | survives | survives | survives | 26, 42 |
| f-plus-p0 | Z/2 | Z/2 | Z/2 | Z/2 | 26, 42 |
| v-cfp-order2 | Z/2 | Z/2 | Z/2 | Z/2 | 44, 74 |
| v-cfp-order3 | survives | survives | survives | survives | 44, 87 |
| v-cfp-p1 | Z/2 | Z/2 | Z/2 | survives | 59, 100 |
| v-torsion-2-3 | Z/2 | Z/2 | Z/2 | Z/2 | 6, 6 |
| v-torsion-2-3-order3 | survives | survives | survives | survives | 6, 6 |
| sym4-leaves-f | Z/2 | Z/2 | Z/2 | survives | 47, 80 |
| alt5-leaves-f-order3 | Z/3 | survives | survives | survives | 59, 135 |
| alt5-leaves-f-order2 | survives | survives | survives | survives | 59, 116 |
| gl32-leaves-f-order2 | survives | survives | survives | survives | 95, 164 |
| gl32-leaves-f-order3 | Z/3 | survives | survives | survives | 95, 285 |
| gl32-leaves-v-order2 | survives | survives | survives | survives | 65, 106 |

So 24 windows are excluded and 32 survive.

**Reading.**
- A leaf transposition as the symmetry (`p0`; `t4` and `p1` below radius `2:2`) is
  separated by a character mod 2 at once. The table groups of these small windows are
  far from perfect.
- When `p0` and `C` are both generators, the order-3 symmetry `C` survives characters
  from radius `1:1`.
  - On the leaves `0, 10, 11`, `p0` is the transposition `(0 10)` and `C` is the 3-cycle
    `(0 11 10)`, so `p0 C p0 = C^2`.
  - The window relators `x_p0 x_p0 = 1`, `x_(C p0) = x_C x_p0` and
    `x_p0 x_(C p0) = x_(C^2) = x_C^2` give `2 chi(p0) = 0` and `2 chi(p0) = chi(C)` mod 3.
  - So `chi(C) = 0` for every character mod 3.

  Without `p0` (family t-cfp-order3), `C` is separated below `2:2`.
- Symmetries inside a perfect corner (`A_5`, `GL(3,2)`) survive characters everywhere
  except the order-3 symmetries at `1:1`. The nine-leaf windows behaved the same way
  over the Leavitt units (`small-leavitt-invariant-output-windows-have-finite-separations`).

## 4. Stage 2: status

The stage-1 survivors were written as GAP files: Tietze simplification, epimorphisms
onto `A5`, `PSL(3,2)`, `A6`, `A7`, `PSL(2,8)`, `A8`, `PSL(2,11)`, then coset actions of
index at most 6.
- **First two attempts.** The driver fed the file list to `xargs` with its stdin
  redirected from `/dev/null`, so `xargs` ran one empty job, and the replay reported every
  survivor without a witness.
- **Stage 2b.** A standalone runner fed from the pipe, GAP 4 via `sagemath/10.7` on MSI.
  Each witness is checked in GAP under `MappedWord`.
- **Python replay.** `--verify` recomputed every relator from the tree-pair arithmetic
  and replayed each witness: 50 OK (24 characters, 26 permutation images). Six windows
  have no witness: the rows "none" and "timed out" below.

| Separating image | Windows |
|---|---|
| `A5` (degree 5) | v-cfp-order3 `1:1, 1:2, 2:1`; alt5-leaves-f-order2 all four; alt5-leaves-f-order3 `1:2, 2:1, 2:2`; t-cfp-order3 `2:2` |
| `PSL(3,2)` (degree 7) | gl32-leaves-v-order2 all four; t-cfp-half-turn `1:2, 2:1, 2:2`; gl32-leaves-f-order2 `1:2, 2:1`; gl32-leaves-f-order3 `1:2, 2:1` |
| cosets of index 3 | v-torsion-2-3-order3 all four |
| none (targets through `PSL(2,11)`, index at most 6) | sym4-leaves-f `2:2`; v-cfp-order3 `2:2`; v-cfp-p1 `2:2`; gl32-leaves-f-order2 `2:2`; gl32-leaves-f-order3 `2:2` |
| timed out (1500 s, simplified to 6 generators and 9 relators); stage 2d rerun below | gl32-leaves-f-order2 `1:1` |

After Tietze simplification, the five survivors have 3 generators and 8 to 13 relators.
- Among them is v-cfp-order3 `2:2`, whose letters `A, B, C, p0` generate `V`.
- **Stage 2c**, on these five: an abelian-invariants diagnostic; the largest 2- and
  3-quotients of class at most 4; epimorphisms onto `PSL(2,13)`, `A9`, `PSL(2,16)`,
  `PSL(2,17)`, `PSL(3,3)`, `PSL(2,19)`, `M11`, `PSU(3,3)`, `PSL(2,23)`, `PSL(2,25)`,
  `PSL(2,27)`; and coset actions of index 7 to 9.

| Window (`2:2`) | Abelianization of `U` | 2-quotient, 3-quotient (class at most 4) | Result |
|---|---|---|---|
| v-cfp-order3 | trivial (perfect) | trivial, trivial | survives every stage-2c test |
| sym4-leaves-f | trivial (perfect) | trivial, trivial | survives every stage-2c test |
| gl32-leaves-f-order2 | `Z` | order 16, order 81, both killing `x_h` | survives every stage-2c test |
| gl32-leaves-f-order3 | `Z` | order 16, order 81, both killing `x_h` | survives every stage-2c test |
| v-cfp-p1 | running | running | running |

**Reading.**
- Two of these table groups are perfect at radius `2:2`, with no p-quotients and no
  image of degree at most 9 that separates `x_h`. One of them comes from `A, B, C, p0`,
  which generate `V`.
- This is how Section 5 predicts a window behaves as its tables approach a presentation
  of the simple group `V`. It is not evidence of a strict pair: no local rules were
  examined here.
- Survival at this depth means that small-radius finite-image exclusions are exhausted
  for these generating sets. It says nothing about which windows carry strict pairs.

**Internal control.** `p0` and `C` both permute the three leaves `0, 10, 11`, so every
`v-torsion-2-3` window lies in a finite subgroup `S_3` of `V`. The inclusion realizes its
tables injectively, with `h != 1`. So all four `v-torsion-2-3-order3` windows are
excluded directly, and stage 2 must find an image for each of them, index 3 included.
This is the check that stage 2 actually runs.

## 5. The table group of a large window is V

Claim `large-window-table-groups-present-the-ambient-group`, route
`large-window-table-group-presentation-proof`.

**Theorem.** Let `G = <X | R>` be finite, with `X` symmetric and relators of length at
most `L`. Let `h` have finite order. If `1 <= r_m <= r_s`, `|h|_X <= r_s` and
`ceil(L/2) <= r_s`, then `x_a -> a` is an isomorphism from the table group of
`(B_(r_s)(X), <h> . B_(r_m)(X), <h>)` onto `G`.

**Proof idea.**
- Every table generator is a word in the letters, via the relators `x_(b') x_g = x_b`
  along geodesics and the symmetry relators.
- Each relator of `R`, split into two halves of length at most `ceil(L/2)`, evaluates in
  the table group through prefixes inside `S`, so it holds on the letters.
- Hence `G -> U`, `g -> x_g`, is a surjective homomorphism inverse to evaluation.
- Full proof in the route.

**Over V.** `V` is finitely presented, infinite and simple
(`thompson-v-finitely-presented-infinite-simple`). For every finite generating set there
is a radius `R_0` beyond which every window with `r_m >= 1` has table group `V`. At those
windows:
- every finite image kills `x_h`, so stages 1 and 2 are blind by construction;
- a realization with `x_h != 1` is an embedding `V -> K`. Using it to exclude pairs needs
  a surjunctive `K` containing `V`, which is the conclusion `thompson-v-surjunctive`
  itself.

The same holds for `T` with `A, B, C`, and for every other finitely presented infinite
simple group.

## 6. What this means for the V lane

- **Counterexample side.** Rule-free exclusions reach only radii below `R_0(X)`. A
  window that survives there is not evidence of a strict pair; it is what simplicity
  forces once the tables present `V`.
  - The meaningful test for large windows is at the level of rules: for an invariant
    rule `f` on `M`, decide by SAT whether two configurations on `SM` with different
    values at `1` have equal outputs on `S` (the two-copy decoding instance).
  - UNSAT would give a decoder with memory `S`, hence a strict pair over `V`.
  - The rules must satisfy the necessary conditions already on main:
    `invariant-output-rules-need-odd-invariant-monomials`,
    `invariant-output-symmetry-must-be-core-free`, and
    `invariant-output-injective-automata-need-invisible-symmetry`.
- **Positive side.** Nothing. Section 5 shows that the table-realization machinery,
  pushed to large windows over `V`, asks exactly for a surjunctive group containing `V`.
  This matches the circularity of `thompson-v-surjunctive-via-coset-peeling` and the
  rewrite invariance of `v-self-similar-rewrites-preserve-strict-pairs`.

## 7. Replay

The run files are in `experiments/gottschalk-thompson-v/runs/`:
- `results.json`: all 56 windows;
- `results-excluded.json`: the 50 excluded windows;
- `wit/`: the 26 permutation witnesses;
- `screen.log`, `stage2b.out`: the stage logs;
- `verify-excluded.txt`: the replay transcript.

From `experiments/gottschalk-thompson-v`:

    python3 v_window_screen.py --selftest
    python3 v_window_screen.py --verify runs/results-excluded.json --gap-dir runs/wit

- `--verify` recomputes every relator from the tree-pair arithmetic, then checks each
  stored character and each permutation witness in Python.
- On MSI on 2026-09-12, both commands exited 0: `selftest OK`, then `VERIFY_DONE bad=0`
  over 50 windows.
- `--verify runs/results.json` exits 1, because six windows have no witness: the five
  survivors and the timed-out window.
- The census is claim `thompson-v-small-windows-have-finite-separations`, route
  `thompson-v-window-separation-certificates`.
