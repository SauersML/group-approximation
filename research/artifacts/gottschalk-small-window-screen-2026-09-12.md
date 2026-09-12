# Rule-free screen of small invariant-output windows over the Leavitt unit group

Date: 2026-09-12. Lane `gottschalk-small-presentations`. Computation on MSI with
`experiments/gottschalk-small-presentations/window_table_screen.py` (commits
6c79b80b1, e6d679844, 3240f1246) and the shared checker
`experiments/nonsofic-certificates/leavitt.py` (MSI copy at VERSION 2e9a9873e).

## What is screened

`G = L_(F_2)(1,2)^x`. An invariant-output window is `(S, M, H)` with `H = <h>`
finite cyclic, `1` in `S` and `M`, and `HM = M`
(`leavitt-units-carry-injective-invariant-output-automaton`). Its table group `U`
has one generator `x_a` for each `a` in `S u M`, with `x_1 = 1`, and relators

    x_s x_m = x_s' x_m'   whenever  s m = s' m'  in G   (s, s' in S; m, m' in M),
    x_k x_m = x_(km)      for k in H, m in M.

By `strict-pairs-transfer-to-table-realizations` (Corollary 3), if some
homomorphism from `U` into a finite group sends `x_h` to a nontrivial element,
then no pair of local rules on that window is strict. The rules never need to be
examined. A window is **dead** once such a homomorphism is found.

Windows are balls: `S = B_(r_s)(X)` and `M = H . B_(r_m)(X)` for a generating set
`X`, balls taken in `X u X^-1`. All products are exact normal-form products in
`G`.

## Method

- **Stage 1, characters.** `p` is the (prime) order of `h`. A homomorphism
  `U -> Z/p` is a vector `chi` over `F_p` vanishing on every relator vector.
  Linear algebra over `F_p` decides whether one with `chi(x_h) != 0` exists, and
  the vector is stored as the witness.
- **Stage 2, nonabelian images (GAP 4.14 via `sage -gap`).**
  - Tietze-simplify `U`.
  - Try epimorphisms onto PSL(3,2), A7, PSL(2,8), A8 and PSL(2,11) in their
    natural actions.
  - Then try permutation actions on cosets of subgroups of index at most 5 or 6.
  - A separating image is stored as permutation images of the original
    generators, relator-checked in GAP.
- **Replay.** `window_table_screen.py --verify` recomputes the relators from the
  checker and replays every character and permutation witness in Python.

## Generating sets

| Family | `X` | `h` (order) |
|---|---|---|
| control-gl2 | `u = 1+s0t1`, `v = 1+s1t0`, `w = s0t1+s1t0` | `u` (2) |
| v-plus-swap | `w`, `a = (0,10,11)->(00,01,1)` | `w` (2) |
| transvections-depth12 | `u, v`, `t = 1+S[00]T[01]`, `q = 1+S[1]T[01]`, `r = 1+S[01]T[1]` | `u` (2) |
| transvections-swap | `w, t, q, r` | `w` (2) |
| order3-thompson | `g = uv`, `a` | `g` (3) |
| order3-transvections | `g, t, q, r` | `g` (3) |
| mixed-all | `u, v, w, a, t, q, r` | `u` (2) |
| mixed-all-order3 | `g, w, a, t, q, r` | `g` (3) |
| atlas-order2 / -order3 | the four GL(4,2) atlas chart units of `dfsat.py` (they generate `G`) | `u` (2) / `g` (3) |
| eld1-compressors-order2 | the six `E_ij(1)` on the nine-leaf corner `alpha = (000,001,01)`, compressors `cu, cv` | `E_01(1)` (2) |
| eld1-compressors-order3 | as above, plus the 3-cycle `p3` of the `alpha` leaves | `p3` (3) |
| eld-full-order2 | the 30 `E_ij(r)`, `r in {1, s0, s1, t0, t1}`, plus `cu, cv` | `E_01(1)` (2) |

The nine-leaf generators and the atlas charts are those of
`experiments/nonsofic-certificates/kaplansky-df/sat/dfsat.py`.

## Results

Radii are `r_m:r_s`. Every verdict below was replayed in Python from the checker
(`--verify`), exit 0. Results: `experiments/gottschalk-small-presentations/runs/`
(commit d99a23cf3).

| Family | Radii | `|S|`, `|M|` | Separating finite image of `U` |
|---|---|---|---|
| control-gl2, v-plus-swap, transvections-depth12, transvections-swap, mixed-all | 1:1, 1:2, 2:1, 2:2 | up to 58, 100 | character to `Z/2` (all 20) |
| order3-thompson, order3-transvections | 1:1, 1:2, 2:1, 2:2 | up to 23, 45 | character to `Z/3` (all 8) |
| mixed-all-order3 | 1:1, 1:2, 2:1, 2:2 | up to 60, 138 | no character; permutation images of degree 7, 6, 5, 6 |
| atlas-order2, atlas-order3 | 1:1, 1:2, 2:1 | up to 53, 159 | character to `Z/2` or `Z/3` (all 6) |
| eld1-compressors-order3 | 1:1 | 13, 33 | character to `Z/3` |
| eld1-compressors-order2 | 1:1, 1:2, 2:1 | up to 93, 160 | no character, no coset image of index at most 6; epimorphism onto PSL(3,2), degree 7 |
| eld1-compressors-order3 | 1:2, 2:1 | up to 123, 303 | no character, no coset image of index at most 6; epimorphism onto PSL(3,2), degree 7 |
| eld-full-order2 | 1:1 | 35, 68 | no character; no 2-quotient of class at most 3 (orders 2^140 and 2^1435); the PSL(3,2) search did not finish in 45 minutes; linear image onto GL(4,2), degree 63, from `nine_leaf_corner_rep.py` |

So all 45 windows are dead. In the nine-leaf `E_ij(1)` windows the separating image
is PSL(3,2): the table group sees the corner `GL(3,2)` of the `E_ij(1)`, and the
compressors do not force enough coincidences to kill `x_h` there. The full nine-leaf
window dies in GL(4,2) instead (last reading below). Its witness is
`runs/wit/eld-full-order2-1-1.witness.json`, and `--verify runs/res-c.json` replays it.

## Reading

- **Every window built from Thompson units, transvections and the atlas charts
  dies at once.** An abelian character already separates `h`. The table group of
  a small window has few coincidences, so it is far from perfect.
- **The nine-leaf windows are the first that survive.** The corner group
  `EL_3(F_2) = GL(3,2)` generated by the `E_ij(1)` is perfect, so characters see
  nothing. Its smallest faithful permutation action has degree 7, so coset
  actions of index at most 6 see nothing either. Survival to index 6 is
  therefore weak evidence, which is why stage 2 tests PSL(3,2) quotients
  directly.
- **What survival would mean.** A window inside a finite subgroup `K` of `G`
  realizes in `K` itself and is dead by Corollary 3. The nine-leaf windows contain
  the infinite-order compressors `cu, cv`, so that shortcut does not apply to them.
  A window that survives every finite image presents a non-residually-finite group
  with `x_h` in its finite residual. By
  `strict-automaton-tables-present-an-invisible-window-difference` that group is
  also nonsofic.
- **The full nine-leaf window dies in GL(4,2).** Written over the 32 original
  generators, its 546 relators reduce to 375 distinct words:
  - every `E_ij(r)` is an involution;
  - `E_ij(a), E_kl(b)` commute at positions that are not adjacent (`j != k`, `l != i`);
  - `E_ij(t_k), E_jl(s_m)` commute for `k != m`, since `t_k s_m = 0` in `L_2`;
  - Steinberg relations appear only with `h = E_01(1)`: `[h, E_12(r)] = E_02(r)`,
    `[E_20(r), h] = E_21(r)`, and `[E_02(a), E_21(b)] = h` for `ab in {1, t0 s0, t1 s1}`;
  - `cu, cv` occur only in 4 relators with `h`, so they can be sent to `1`.

  Two natural kinds of image fail:
  - *Nilpotent images.* The relators give `h = [[h, E_12(1)], [E_20(1), h]]`, so
    `x_h` lies in every term of the lower central series. This explains the
    2-quotient failures.
  - *Position-independent elementary matrices over a finite ring `R`.* With
    `p = rho(1)`, the relators force `ps = s = sp`, `pt = t = tp` and
    `t_k s_m = delta_km p` in the finite ring `pRp`. There `t_0 s_0 = p` gives
    `s_0 t_0 = p`, so `t_1 = t_1 s_0 t_0 = 0` and `p = t_1 s_1 = 0`.

  The relators never tie coefficients at different positions together, and they ask
  for `t_k s_k = p` only at the triple `(0,2,1)`. Take `rho_ij(1) = e_00` for
  `(i,j) != (1,0)`, `rho_02(t_k) = rho_12(t_k) = e_0k`,
  `rho_21(s_k) = rho_20(s_k) = e_k0`, and `rho = 0` otherwise, over `M_2(F_2)`. Then
  `E_ij(r) -> 1 + e_ij (x) rho_ij(r)` in `GL_6(F_2)` satisfies all 546 relators, checked
  in Python and in GAP, with `x_h != 1`. The matrices fix `e_1, e_3` and act on the
  span of `e_0, e_2, e_4, e_5`. The image has order 20160, so it is GL(4,2) = A_8.
  At radius `1:1`, then, the Leavitt products are visible at one position triple
  only, and a rank-one corner realizes them. A window protected by Dedekind-finiteness
  would need relators that tie several triples together.
