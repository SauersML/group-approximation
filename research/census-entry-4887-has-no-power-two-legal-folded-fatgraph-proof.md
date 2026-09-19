---
rg: 2
id: census-entry-4887-has-no-power-two-legal-folded-fatgraph-proof
kind: route
title: Relax the memory-two polygon LP by letting d^+ darts of different blocks remember different amounts, prove every legal fatgraph still projects to it, and refute it by an exact dart-shifted Farkas vector
target: census-entry-4887-has-no-power-two-legal-folded-fatgraph
requires:
  - power-two-word-free-census-of-power-one-silent-classes
  - legal-f-folded-fatgraphs-give-surface-subgroups
  - positive-f-folded-fatgraphs-have-only-even-valence
artifacts:
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_brute.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/sp_vmem.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vchain2.sh
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_m2_4887_rm2_rpa2b1c1.json
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_m2_4887.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_vmem_brute_m2_4887.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4887_rm2_rpa2b1c1_round0.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4887_rm2_rpa2b1c1_round1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4887_rm2_rp1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/vcg_m2_4887_rm3_rp1.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/sp_vmem_m2_4887_masks.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/validate_vmem_certificates.log
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_memory.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/lp_allwords.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/cg_memory.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/farkas_rho.py
  - experiments/legal-f-folded-fatgraphs-2026-09-17/verify_farkas_memory.py
---

**Notation.** The conventions are those of `lp_allwords.py` and `lp_memory.py`, which are the conventions of
`power-two-word-free-census-of-power-one-silent-classes`.

- `phi` is entry 4887, `a -> ab, b -> bbca, c -> aab`. `f` is its rose map, and `g = f^2` is the rose map of `phi^2`.
- Upper case letters are inverses. `L = {a, b, c, A, B, C}`.
- A turn `(x, y)` is legal when `y != x^{-1}` and `x^{-1}` and `y` lie in different gates of `Dg`.
- `R(x) = g(x)^{-1}` is the block of `x`. For entry 4887 the blocks of `a, b, c` have 6, 13 and 8 letters.

A legal `g`-folded fatgraph `X` has two boundaries, as in `legal-f-folded-fatgraphs-give-surface-subgroups`:

- `partial^-`, a nonempty finite set of cyclically legal cyclic words `w = x_1 ... x_L`;
- `partial^+`, whose circle for `w` reads the blocks `R(x_L) ... R(x_1)`.

**Darts.** The darts of `X` are of two kinds:

- a `d^-` dart for each letter occurrence `x_j` of `partial^-`, labelled `x_j`;
- a `d^+` dart for each letter `i` of each block occurrence `R(x_j)`, labelled `R(x_j)[i]`.

`nxt(d)` is the next dart along its boundary circle, and `p` is the edge pairing of `X`. `p` is a fixed-point-free
involution with `label(p(d)) = label(d)^{-1}`.

Each vertex of `X` is an orbit of `d -> nxt(p(d))`. It is a cyclic list of slots `(d_s, p(d_s))` with
`d_{s+1} = nxt(p(d_s))`, and every dart is the `d_s` of exactly one slot.

The conditions that the conventions put on each vertex depend only on labels and on the kind of dart
(`-` or `+`, and whether it is the first dart of a block):

1. its directions lie in distinct gates;
2. at most one `d_s` is a `d^-` dart;
3. no slot pairs two `d^-` darts;
4. a vertex containing an `f`-dart (the first dart of a block) is a 2-gon, and it contains only one.

The valence is at most `2 min(g_+, g_-)`, by the gate bound of
`positive-f-folded-fatgraphs-have-only-even-valence`. Here that bound is `maxval = 4`.

**Step 1: reduction to power one for `phi^2`.** Steps 1 and 2 of
`power-two-word-free-census-of-power-one-silent-classes-proof` give two facts.

- A legal `f^2`-folded fatgraph is a legal `g`-folded fatgraph for the rose map `g` of the positive automorphism
  `phi^2`.
- `det(I - M^2) != 0`. So `[partial^-] = 0` in `H_1` of the rose: `X` bounds, which gives
  `[partial^-] + [partial^+] = 0` and `[partial^+] = -M^2 [partial^-]`.

It remains to show that no legal `g`-folded fatgraph exists.

**Step 2: the mixed-memory LP.** Fix memories:

- `r_-(x) = 2` for every letter `x`;
- `r_+(a) = r_+(A) = 2`, and `r_+(x) = 1` for `x` in `{b, B, c, C}`.

Set `R = 2`. A window is a legal path `v = (v_0, v_1, v_2)`, with both turns legal. There are 114 windows.

The dart types are:

- `('-', v)`, where `v` is a legal path of `r_-(v_0) + 1` letters. It stands for a `d^-` dart reading `x_j`, with
  `v = (x_j, ..., x_{j + r_-(x_j)})` (the letters ahead).
- `('+', v, i)`, where `v` is a legal path of `r_+(v_{last}) + 1` letters and `0 <= i < |R(v_{last})|`. It stands
  for dart `i` of the block `R(x_j)`, with `v = (x_{j - r_+(x_j)}, ..., x_j)` (the letters behind).

A type's label, kind and `f`-dart flag depend only on `v_0`, or on `v_{last}` and `i`. There are 524 types.

The successor sets (`lp_vmem.VTypes.succ`) contain every coarse context consistent with what the dart
remembers:

- `('-', v)` goes to every `('-', u)` with `(v_0, u_0)` legal and `u`, `v[1:]` agreeing on their common prefix.
- `('+', v, i)` goes to `('+', v, i + 1)` when `i + 1 < |R(v_{last})|`.
- From the last dart of its block, `('+', v, i)` goes to every `('+', u, 0)` with `(u_{last}, v_{last})` legal and
  `u`, `v[:-1]` agreeing on their common suffix.

The variables are `y_P >= 0` for each typed polygon `P` and `c_w >= 0` for each window `w`. The typed polygons
are the cyclic lists of slots `(d_s, q_s)` of types that satisfy four conditions:

- `label(q_s) = label(d_s)^{-1}`;
- `d_{s+1}` is in `succ(q_s)`;
- conditions 1 to 4 above hold;
- `2 <= k <= maxval`.

Each polygon is written in its rotation with the smallest type first (`lp_memory.polygons`).

The rows are:

- **type rows**: for each type `tau`, `sum_P y_P #{s : d_s = tau} - sum_{w in tw(tau)} c_w = 0`. Here
  `tw('-', v)` is the set of windows `w` with `w[: r_-(w_0) + 1] = v`, and `tw('+', v, i)` is the set of windows
  with `w[R - r_+(w_2):] = v`.
- **pair rows**: for each unordered pair `{tau, sigma}` of types, `sum_P y_P (#{s : (d_s, q_s) = (tau, sigma)} -
  #{s : (d_s, q_s) = (sigma, tau)}) = 0`. Here `tau != sigma` always, because the two labels are inverse.
- **circulation rows**: for each legal 2-letter path `u`, `sum_{w[:-1] = u} c_w - sum_{w[1:] = u} c_w = 0`.
- **homology rows**: for each letter `x` in `{a, b, c}`, `sum_w c_w eps_x(w_0) = 0`. Here `eps_x(x) = 1`,
  `eps_x(x^{-1}) = -1`, and `eps_x` is 0 on other letters.
- **normalisation**: `sum_w c_w = 1`.

This is `lp_vmem.build` together with the normalisation row of `vcg.py`. With `r_+ = 2` for every letter it is
exactly the memory-2 LP of `lp_memory.py`.

**Step 3: every legal `g`-folded fatgraph projects to a feasible point.** Let `X` be one, and let `n` be the total
length of `partial^-`. It is positive because `partial^-` is nonempty. Give each dart its type:

- a `d^-` dart reading `x_j` gets `('-', (x_j, ..., x_{j + r_-(x_j)}))`;
- dart `i` of the block `R(x_j)` gets `('+', (x_{j - r_+(x_j)}, ..., x_j), i)`.

Indices run cyclically in the word, and the paths are legal because the words are cyclically legal. Set
`c_w = (number of cyclic occurrences of w in partial^-) / n`, and `y_P = (number of vertices of type P) / n`.

(a) *Successors.* Let `q` be a dart and `nxt(q)` the next dart on its circle. Then the type of `nxt(q)` lies in
`succ(type(q))`.

- If `q` is a `d^-` dart reading `x_j`, then `nxt(q)` reads `x_{j+1}`. Both types are initial segments of the same
  sequence `x_{j+1}, x_{j+2}, ...` after their first letter, so they agree on common prefixes, and `(x_j, x_{j+1})`
  is legal.
- If `q` is dart `i` of `R(x_j)` and not the last dart of the block, then `nxt(q)` is dart `i + 1` of the same block,
  with the same `v`.
- If `q` is the last dart of `R(x_j)`, then `nxt(q)` is the first dart of `R(x_{j-1})`, since the `partial^+` circle
  of `w` reads `R(x_L) ... R(x_1)`. Its path `u` ends at `x_{j-1}`, and `v[:-1]` also ends at `x_{j-1}`. Both are
  final segments of `..., x_{j-2}, x_{j-1}`, so they agree on common suffixes. The turn `(u_{last}, v_{last})` is
  `(x_{j-1}, x_j)`, which is legal.

(b) *Vertices.* The slot list of a vertex, `(d_s, p(d_s))` with `d_{s+1} = nxt(p(d_s))`, maps to a list of types.

- It has `label(q_s) = label(d_s)^{-1}`, and by (a) `d_{s+1}` is in `succ(q_s)`.
- Conditions 1 to 4 and `k <= maxval` hold in `X`, and they depend only on data the types keep.

So each vertex is a typed polygon of the LP. By condition 1 its darts have distinct labels, hence distinct types,
so it has a unique rotation with the smallest type first.

(c) *Type rows.* Every dart is the `d_s` of exactly one slot. So `sum_P y_P #{s : d_s = tau}` is `1/n` times the
number of darts of type `tau`.

- A `d^-` dart reading `x_j` corresponds to the occurrence of the window `(x_j, x_{j+1}, x_{j+2})`. Its type is
  `('-', v)` exactly when that window is in `tw('-', v)`.
- Dart `i` of `R(x_j)` corresponds to the occurrence of the window `(x_{j-2}, x_{j-1}, x_j)`, and its type is
  `('+', v, i)` exactly when that window is in `tw('+', v, i)`.

Both correspondences are bijections, so every type row holds.

(d) *Pair rows.* `p` is an involution, so the slots `(d, p(d))` with `d` of type `tau` and `p(d)` of type `sigma`
are in bijection with those of type `(sigma, tau)`, by `d -> p(d)`.

(e) *Circulation, homology and normalisation.* These rows involve only `c`, which is the memory-2 flow of
`lp_memory.py`.

- Each cyclic occurrence of a 2-letter path is preceded by one letter and followed by one letter, which gives the
  circulation rows.
- `sum_w c_w eps_x(w_0)` is `1/n` times the `x`-coordinate of `[partial^-]`, which is 0 by Step 1.
- `sum_w c_w = 1` because there are `n` window occurrences.

So `(y, c)` is feasible. Only the successor sets and the type rows differ from `lp_memory.py`, and (a) and (c)
check both.

Code note: `lp_vmem.py` first tested `(u_{last}, v_0)` in place of `(u_{last}, v_{last})` in the third successor
rule, and it now tests `(u_{last}, v_{last})`. For entries 4887 and 4012 the two successor relations
coincide, which was checked by comparing the sets. The reason is that the illegal turns of `phi^2` form a set closed
under reversal, and every `r_+ <= 2`.

- For `r_+ = 1` the old test is `(x_{j-1}, x_{j-1})`, which is always legal.
- For `r_+ = 2` it is the reverse of the legal turn `(x_{j-2}, x_{j-1})`.

`farkas_vmem_m2_4887.log` records the certificate check under the corrected code.

**Step 4: the Farkas lemma.** Write the LP as `A y + B c = e_norm` with `y, c >= 0`. Let `z` assign a number to
every row. Suppose that:

- every typed polygon has charge `(A^T z)_P <= 0`;
- every window has charge `(B^T z)_w <= 0`, where `B` includes the normalisation entry `+1`;
- the normalisation row has `z_norm > 0`.

Then a feasible point would give `0 < z_norm = z . (A y + B c) = sum_P y_P (A^T z)_P + sum_w c_w (B^T z)_w <= 0`,
which is impossible. So the LP is infeasible. By Step 3, no legal `g`-folded fatgraph exists, which proves the
claim.

**Step 5: the vector and its checks.** `farkas_vmem_m2_4887_rm2_rpa2b1c1.json` stores integers `zrows` (type
rows, then circulation and homology rows) and `zpairs` (pair rows; absent pairs have `z = 0`), with `D = 10^6`.
The row layout is that of `lp_vmem.build(TY, [])`, with pair rows keyed by type pairs.

- **Dart shift.** Both checkers first compute `R_d = max(0, max over polygons P through d of ceil(charge(P)/|P|))`
  and set `z'_d = z_d - R_d` on type rows. Every polygon through `d` loses at least `ceil(charge/|P|)` at each
  of its `|P|` darts, so its new charge is at most 0. The checkers do not deduce this; they recompute it.
- **Normalisation.** They set `z'_norm = -max_w (charge of window w on the other rows)`, so every window charge is
  at most 0, and they require `z'_norm > 0`.
- **`farkas_vmem.py` (max-plus).** It uses `farkas_rho.dart_max_charge` for `R` and
  `verify_farkas_memory.max_polygon_charge` for the re-check. The latter is exact max-plus over all cyclic typed
  sequences of length 2 to 4 that satisfy the gate, sign and `f`-dart conditions, which is a superset of the
  polygons. All values are integers below `2^52`, which is asserted, so float arithmetic is exact.
- **`farkas_vmem_brute.py` (enumeration).** It walks every typed polygon one at a time, with the enumeration of
  `lp_memory.polygons`, in Python integers. It makes two passes: first `R`, then the shifted charges.

Both give 176 shifted darts with maximum shift 29714, maximum polygon charge 0, maximum window charge 0, and
`z'_norm = 65944`, which is `0.065944 D`. The outputs are `FARKAS VERIFIED` (`farkas_vmem_m2_4887.log`) and
`BRUTE FARKAS VERIFIED` (`farkas_vmem_brute_m2_4887.log`). Rerun them with:

- `python3 farkas_vmem.py farkas_vmem_m2_4887_rm2_rpa2b1c1.json`
- `python3 farkas_vmem_brute.py farkas_vmem_m2_4887_rm2_rpa2b1c1.json`

**Step 6: how the vector was found.** This step is not load-bearing: Steps 3 to 5 are the proof.

`vcg.py` is `cg_memory.CGM` with two changes: the row builder is `lp_vmem.build`, and the window sums in the dart
bound use `tw`. It is column generation, with an IPM master and exact min-plus pricing over typed polygons.

- **Round 0** (`vcg_m2_4887_rm2_rpa2b1c1_round0.log`) stopped at the 1080 s limit with phase-1 value 0.1146.
- **Round 1** reloaded the columns (`vcg_m2_4887_rm2_rpa2b1c1_round1.log`). Phase 1 fell to 0.097451 with min
  reduced cost -0.12.
- The final master dual, rounded at `D = 10^6` and dart-shifted as in Step 5, already has `z'_norm > 0`. The float
  dart bound of the run was still negative, at -0.70. The exact per-dart shift is sharper than the float bound
  over the whole run, because it takes each dart's maximum over its own polygons.

The driver `vchain2.sh NAME PHI0 rm rp rounds` chains such rounds and runs `farkas_vmem.py` after each one.

**Dead ends recorded.** These are float column-generation values, not claims.

- **`(r_-, r_+) = (2, 1)`** (`vcg_m2_4887_rm2_rp1.log`) reaches phase 2 at objective `-1/2`, with flow on
  `{a, b}` windows. So `d^+` memory 1 for every letter is too coarse.
- **`(3, 1)`** (`vcg_m2_4887_rm3_rp1.log`, two rounds concatenated) is the same, so more `d^-` memory does not
  compensate.
- **Support propagation.** `sp_vmem.py` is the exact support propagation of `sp_mask.py`, adapted to the coarse
  types (`sp_vmem_m2_4887_masks.log`). With the `{a, b}` mask, `r_+ = a1b1c2` leaves 12 windows alive, while
  `a2b1c1`, `a1b2c1`, `a2b1c2`, `a2b2c1` and `a1b2c2` kill every window.
- **The choice of `a2b1c1`.** It is the smallest of those, with 524 types. It gives memory 2 to `a`, whose
  `f^2`-block `abbbca` is the shortest. Under the same mask it also kills the `{b, c}` windows, and it leaves 8 on
  `{a, c}`.

**Validation of the projection on real certificates.** `validate_vmem_certificates.log` records `lp_vmem.py
--validate`. The run takes each certified power-two fatgraph of `surfaces_m2_census` and checks four things:

- every dart's type has the right label;
- the type of the next dart is in `succ`;
- every vertex is an enumerated typed polygon;
- all rows balance.

It covers entries 4052, 4011 and 3684 under several memory choices, and reports 0 failures and no nonzero rows.
The exact choice `(2, a2b1c1)` of this proof was checked on entry 4052, since the 4011 run exceeded the 2 GB limit.
This tests Step 3; it does not replace it.

**Scope.**

- The float solver only proposes `z`. Every inequality in Step 4 is checked exactly, twice, by different
  enumerations.
- The result is about legal `f^2`-folded fatgraphs over the rose. It says nothing about powers `m >= 3`, or about
  surface subgroups found by other methods.
