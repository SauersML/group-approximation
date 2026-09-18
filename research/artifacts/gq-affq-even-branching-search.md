# Even branching: Jacobsthal machines exist, but none of those found is globally 2-adic (lane gq-affq, 2026-09-18)

**Question.** Is there a SMART-format reversible machine whose induced map has a height-2 (or height-2m′)
renormalization? That would give `BS(1,2)` or `BS(1,2m′)` in `3V`. By `crossing-move-hierarchies-have-odd-branching`,
an even hierarchy needs return moves. Class split with bh-free-18: I take two-shape machines with more symbols and
tables that are **not mirror-symmetric**. The earlier gq-nv-obstruct searches were mirror-symmetric or had 2
symbols.

**Tools** (MSI, single core, C; all calibrated on SMART):
- `even_dfs.c`: lazy DFS. It accepts even `b` with a periodic correction, `T(L+1) = b T(L) + c_(L mod p)`,
  `p ≤ 3`. With `NOMIR=1` a rule may depend on the direction. Calibration: with odd `b` allowed it reports SMART
  (`b = 3`, period 1).
- `types.c`: per-type step counts per level, fitted exactly by `a 2^L + b (−1)^L + c L + d`.
- `ysubsets.c`: every subset `Y` of local types (state, source symbol, target symbol) with `N_Y(L+1) = 2 N_Y(L)`
  exactly for `L ≥ 4`, and a maximal gap between `Y`-steps that does not grow from level 10 to level 13.
- `percheck.c`: periodicity on random tapes. Calibration: SMART gives 0/20 periodic.
- `eig2.c`: locally readable eigenvalues of `S = F_Y` on random tapes. Calibration: SMART in 4-state form gives
  `Z/2` at `r ≥ 0`, `Z/3` at `r ≥ 1`, `Z/9` at `r ≥ 2`, and never `Z/4`.

**Results, class 2 shapes × 3 symbols, non-mirror** (5.3M DFS nodes).
1. **Exact even timing exists.** 140 partial tables have `b = 2` with a period-2 correction. The smallest use
   only the symbols `{0,1}` and 4 states. Their first-arrival times are exactly the Jacobsthal numbers
   `1, 11, 21, 43, 85, 171, 341, …`, i.e. `T(L+1) = 2T(L) ± 1`. This is the scheme gq-nv-obstruct predicted.
2. **Exact binary inducing sets exist along the hierarchy.** For the smallest table the fit gives `a = 1/6` for
   every type, with linear coefficient `c ∈ {−1/2, 0, 1/2}`. 976 subsets `Y` give `N_Y(L+1) = 2N_Y(L)` exactly,
   with maximal gap 3 to 10 steps, not growing with the level. So the "linear walk" is spread over types that a
   local `Y` can skip.
3. **None of those tested is globally 2-adic.**
   - Of the 140 tables, 42 hit undefined pairs on random tapes (partial tables), and most of the others fall into
     periodic cycles.
   - 11 are fully defined and show no detected cycle. Of these, 8 have a good `Y`.
   - For all 8, on random tapes: `Y` still has bounded return (maximal gap 3 or 4), but **no** eigenvalue
     `−1, i, e^{2πi/8}` or `e^{2πi/3}` is locally readable at radius ≤ 5. The mean return gaps are exactly 16/9 or
     8/3, a sign of rigid, possibly periodic, random-tape dynamics.
   - By `renormalization-heights-force-eigenvalue-roots`, a height-2 renormalization of `S` needs all 2-power roots
     of unity as continuous eigenvalues. Continuous eigenfunctions on a Cantor set are locally constant, so they
     are read at some finite radius. The test at radius ≤ 5 therefore does not exclude them, but it finds nothing.

**Reading.** The Jacobsthal hierarchy of gq-nv-obstruct's parity analysis is realized by small non-mirror
machines, with bounded-gap exact binary inducing sets along the hierarchy run. What fails is **global**
structure: off the special tapes these machines do not behave like odometers. SMART and `SMART_m` are aperiodic,
with every configuration inside the move hierarchy. A binary analogue needs the same property, which none of the
machines found has.

**Not run** (compute budget): non-mirror classes `2×4`, `3×3` and larger. The pipeline
`even_dfs → percheck → ysubsets → eig2` runs unattended and is ready for them.

**Periodic points kill a table outright.** `odometer-factor-witnesses-mix-coordinates` shows that an odometer-factor
witness has no periodic points, because `Z_m` is torsion-free.
- A renormalization of any height gives such a factor (`renormalizable-thompson-elements-are-odometer-codes`).
- If `Y` has bounded return, every `F`-orbit meets `Y`, so a periodic point of the moving-tape map `F` gives a
  periodic point of `S = F_Y`.
- `percheck.c` detects an exact repeat: the head stays inside a window of width ≤ 64, and the window contents,
  state and head offset recur, while the tape outside the window is untouched. That is a genuine periodic point
  of `F`, up to hash collisions.

So every table with a detected cycle is excluded for every height and every bounded-return `Y`; the eigenvalue
test is not needed for them. Undefined pairs in partial tables are a separate issue. A useful search needs
**aperiodic** reversible machines, as SMART and `SMART_m` are (Kari–Ollinger aperiodicity). Periodic points are
semi-decidable, so they make a cheap first filter.
