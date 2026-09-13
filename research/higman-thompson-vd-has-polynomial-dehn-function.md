---
rg: 2
id: higman-thompson-vd-has-polynomial-dehn-function
kind: claim
title: The Higman–Thompson groups V_d have polynomially bounded Dehn function
distinct_from:
  thompson-v-dehn-function-is-at-most-sextic: that is the case d = 2, imported from an unrefereed preprint; this asks for every d >= 2, and the BS(1,2) route needs d = 10.
artifacts:
  - research/artifacts/solve-bh-poly-dehn-2026-09-13.md
---

**OPEN.** For every `d >= 2`, the Higman–Thompson group `V_d = V_d({1})` has
a polynomially bounded Dehn function.

**Known.**
- `d = 2`: `δ_V ≼ n^6` (`thompson-v-dehn-function-is-at-most-sextic`,
  unrefereed), and `δ_V ≼ n^11` (Guba 2000, as cited by Zaremsky
  arXiv:2305.15176, TeX l.114).
- Zaremsky, TeX l.114, verbatim: "Presumably, close relatives like the
  Higman--Thompson groups $T_d$ and $V_d$, which are virtually simple, also have
  polynomial Dehn functions, using similar arguments."
- The Higman–Thompson groups `T_n` have quadratic Dehn function
  (arXiv:2410.23088, abstract TeX l.19). That covers `T_n`, not `V_n`.

No source found here proves a polynomial bound for `V_d` with `d >= 3`.

## Attempts

- **Literature (lane solve-bh-rn-dehn, 2026-09-13).** arXiv listing searches returned only arXiv:2410.23088 (abstract: "all the Higman-Thompson groups $T_n$ have quadratic Dehn function") and arXiv:2608.03813 (`n^6` for V only). No source found covers `d >= 3`. Not exhaustive. Details: `research/artifacts/solve-bh-rn-dehn-2026-09-13.md` §1.
- **T_d does not transfer.** `T_d <= V_d`, and Dehn functions pass neither to subgroups nor overgroups. Migliorini's bounded non-F normal form is dead for V by `thompson-v-elements-need-unboundedly-many-non-f-letters`; the same break count on `d`-ary cones should kill it for every `V_d` (hand remark, not checked).
- **Stein–Farley push-down: stops at an additive descending-link lemma.** Loops of length `L` in the truncation fill in the CAT(0) complex with at most `L^2/4` squares at heights `<= k + (d−1)L/2` (standard minimal-diagram facts, sketched). Pushing down through descending links over `O(L)` levels only gives an exponential bound, because per-level costs multiply. The missing input is a quantitative descending-link filling lemma with additive cost. See `research/artifacts/solve-bh-rn-dehn-2026-09-13.md` §3.
- **Projection instead of push-down (lane solve-vd-dehn-filling, 2026-09-13).** Projecting the CAT(0) filling through the canonical lexicographic projection `r` loses only a polynomial factor: `δ_(V_d)(L) <= C·L + C·L^2·max_{n <= k_0 + C·L} A_d(n)`, with `A_d(n)` the area of the standard square words (`vd-dehn-bounded-by-standard-square-word-area`, pending two OPEN imports). So the multiplicative push-down cost is not forced. The route `vd-poly-dehn-via-square-word-projection` wires this in; what remains is `vd-standard-square-words-have-polynomial-area`, the `d`-ary analogue of Lorrain's π-word lemmas. Lorrain's `d = 2` method is pinned from the TeX in `research/artifacts/solve-vd-dehn-filling-2026-09-13.md` §1.
