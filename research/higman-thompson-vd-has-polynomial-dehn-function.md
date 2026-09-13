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
