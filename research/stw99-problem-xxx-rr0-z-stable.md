---
rg: 2
id: stw99-problem-xxx-rr0-z-stable
kind: claim
title: Simple nuclear real rank zero algebras are Z-stable (STW Problem XXX)
root: true
distinct_from:
  stw99-problem-xxix-rr0-dichotomy: that only asks to exclude the mixed finite/infinite phenomenon; this asks for full Jiang--Su absorption from real rank zero, and implies it via Kirchberg's dichotomy (route stw99-xxx-implies-xxix).
  stw99-problem-xxi-tracial-rr0-implies-gamma: that assumes real rank zero of the TRACIAL ULTRAPOWER of the tracial completion and asks only for uniform property Gamma; this assumes real rank zero of the algebra itself and asks for Z-stability.
artifacts:
  - research/artifacts/stw99-rr0-cluster-2026-08-30.md
  - research/artifacts/stw30-quantum-expander-centralization-firewall-audit-2026-08-30.md
---

**Problem XXX of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Is
every simple separable nuclear non-elementary C\*-algebra with real
rank zero automatically `Z`-stable?  STW: serious attempts to build a
Villadsen-type RR0 non-`Z`-stable example have failed, and it is
unclear whether any variant can work.

## Attempts

* Stronger central form (Perera--Rordam):
  `perera-rordam-rr0-approximately-divisible` — RR0 non-type-I
  algebras are weakly divisible (PR Thm 5.8), and the question whether
  simple nuclear RR0 forces APPROXIMATE divisibility implies this
  problem through Toms--Winter (CJM, Thm 2.3: approximately divisible
  ⟹ `Z`-stable in this class); route
  `stw99-pr-approx-divisible-implies-xxx`.
* The unique-trace stable-rank-one cell is exactly solved: under those
  hypotheses plus RR0, `Z`-stability ⟺ `K_0` weakly unperforated
  (`stw25-real-rank-zero-k0-perforation-is-exact-obstruction`).  So a
  Villadsen-type counterexample in that cell needs `K_0` perforation
  coexisting with RR0, sr1 and one trace: perforation of purely
  cohomological origin whose pairing image is nevertheless dense — the
  known perforation machines (coordinate Euler mass, mod-`ell` Chern
  thresholds of the XXVII lane) produce sparse projection lattices,
  and no construction with dense `ρ(K_0)` and surviving perforation
  exists.  Sharp target: EITHER a Villadsen system engineered so that
  perforated classes hide in the kernel of `ρ` while trivial summands
  make `ρ(K_0)` dense (refuting XXX), OR a theorem that dense pairing
  image plus weak divisibility washes out perforation under the RR0
  spectral-cutting supply (proving the sr1 unique-trace cell).
* Weak divisibility (free, from PR) vs approximate divisibility (needed)
  is again a pure CENTRALIZATION gap, the same shape as Problem
  XXVIII's order-zero centralization and XXI's selection: RR0 supplies
  the objects, centrality is the open half.
  This gap cannot be crossed from weak-divisibility and RR0 data alone:
  `stw30-quantum-expander-weak-divisibility-centralization-no-go` constructs
  a real-rank-zero matrix corona with endpoint blocks at every scale but a
  fixed finite packet whose relative commutant contains no unital
  `M_2 direct_sum M_3`.  The example is outside the conjecture's simple,
  separable, nuclear class.  It shows that some additional structural or
  uniform-selection input is indispensable, without deciding which missing
  hypothesis supplies it.
