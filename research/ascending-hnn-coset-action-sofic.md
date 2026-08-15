---
rg: 2
id: ascending-hnn-coset-action-sofic
kind: claim
title: The coset action of an ascending HNN skeleton is sofic when the fiber is
distinct_from:
  coordinate-action-not-sofic: That claim is a NEGATIVE soficity statement about a specific coordinate action; this is the positive open question for the lean ascending-HNN coset action, whose amenability is classical (Monod--Popa).
  marked-quotients-not-lef: That claim is a negative LEF statement about marked quotients; this is a positive soficity question about the coset ACTION of the lean HNN skeleton, feeding the sofic-plus-non-MF headline.
artifacts:
  - research/artifacts/unified-mf-compression-external-2026-08-15.md
---

OPEN.  Let Gamma be residually finite (or just sofic) and G =
<Gamma, t> the ascending HNN extension along a proper self-embedding.
Two layers:

- The GROUP G is sofic unconditionally from sofic Gamma: N = the
  directed union of t^{-n} Gamma t^n is a directed union of copies of
  Gamma (soficity passes to directed unions), and G = N x| Z is
  sofic-by-amenable (Elek--Szabo).  No open input here.
- The ACTION G on G/Gamma: amenable with explicit Folner sets by
  Monod--Popa (arXiv math/0301348, Prop 2; C. R. Acad. Sci. Canada 25
  (2003) 82-87 — same paper whose co-amenability counterexample lives
  in exactly this skeleton family).  Question: is the action sofic in
  the near-action sense consumed by the repo's
  `isSofic_iff_admitsEssentiallyFreeNearAction` framework?  If yes
  with Gamma residually finite, the finite-order-lamp wreath over
  G/Gamma is sofic AND non-MF (by [[multi-mover-collapse-criterion]]),
  giving the sofic non-MF headline through the simplest possible
  skeleton, with G far from (T) (it surjects onto Z) — a clean
  contrast to the Kun--Thom examples.

Candidate route: lane-5 telescope-window machinery transplanted —
finite-index windows in each t^{-n} Gamma t^n give finite quotient
actions of HNN truncations; Monod--Popa's Folner structure patches
the windows equivariantly.  Should be EASIER than the E-soficity lane
(no Clifford kernel to carry).  Raised by Fournier-Facio (email,
2026-08-15).

## Attempts

None yet; the lane-5 window route above is the recorded attack.
