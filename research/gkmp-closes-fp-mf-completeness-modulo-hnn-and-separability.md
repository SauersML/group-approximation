---
rg: 2
id: gkmp-closes-fp-mf-completeness-modulo-hnn-and-separability
kind: claim
title: GKMP permanence reduces the finite-presentation MF-completeness to an HNN form plus separability of a benign subgroup
distinct_from:
  fp-mf-completeness-wall-is-route-independent: that showed every engine meets one product edge with no tool available; this records that a tool now exists and states the two precise conditions under which it closes the prize.
  digit-edge-mf-is-a-free-entropy-model-uniqueness-question: that read the edge as possibly-open by a free-entropy obstruction to soft methods; this observes that GKMP's hard method bypasses that obstruction, so the pessimistic reading is corrected.
---

With [[gkmp-amalgam-product-mf-permanence]] available, the finite-presentation
`Pi^0_2`-completeness of MF
([[mf-recognition-finite-presentations-is-pi2-complete]]) follows from two
conditions on a Higman compiler run on the two-generator bridge
[[bidirectional-hnn-bridge-trivial-value-is-residually-finite]]:

```text
(HNN)  an HNN / stable-letter form of GKMP Theorem 1.1: the rope output
       < G x C, s | s(l,1)s^-1 = (l, phi(l)), l in L >  is MF when G is MF,
       G exact, L <= G separable, C residually finite MF; equivalently the
       rope output embeds in an amalgam G' *_{H'} (H' x C) meeting Thm 1.1.
(SEP)  the benign subgroup L of the ambient G is separable in G.            (GK1)
```

The remaining ingredients are already in hand or automatic:

* **`G` MF.**  The ambient is a machine group; the modular-machine engine is
  MF ([[modular-machine-boone-group-is-mf]]).
* **`G` exact.**  `G` is built from `BS(1,m)` (amenable, exact) and free
  groups by HNN extensions and amalgams over exact (indeed free/cyclic)
  subgroups; exactness is closed under both, so `G` is exact and (SEP)'s
  overgroup is exact, satisfying the exactness hypothesis of Theorem 1.1
  outright.
* **`C` residually finite MF on `INF`.**  `C = B2(1)` is residually finite
  ([[bidirectional-hnn-bridge-trivial-value-is-residually-finite]]), hence MF.
* **`E <= C` on `FIN`.**  The switch embeds `E`, so the output is non-MF.

## The convergence that makes (SEP) plausible

Chiodo--Vyas (*Torsion, torsion length and finitely presented groups*, Camb.
repos.) show the Aanderaa--Cohen Higman construction can be taken to output a
finitely presented **word-hyperbolic, virtually special** group (their
Theorem 6.10 region).  In a virtually (compact) special group every
quasi-convex subgroup is separable (Haglund--Wise); this is exactly the
mechanism GKMP use for their Corollary 1.4 (`pi_1` of hyperbolic
`3`-manifolds).  So (SEP) reduces to arranging the benign subgroup `L` to be
quasi-convex in a virtually special ambient, which the Chiodo--Vyas form of
the construction makes available.

## What remains, precisely

Only (HNN) is a genuinely new mathematical step, and it is a permanence
question for the **same** product data as GKMP Theorem 1.1 with a stable
letter in place of the amalgam.  The GKMP method (selflessness / `C*`-free
independence) is not tied to the amalgam form and their own
`G *_H (H x Z) ≅ (*_H G) ⋊ Z` remark already produces a mapping-torus /
HNN-type object; adapting it to the rope's `graph(phi)` edge is the open
step.  This **supersedes** the "possibly false / genuinely open" reading of
[[digit-edge-mf-is-a-free-entropy-model-uniqueness-question]]: the
free-entropy obstruction only blocks soft distribution-matching, which
GKMP's hard free-independence argument does not use.

## Attempts

The digit/shift edges were shown incompatible with finite quotients
([[c-free-aanderaa-rope-is-mf-with-fine-quotients]]); GKMP bypasses finite
quotients entirely.  The remaining task is not another obstruction audit but
an adaptation of the GKMP proof to the HNN edge, which is analytic work of
the same character as their Section 3--6 and is the correct next attack.
