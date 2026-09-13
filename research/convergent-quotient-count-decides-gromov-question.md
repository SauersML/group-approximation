---
rg: 2
id: convergent-quotient-count-decides-gromov-question
kind: claim
title: If the expected number of finite simple quotients of some finite family of hyperbolic groups is finite, a quotientless hyperbolic group exists
distinct_from:
  random-relators-kill-small-simple-quotients-of-kazhdan-groups: that proves the first moment kills quotients below an exponential threshold and notes the sum diverges above it at fixed relator length; this shows that proving mere convergence of the full sum, with no bound below 1, already decides Gromov's question
  random-complex-group-no-quotients-above-exp-pn: that is the open large-quotient regime for one random model; this is a model-free statement about any finite family of non-elementary hyperbolic groups
  finite-simple-spectrum-gives-quotientless-hyperbolic-group: that is the construction criterion used here; this applies it to averaged quotient counts
---

For a group `Λ` let

```text
X(Λ) = #{ N normal in Λ : Λ/N finite simple }  =  Σ_S #Epi(Λ, S) / |Aut(S)|,
```

where `S` runs over the finite simple groups up to isomorphism, and the equality holds
because `Aut(S)` acts freely on `Epi(Λ, S)`, with orbits the kernels.

**THEOREM (established; unreviewed).**

```text
(C1) If X(Λ) < ∞ for one non-elementary hyperbolic group Λ, then an infinite
     hyperbolic Kazhdan group with no nontrivial finite quotient exists. Through
     hyperbolic-rf-vtf-kazhdan-equivalence, some hyperbolic group is then neither
     residually finite nor virtually torsion-free.
(C2) Let {Λ_x} be a finite family of non-elementary hyperbolic groups with any
     probability weights. If the first moment  E_x X(Λ_x)  is finite, the conclusion
     of (C1) holds. If it is < 1, some Λ_x has no nontrivial finite quotient.
(C3) Contrapositive: if every hyperbolic group is residually finite, then
     X(Λ) = ∞ for every non-elementary hyperbolic Λ, and every such first moment
     diverges.
```

**Why it matters for the triangle target.** The random-edge-identification heuristic in
`hyperbolic-simple-triangle-group-without-finite-quotients` predicts about `|S|^(-χ_orb)`
conjugacy classes of epimorphisms onto `S`, with `χ_orb > 0` for the explicit
candidates. That predicts a convergent `X`. By (C1)–(C2), a rigorous upper bound showing
merely `E_x X(Λ_x) < ∞`, for any finite family of gluings, is already a negative answer
to Gromov's question. So the counting tool is not an easy step followed by a hard
`< 1` step: its "soft" half, convergence, is the whole problem.
- The heuristic is sharp in the other direction too. Take any member with finite
  quotients, for instance the Caprace–Conder–Kaluba–Witzel groups with `PSp_6(p)` or
  `PSL_3(F_q)` quotients. Either it has `X = ∞`, or (C1) already produces a quotientless
  hyperbolic group.
- What a counting proof must therefore control is exactly the large, structured
  quotients: families of Lie type quotients coming from a representation with infinite
  image, and large alternating quotients.

Proof: `convergent-quotient-count-decides-gromov-question-proof`.
