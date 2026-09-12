---
rg: 2
id: stw99-problem-lvi-untwisting-cocycle-actions
kind: claim
title: Determine when strongly outer cocycle actions on classifiable algebras untwist (STW Problem LVI, Shlyakhtenko)
root: true
artifacts:
  - research/artifacts/stw99-actions-classification-cluster-2026-08-30.md
---

**Problem LVI of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Shlyakhtenko's challenge).  When is a strongly outer cocycle action
of a countable discrete amenable group on a classifiable algebra
cocycle conjugate to a genuine action, in terms of `K`-theoretic data
of the algebra and cohomological data of the group?  Von Neumann
model: ALWAYS untwists (Popa 2021, outer cocycle actions of amenable
groups on any II₁ factor).  C*: non-untwistable examples exist
(Izumi--Matui 8.19/8.20); Matui--Sato untwist `Z^2` on UHF/`Z` under
conditions and all Klein-bottle-group strongly outer cocycle actions
on `Z`.

## Attempts

* The shape of the expected answer is visible in the known cases: the
  obstruction of a cocycle action lives in
  `H^2(G, U(∞)-homotopy data)` mapped into the algebra's
  `K`-theoretic receptacle (for `Z^2`: a single `K_0`-valued Chern
  class of the commutator cocycle, which is what Matui--Sato's
  condition tests; Izumi--Matui's non-untwistable examples have
  nontrivial such class with torsion receptor).  Conjecture-shaped
  record: a strongly outer cocycle action untwists iff the induced
  class in `H^2(G, K_0(A) ⊗ (torsion data))`-type receptacle
  vanishes; Popa's theorem is the statement that the von Neumann
  receptacle is always trivial (`U(R)` contractible-like), so the
  entire phenomenon is non-stable K-theory of the coefficients —
  linking this problem to the K1-injectivity cluster: the receptacle
  is trivial exactly when enough unitary groups are connected, and
  Jiang's K-stability of `Z`-stable algebras is why `Z`-coefficient
  cases are the tractable ones.
