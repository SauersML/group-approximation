---
rg: 2
id: stw99-problem-lxi-properly-infinite-k1-injective
kind: claim
title: Properly infinite unital C*-algebras are K1-injective (STW Problem LXI, Blanchard-Rohde-Rordam)
root: true
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
---

**Problem LXI of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Blanchard--Rohde--Rordam; implicitly Rordam's Crelle hypotheses;
Kirchberg's squeezing property was invented for it).  Are all properly
infinite unital C\*-algebras `K_1`-injective?  BRR reduce it to the
single algebra `O_∞ * O_∞` (full unital free product); properly
infinite algebras are always `K_1`-surjective (Cuntz).

## Attempts

* Szabo's January 2026 solution of KK-uniqueness
  (`stw99-problem-lxii-kk-uniqueness`) went AROUND this problem
  (Cuntz--Higson multiplier-algebra features), and STW note it does
  not touch LXI — so LXI is now decoupled from its main classical
  application and stands as pure non-stable K-theory.
* The `O_∞ * O_∞` reduction makes it a free-probability/K-theory
  hybrid: a unitary `u` in the free product, trivial in `K_1`
  (= trivial in each factor since `K_1(O_∞ * O_∞) = 0`), must be
  connected to `1`.  The free-product unitary group deformation
  technology (Brown--Dykema-type standard form arguments, and the
  homotopy analysis of `U(A*B)` by Thomsen) handles REDUCED free
  products with faithful states; `O_∞` has no trace, which is exactly
  why nothing transfers — the recorded gap is a homotopy analogue of
  Avitzour freeness for state-free full products.  Kirchberg's
  squeezing property is the only structural attack on record and its
  status for `O_∞ * O_∞` is open.
