---
rg: 2
id: stw99-problem-lviii-pure-k1-bijective
kind: claim
title: Pure C*-algebras are K1-bijective and K-stable (STW Problem LVIII, Thiel)
root: true
artifacts:
  - research/artifacts/stw99-k1-kk-cluster-2026-08-30.md
---

**Problem LVIII of Schafhauser--Tikuisis--White, arXiv:2506.10902**
(Thiel).  Is every pure C\*-algebra `K_1`-bijective, or even
`K`-stable?  Jiang: `Z`-stable algebras are `K`-stable; STW flag the
non-nuclear case as the interesting one, where pureness does not give
`Z`-stability.

## Attempts

* The test class is the 2025-26 selflessness wave: reduced group
  algebras of limit groups and their relatives have strict comparison
  and unique trace (so all ranks occur and they are pure) without
  known `Z`-stability; `K_1(C*_r(F_n)) = Z^n` with the Fuglede--Kadison
  determinant controlling `π_0(U)`.  For `C*_r(F_n)` `K_1`-bijectivity
  is classical (sr1: Dykema--Haagerup--Rordam territory gives
  `K_1`-injectivity via stable rank one), so a counterexample needs a
  pure algebra of higher stable rank — but Lin's theorem says simple
  separable finite PURE algebras have sr1!  So in the simple finite
  case `K_1`-injectivity is FREE (Rieffel) and `K_1`-surjectivity is
  the only content; simple pure infinite algebras are `K_1`-bijective
  (Cuntz).  Sharp residue: `K_1`-surjectivity and the higher
  `K`-stability maps for simple finite pure algebras, plus the
  non-simple case where Lin is unavailable.  Recorded reduction: via
  Lin + Rieffel + Cuntz, LVIII for simple algebras is exactly
  "sr1 + pure ⟹ K_1-surjective + K-stable" — Thiel-style Cuntz
  semigroup methods apply to the rank side of unitaries
  (`det`-twisted rank functions), untried in the literature.
