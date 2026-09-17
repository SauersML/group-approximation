---
rg: 2
id: deligne-nontrivial-maslov-opnorm-sectors-are-empty
kind: claim
title: The two nontrivial mod-three Maslov sectors have no point-norm matrix models
distinct_from:
  maslov-mod3-projective-defect-gap: that asks for a normalized-Hilbert--Schmidt defect gap; this asks for pointwise operator-norm asymptotic projective representations and is exactly the MF-radical gate.
  deligne-triple-cover-fd-central-invisibility: that excludes exact finite-dimensional odd-sector representations; this excludes their asymptotic operator-norm analogues.
---

**OPEN PRECISE OPERATOR-MF GATE.**  Let `alpha` and `alpha^2` be the two
nontrivial mod-three Maslov multipliers of `Sp_4(Z)`.  There is no sequence
of finite-dimensional projective unitary tuples which is pointwise
asymptotically multiplicative in operator norm with multiplier `alpha` or
`alpha^2`.

Equivalently, neither nontrivial Maslov sector defines a homomorphism into a
positive-dimension norm-matrix corona.  This statement uses no property
`(T)` hypothesis.  Exact finite-dimensional invisibility does not prove it:
the missing issue is precisely passage from exact representations to
operator-norm asymptotic representations.

## Attempts

- **2026-09-17, swarm-0917-w4-pull-deligne-2: transplanting the g >= 3
  stability route to genus two dies at the [T_2] hypothesis.** At g >= 3,
  empty sectors would follow from operator-HS-stability of the cover lattice
  (BDL Proposition 1.5 via `deligne-sp2g-covers-not-mf-from-operator-hs-stability`),
  and the only proposed source of that stability is BDL Conjecture 1.8, whose
  input is `[T_2]`. At g = 2 that input is false, even virtually:
  `genus-two-cover-lattices-fail-bracket-t2` shows that every finite-index
  subgroup `Delta` of `Gamma~_2` or of `E_3` has
  `dim H^2(Delta; l^2(Delta/Delta')) >= 117`, where `Delta'` is `Delta` meet the
  level-four preimage. The invariant is `b_2(Gamma_2(4)) = 118`
  (Hoffman--Weintraub), carried through the Gysin sequence, transfer and
  Shapiro. So DGLT/BLSW Theorem 1.1(F) and Conjecture 1.8 do not apply to
  this gate or to any finite-index model of it. A genus-two proof needs
  vanishing of the specific defect classes, or a non-cohomological route
  such as the Schur-kernel hole.

