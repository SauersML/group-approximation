---
rg: 2
id: sl3-hnn-admits-no-amalgamated-free-haar-unitary
kind: claim
title: No regular-trace matrix model of SL3(Z[1/2]) carries a Haar unitary in the SL3(Z)-centraliser that is free from the lattice factor with amalgamation over L(SL3(Z))
distinct_from:
  sl3-pair-relative-commutant-route: that quantifies over every commutant element; this names the canonical HNN distribution. Arithmetic maximality and tensor extraction prove the two global exclusions equivalent, while changing the embedding.
  projective-trace-square-transfer-for-sl3-pair: that is a finite-matrix inequality for arbitrary assignments; the arithmetic maximality and regular-RCC transfer theorems make it equivalent to this canonical HNN exclusion.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that is the equivalence, for any pair, between hyperlinearity of the HNN group and the existence of such a unitary in some model; this is the OPEN instance of its negative side for the rank-two arithmetic pair.
---

OPEN.  Let `C = SL_3(Z) <= A = SL_3(Z[1/2])`, `B = L(C) subset N = L(A)`.
For every trace-preserving embedding `iota : N -> M` into a tracial matrix
ultraproduct, there is NO unitary `k in B' cap M` with `E_B(k^n) = 0` for
all `n != 0` such that `N` and `W^*(B, k)` are free with amalgamation over
`B`.

By `hnn-hyperlinearity-is-amalgamated-free-haar-unitary` this is exactly
non-hyperlinearity of the finitely presented group
`G_3 = <SL_3(Z[1/2]), t | [t, SL_3(Z)] = 1>`. By
`arithmetic-hnn-nonhyperlinearity-equals-global-collapse`, it is
equivalent to full collapse `(RC3)`, scalar non-relative-embeddability,
plain-double nonhyperlinearity, and the full projective trace-square
transfer inequality. A single projection leak has stabilizer exactly
`C` by Smith maximality; tensor extraction then constructs the HNN
distribution in a new model. Thus the stronger distribution imposed
on a witness in one model does not make this global exclusion weaker.
The claim feeds the goal through
`non-hyperlinear-from-sl3-amalgamated-free-exclusion` and remains OPEN.

## Attempts

- **Standard model.**  In `M = L(A)^omega` no such `k` exists, because no
  leak of any kind exists there
  (`arithmetic-pair-group-factor-ultrapower-has-no-leak`); every candidate
  lives in `L^2(M) (-) L^2(L(A))`.
- **Coordinatewise boundary.** Property (T) controls the conjugation
  representation after an exact subgroup representation is available.
  It does not, by itself, replace an arbitrary approximate subgroup
  tuple by an exact representation or make its commutant coordinatewise.
  The representation-lift and subgroup-exactification nodes record their
  missing hypotheses explicitly. Even on an exact face, amalgamated
  freeness is a joint limiting distribution over `L(C)`, not a
  coordinatewise expectation over the larger matrix algebras generated
  by the subgroup images.
- **The ambient-extendable sector is closed.**
  `sl3-amalgamated-free-enemies-are-ambient-extension-outliers` combines
  the exact subgroup-indicator moment forced by amalgamated freeness with
  the unbalanced-torus inequality.  It proves that any surviving enemy is
  uniformly separated, on the lattice generators, from the restriction of
  every exact same-dimensional representation of `A`.  This includes
  arbitrary exact ambient multiplicity patterns, not only a single tensor
  factor.  The remaining gap is therefore genuinely an ambient-extension
  outlier: being close to an exact representation of `C` does not by itself
  make that representation extend to `A`.  The exact residual leaf is
  `sl3-ambient-outliers-carry-no-free-hnn-letter`,
  wired through `sl3-amalgamated-free-exclusion-from-outlier-rigidity`.
- **Popa's theorem does not apply.**  Relative free independence in the
  centraliser `B' cap M` is a theorem for AMENABLE `B` (Popa
  arXiv:1308.3982); `B = L(SL_3(Z))` is the opposite extreme, and no
  published result produces or forbids free independence in the
  centraliser of a property-(T) subalgebra of `R^omega`
  (Gao--Junge arXiv:2012.07940 record the amalgamated-free-product
  embeddability question as open).
- **The stable letter's natural Popa deformation has the wrong
  compactness.**
  `central-hnn-haar-leg-has-only-base-relative-compactness` diagonalizes
  the Poisson maps on
  `L(C) tensor_bar L(Z)`: they are compact relative to `L(C)` but fix the
  whole infinite-dimensional `L^2(L(C))`, so they are not scalar compact.
  This algebra has no nonzero scalar-amenable corner, although the
  inclusion over `L(C)` is relatively amenable.  Thus the candidate Haar
  unitary itself produces neither an amenable corner nor the scalar-compact
  deformation needed for a property-`(T)` contradiction.  Any Popa proof
  must extract additional scalar tightness from the matrix coordinates of
  the joint extension.
- **1-bounded entropy cannot decide it.**  The pair `k, u_h k u_h^*` would
  be free Haar unitaries inside the centraliser of the property-(T)
  algebra `L(C cap hCh^-1)`, and Hayes' normaliser bound keeps the
  relative 1-bounded entropy finite there, so no entropy count separates
  this scenario from the standard model (recorded in
  `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`).
- **Hecke information remains consistent with the candidate.** The
  far-defect formula `hecke-far-commutator-defect-formula` gives the
  expected orthogonality of distant conjugates of a free letter.
  This supplies no contradiction. Maximality now also permits a proof
  through ordinary commutant collapse without retaining those free
  moments at every step.
- **Symmetric-double MF firewall.**
  `sl3-hnn-sits-in-shulman-symmetric-double` embeds the entire HNN group
  in

  ```text
  (A x Z) *_C (A x Z).
  ```

  Shulman's genuine operator-norm theorem therefore shows that MF of the
  full group C-star algebra `C*(A x Z)` would make the full group C-star
  algebra of the symmetric double MF.  This still does **not** make the
  HNN group hyperlinear: the resulting corona embedding need not preserve
  the canonical trace, and operator-norm group-MF does not imply
  canonical-trace hyperlinearity.  Thus the symmetric-double idea gives no
  shortcut in either direction.  To use it one would have to upgrade its
  embedding to the canonical trace on the nonamenable amalgam, precisely
  the trace-sensitive problem this target already expresses.
- **A smaller adjacent-vertex double is enough for a negative result.**
  `sl3-arithmetic-double-embeds-in-centralizer-hnn` identifies
  `<A,tAt^(-1)>` with `D=A*_C A`.  Therefore it suffices to show that this
  subgroup is non-hyperlinear.  The exact finite-dimensional boundary is
  unusually rigid: `sl3-arithmetic-double-finite-representations-fold`
  proves by a block-swap/co-density argument that every exact matrix
  representation of `D` factors through the fold `D->A`.  The open
  `sl3-regular-arithmetic-double-fold-mark-collapse` asks only to promote
  that fact for one fold-kernel word along full canonical-character
  microstates of `D`. This removes the stable letter from the presentation;
  the general coset equivalence proves that the resulting negative
  group statement is equivalent to the present one.
