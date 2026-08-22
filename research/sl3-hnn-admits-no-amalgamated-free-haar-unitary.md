---
rg: 2
id: sl3-hnn-admits-no-amalgamated-free-haar-unitary
kind: claim
title: No regular-trace matrix model of SL3(Z[1/2]) carries a Haar unitary in the SL3(Z)-centraliser that is free from the lattice factor with amalgamation over L(SL3(Z))
distinct_from:
  sl3-pair-relative-commutant-route: that asks for the full relative-commutant collapse, forbidding every subgroup-central unitary that fails to be ambient-central; this forbids only the ones with the amalgamated-free joint distribution that an embedding of the HNN factor would supply, and is implied by the collapse.
  projective-trace-square-transfer-for-sl3-pair: that forbids every subgroup-central unitary whose commutator with the ambient generator is non-scalar; this is weaker still, since an amalgamated-free unitary has commutator of trace zero, and is implied by the transfer.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that is the equivalence, for any pair, between hyperlinearity of the HNN group and the existence of such a unitary in some model; this is the OPEN instance of its negative side for the rank-two arithmetic pair.
---

OPEN.  Let `C = SL_3(Z) <= A = SL_3(Z[1/2])`, `B = L(C) subset N = L(A)`.
For every trace-preserving embedding `iota : N -> M` into a tracial matrix
ultraproduct, there is NO unitary `k in B' cap M` with `E_B(k^n) = 0` for
all `n != 0` such that `N` and `W^*(B, k)` are free with amalgamation over
`B`.

By `hnn-hyperlinearity-is-amalgamated-free-haar-unitary` this is exactly
non-hyperlinearity of the finitely presented group
`G_3 = <SL_3(Z[1/2]), t | [t, SL_3(Z)] = 1>`, and it is the weakest
operator-algebraic statement in the rank-two collapse lane: the full
collapse `(RC3)` of `sl3-pair-relative-commutant-route` implies it
(`sl3-amalgamated-free-exclusion-from-collapse`), the projective
trace-square transfer implies it
(`sl3-amalgamated-free-exclusion-from-projective-transfer`), and it feeds
the goal through `non-hyperlinear-from-sl3-amalgamated-free-exclusion`.
Nothing weaker than this statement makes `G_3` the witness.

## Attempts

- **Standard model.**  In `M = L(A)^omega` no such `k` exists, because no
  leak of any kind exists there
  (`arithmetic-pair-group-factor-ultrapower-has-no-leak`); every candidate
  lives in `L^2(M) (-) L^2(L(A))`.
- **Coordinatewise form.**  Since `SL_3(Z)` has property (T), Peterson's
  interchange formula lets `k` be represented by unitaries commuting
  exactly with the microstate image `pi_n(SL_3(Z))` in every coordinate;
  the amalgamated-free joint distribution is not coordinatewise, because
  `L(C)` is strictly smaller than the ultraproduct of the coordinate
  algebras `pi_n(C)''`, so the `B`-valued conditional expectation is not
  computable coordinate by coordinate.  This is where the congruence
  models, in which `pi_n(A) subseteq pi_n(C)''`, are automatically
  excluded (co-density), and where exotic models are not.
- **Popa's theorem does not apply.**  Relative free independence in the
  centraliser `B' cap M` is a theorem for AMENABLE `B` (Popa
  arXiv:1308.3982); `B = L(SL_3(Z))` is the opposite extreme, and no
  published result produces or forbids free independence in the
  centraliser of a property-(T) subalgebra of `R^omega`
  (Gao--Junge arXiv:2012.07940 record the amalgamated-free-product
  embeddability question as open).
- **1-bounded entropy cannot decide it.**  The pair `k, u_h k u_h^*` would
  be free Haar unitaries inside the centraliser of the property-(T)
  algebra `L(C cap hCh^-1)`, and Hayes' normaliser bound keeps the
  relative 1-bounded entropy finite there, so no entropy count separates
  this scenario from the standard model (recorded in
  `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`).
- **Where a proof must act.**  Any proof must use the `B`-valued
  distribution of `k` against the Hecke structure of the pair, for
  example the far-defect formula `hecke-far-commutator-defect-formula`,
  which for such a `k` says the conjugates `pi(g) k pi(g)^*` along far
  double cosets become asymptotically orthogonal to `k` — consistent
  with freeness, hence not yet a contradiction.
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
  microstates of `D`.  This discards the stable letter's Haar moments and
  all higher amalgamated-free conditions, and is therefore a narrower
  sufficient target than the present exact-equivalence formulation.
