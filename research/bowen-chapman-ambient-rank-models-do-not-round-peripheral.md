---
rg: 2
id: bowen-chapman-ambient-rank-models-do-not-round-peripheral
kind: claim
title: Honest rank models of the Bowen--Chapman ambient group do not round the peripheral subgroup in characteristic two
invalidates: [non-linear-sofic-via-bowen-chapman-rank-transcription]
distinct_from:
  kazhdan-group-rank-models-admit-no-expander-decomposition: that uses models of EL_3(F_2[t]) and of the Theorem E subgroup alone; this uses congruence representations of the whole ambient group EL_3(F_2[Z^3]) semidirect EL_3(Z), which a transcribed decomposition step for the double must handle, and adds an almost-centralizer at linear distance from the exact commutants.
  kazhdan-rank-rounding-fails-over-every-field: that removes rounding from property (T) for EL_3(Z[t]) over every field; this is the Bowen--Chapman pair over characteristic-two fields, with representations that extend to the ambient group.
  kazhdan-rank-ultraproducts-can-have-diffuse-commutants: that is a diffuse relative commutant for irreducible models of one Kazhdan group; this is an almost-centralizer at distance 1/64 from the exact commutants of reducible ambient models, from the uncertainty principle on (Z/N)^3.
  nonmonomial-multiplicity-obstructs-hs-compressor-transport: that is the Hilbert--Schmidt obstruction to compressor transport; this is the rank-metric failure of rounding for the Bowen--Chapman pair.
  f2-linear-sofic-groups-kill-rigid-compression-defects: that is the open F_2 rank row of the defect criterion; this removes one proof strategy for one pair and decides nothing about the row.
artifacts:
  - research/artifacts/nls-rank-metric-witness-2026-09-12.md
  - GroupApproximation/BowenChapman/ResiduallyFiniteSubstitution.lean
---

**ESTABLISHED.**

**Setting.**
- `F` is a field of characteristic two, `N >= 7` is odd, `m = (N-1)/2`,
  `A = F[(Z/N)^3]` and `n = 3N^3`.
- `G = EL_3(F_2[Z^3]) semidirect EL_3(Z)` and `Gamma = EL_3(F_2[N^3])`. These
  are the Lean `Ambient` and `Peripheral`.
- `rho_N : G -> GL(A^3)` reduces exponents modulo `N` and substitutes by
  `M mod N`. It is the action of `residuallyFinite_semidirectProduct_of_expSubst`,
  with `F_2` replaced by `F`.
- `B_m = span{ x^v : v in [0,m)^3 }`, `W = B_m^3`, and
  `p = 1_3 (x) pi_B` is the coordinate projection onto `W`.
- `S = { e_ij(1), e_ij(x_l) }` generates `Gamma`, and
  `b_S(X) = sum_(s in S) (dim(X + sX) - dim X)`.

**Theorem.**
1. **Almost invariant.** `b_S(W) <= 1.5 n/N`, and `rk[p, rho_N(s)] <= 2m^2`
   for `s` in `S`.
2. **Far from invariant.** `dim W + dim U - 2 dim(W cap U) > n/64 - 3` for
   every `rho_N(Gamma)`-invariant subspace `U`.
3. **Far from the commutant.** `rk(p - z) > n/64 - 3` for every `z` that
   commutes with `rho_N(Gamma)`.
4. **Consequences.**
   - **No rounding.** No function `delta(eps) -> 0` rounds `eps n`-almost-invariant
     subspaces, for restrictions to `Gamma` of honest `F`-representations of `G`.
   - **No linear-size expanding pieces.** Fix `c, kappa > 0`. For large `N`, no
     subspace of dimension at least `cn` and boundary `o(n)` is internally
     `kappa`-expanding for `rho_N|Gamma`.
   - **No centralizer rounding.** `[p_N]` is a sequential almost-centralizer of
     `Gamma`. Its normalized rank distance from the exact commutants is at least
     `1/64`.
   - **Faithful approximations.** Let `L_N` be the regular representation of a
     finite quotient of `G`, amplified to dimension in `(n/2, n]`.
     - `rho_N (+) L_N` is an `F`-linear sofic approximation of `G` by
       homomorphisms.
     - `W (+) 0` has normalized boundary at most `1.5/N`, and normalized
       distance at least `1/128 - o(1)` from every invariant subspace.

**Scope.**
- **Linear-size pieces only.** Expander decompositions of `rho_N|Gamma` into
  pieces of sublinear dimension are not covered.
- **Characteristic two only.** `F_2[Z^3]` has no ring map to an algebra over a
  field of any other characteristic.
- **Consistent with normalization.** Conjugating `p` by the actor gives the
  projection onto a parallelepiped. That parallelepiped is again Folner, so the
  conjugate still almost commutes with `Gamma`. The claim removes a proof of
  normalization, not normalization itself.

Derivation: [[bowen-chapman-ambient-rank-models-do-not-round-peripheral-proof]].
