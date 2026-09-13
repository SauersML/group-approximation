---
rg: 2
id: sl3z-purely-matricial-field
kind: claim
title: SL_3(Z) is purely matricial field
---

OPEN.  There is a sequence of finite-dimensional unitary representations
`rho_i` of `SL_3(Z)` with `||rho_i(z)|| -> ||lambda_(SL_3(Z))(z)||` for every
`z in C[SL_3(Z)]`.

This is the question Magee--de la Salle leave open (arXiv:2312.03220v2, p. 2:
"it could still be the case that SL3(Z) is not purely MF and we would be very
interested to know the answer"; Magee's survey arXiv:2503.21619, Section 2.4:
"a curious gap at d = 3").  By Bass--Milnor--Serre every finite-dimensional
unitary representation factors through some `SL_3(Z/NZ)`, so the claim asks
for irreducible representations of congruence quotients, possibly of mixed
prime levels, whose norms on every group-ring element approach the regular
norms.  A positive answer makes `C*_r(SL_3(Z))` MF and so answers
`infinite-kazhdan-group-with-mf-reduced-cstar`.

## Attempts

* **Refute by one invariant-vector witness, as for `SL_4(Z)`.**  Dead for every
  finite family of witnesses: `sl3z-has-no-invariant-vector-witnesses`.  The
  block `SL_2` fails on Deligne's representations (MdlS Example 2.2); the
  principal `SL_2` fails at every prime `p >= 5` on the degenerate principal
  series `Ind_P(eta)` with `eta` odd, `eta != sgn`; Zariski-dense subgroups fail
  at almost every prime.  Single levels already escape both main witnesses:
  four representations of `SL_3(F_7)` and four of `SL_3(Z/9)` have no fixed
  vector for the block or the principal `SL_2` (exact census in the artifact of
  that claim).  A refutation must detect norm excess without an eigenvalue at
  the top of the spectrum.
* **Deligne's representations as the strongly convergent sequence.**  Dead:
  `deligne-sl3-representations-have-principal-sl2-invariants` gives them a
  2-dimensional principal-`SL_2` fixed space and norm `4` on a group-ring
  element whose regular norm is `< 4`.  The next candidates are the components
  of cubic-twist-invariant cuspidals at `p == 1 mod 3` that miss both witnesses.
* **Nontrivial parts of congruence regular representations.**  Dead in the
  plain form: `l^2(SL_3(Z/N))` contains every irreducible representation of
  the quotient, including those with block-`SL_2` fixed vectors.  A selection
  of irreducible constituents is necessary; which selection could work is
  unknown.
* **Wassermann's Kazhdan-projection argument as an obstruction.**  Does not
  refute.  For a strongly convergent `rho = (+)_i rho_i` put
  `B = C*_rho(SL_3(Z))` and `I = B cap (+)_i M_(N_i)`, so `B/I = C*_r(SL_3(Z))`.
  The spectral projection `p` of `|S|^(-1) sum_s rho(s) (x) conj rho(s)` at `1`
  lies in `B (x)_min conj B`, is not in `I (x)_min conj B` (its diagonal blocks
  have norm 1), and maps to `0` in `C*_r(SL_3(Z)) (x)_min conj B` by Fell
  absorption and Kesten.  This only says that the extension
  `0 -> I -> B -> C*_r(SL_3(Z)) -> 0` is not locally split, as in
  `kazhdan-fd-block-representation-algebras-are-not-exact`; it contradicts PMF
  only if `C*_r(SL_3(Z))` had the local lifting property.
* **Random models.**  No natural random model: by superrigidity and the
  congruence subgroup property every finite-dimensional unitary representation
  has finite congruence image, so the polynomial method's random permutation
  or Haar models of free groups have no analogue with polynomial dependence on
  the dimension.  Not worked further.
