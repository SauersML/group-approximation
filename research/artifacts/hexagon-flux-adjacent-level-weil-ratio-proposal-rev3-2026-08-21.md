# Supplement: corrected hexagon-flux obstruction mechanism

This fragment was preserved after the active claim was demoted.

- **CORRECTION of the slogan, and the real obstruction mechanism
  (2026-08-21, same day).**  The "adjacent-level ratio" as literally
  stated TELESCOPES around the hexagon: two one-level drops and one
  two-level drop produce the same ratio of `(-1|q)` classes, so that
  quantity is identically `+1` and is NOT the flux.  The correct
  statement has two parts.  (ii-a) The route-B class (legs `h'`,
  `h''` through their own polarizations, meeting through the
  Gauss-normalized `F` at the intermediate level) is the F-class
  ratio `A(1)_l / A(1)_(l-1) = (2|p) * eps_l / eps_(l-1)`: at
  `p = 3 mod 4` this ALTERNATES `-/+ i` with the level (eps flips
  between 1 and i at every level), at `p = 1 mod 4` it is the
  CONSTANT `-1`.  (ii-b) The enemy's rephasing freedom is exactly
  the Lambda_-invariant functions on bands, because `V` must
  intertwine `pi(Lambda_-)` with `pi(h Lambda_- h^-1)`; and
  `Lambda_- = {lambda_21 = lambda_32 = 0 mod p, lambda_31 = 0 mod p^2}`
  contains `e_21(p)`, which conjugates the center of `P` out of `P`
  (`e_21(p) e_13(c) e_21(-p) = e_13(c) e_23(pc)`), so a band's
  `P`-level is NOT preserved and invariant functions are
  LEVEL-INDEPENDENT -- a single global phase `theta`.  Since `h'`,
  `h''` are conjugates of `h`, the identity `V_h = V_h' V_h''`
  rephases as `theta = theta^2 * flux`, which absorbs any CONSTANT
  flux (`theta = flux^-1`) and NO level-alternating one.  Hence:
  `p = 1 mod 4` unobstructed (constant class, absorbed), `p = 3 mod
  4` OBSTRUCTED (alternating class) -- exactly the Hilbert-symbol
  split `(p,p)_p = (-1|p)`, now derived from the measured classes
  plus the level-mixing of `Lambda_-`.  The remaining obligation is
  (ii-a) alone: that the canonical route-B composite on a flat tower
  is the Gauss-normalized `F`-conjugation (in-band `U(m)` parts
  cancelling), the polarization-factoring statement.
## Further refinement: twist incompatibility

- **(ii-a) in its final shape: twist incompatibility.**  Decompose
  the enemy's `V_h` on a multiplicity-`m` band as (SvN-canonical
  transport) tensor `u_h(band)`, `u_h in U(m)`; `V_h'`, `V_h''` are
  the `pi(w)`-transports of the same family.  The hexagon identity
  on each band reads `u_h(b) = flux(level b) * Phi(u_h)(b)`, where
  `Phi` is the route-B composite of the transported multiplicity
  parts and `flux` is the canonical scalar class (alternating at
  `p = 3 mod 4`).  Two false shortcuts are recorded: a scalar
  `flux * 1_m` IS in `U(m)`, so band-by-band absorption is always
  possible; and determinants do not extract the class, since band
  multiplicities in regular-type towers are divisible by 16 at
  `p = 3` (`|SL_3(F_3)| = 2^4 * 3^3 * 13`), making `i^m = 1`.  The
  genuine content: `u_h` is `Lambda_-`-EQUIVARIANT (conjugation
  equivariance under the between-band action), and `Lambda_-` mixes
  levels; a family satisfying `u = flux * Phi(u)` with
  level-alternating `flux` would be a level-twisted `Phi`-eigenfamily
  whose twist is a non-constant function of the level -- the claim
  (ii-a) is that no `Lambda_-`-equivariant family carries such a
  twist (scalar twists are excluded by level-mixing outright; the
  non-scalar case needs the (T)-rigidity of the multiplicity
  representation of the band stabilizers).  At `p = 1 mod 4` the
  constant flux is absorbed by a global phase and no twist is
   needed, which is the constructive side.
