---
rg: 2
id: sl3-outliers-carry-no-balanced-free-involution
kind: claim
title: No uniform lattice outlier carries a balanced central involution free from the S-arithmetic group
artifacts:
  - research/artifacts/sl3-corner-descent-dilation-budget-2026-09-05.md
distinct_from:
  sl3-z-weakly-ucp-stable: that forbids uniform outliers of the lattice altogether, repairing every hyperlinear approximation to genuine representations; this forbids only one structure on them -- a balanced free central involution -- and is implied by stability, without a claimed proof that the implication is strict.
  sl3-double-swap-involution-is-outlier-carried: that is the established confinement theorem -- the swap involution of E_p rides only on outliers; this is the open other half, that outliers cannot carry it either, and together they make E_p and the arithmetic double non-hyperlinear.
  single-hecke-average-isometry-for-lambda-central-unitaries: that asserts the full collapse for every Lambda-central unitary of every regular-trace model, exact face and outliers alike; this asks for far less -- one moment pattern (freeness) for one self-adjoint unitary on the outlier sector only, the exact face being already closed unconditionally at large primes.
---

OPEN CLAIM.  Fix a prime `p >= 11`, `Lambda = SL_3(Z)`,
`Gamma = SL_3(Z[1/p])`, `B = L(Lambda)`, `N = L(Gamma)`.  There is no
trace-preserving embedding `iota : N -> M` into a tracial matrix
ultraproduct whose lattice microstates are uniform outliers (at positive
normalized-HS distance, flexibly, from every genuine finite-dimensional
representation of `SL_3(Z)`) together with a self-adjoint unitary
`s in M` satisfying

```text
s in iota(B)' cap M,   E_(iota(B))(s) = 0,
(iota(N), W*(iota(B), s)) free with amalgamation over iota(B).   (NBI1)
```

By `sl3-double-swap-involution-is-outlier-carried` the outlier hypothesis
is not a restriction but a theorem about every candidate model of the
double-swap group `E_p`, so this claim is exactly what remains: it makes
`E_p` (equivalently the arithmetic double `D_p`) a finitely presented
non-hyperlinear group through `non-hyperlinear-from-sl3-double-swap`.

## Attempts

- **Implied by stability (route comparison).**  `sl3-z-weakly-ucp-stable`
  forbids the outlier sector entirely, hence this claim vacuously; the
  point of stating the claim is that nothing here
  requires repairing an outlier, only reading one moment pattern on it --
  so it isolates a more restricted exclusion target that closes a route
  to the goal. No converse or strict separation from stability is proved.
- **What the freeness costs the enemy.**  `(NBI1)` forces
  `q = (1+s)/2` to be a trace-`1/2` projection commuting with
  `iota(B)` whose `h`-translate is trace-independent:
  `tau(q u_h q u_h^*) = 1/4`, while on the exact face the collapse
  forces `tau(q u_h q u_h^*) = 1/2`.  The Atkin--Lehner disjointness
  theorem (`atkin-lehner-twist-of-vertex-orbit-representation-is-disjoint`)
  shows that in every GENUINE congruence model the `h`-twist acts on
  isotypic data maximally rigidly (total variation `2 - 2 p^(-k)`), the
  opposite extreme from independence.  The open content is a version of
  that rigidity that survives on outliers, where isotypic data does not
  exist. Property (T) controls the genuine conjugation representation in
  the ultraproduct, but does not automatically give a uniform spectral gap
  for the coordinate conjugation operators of HS approximate
  representations. That transfer would require an additional theorem.
- **One-step lattice splitting, not recursive model inheritance.**
  The spectral projections of `s` cut the lattice microstates into two
  trace-`1/2` corners, each again of regular type. If both corner sequences
  were flexibly near genuine representations, their direct sum would be
  too. This one-step observation does not make either corner a new model
  of the full swap extension: `s` becomes scalar, while `q u_h q` has
  squared normalized corner norm `1/2`, not one.
  `canonical-swap-corners-have-no-dimension-descent` computes the sharp
  repair cost. A unitary dilation whose compression is `o(1)`-close to
  this compressed actor requires asymptotically all of the removed
  dimension. The previous assertion that an enemy automatically propagates
  down a binary tree of full models was unsupported. A new actor and a
  new balanced free involution would have to be constructed in each corner.
- **Quantitative collapse on the exact face, by (T)-averaging alone
  (2026-08-25, late).**  On a genuine congruence model
  `pi = lambda_(SL_3(Z/m))` with `gcd(p,m)=1`, taking `pi(h)` from the
  same congruence representation of `Gamma`, if
  `|| [q, pi(s)] ||_2 <= delta` on a Kazhdan
  set of `Lambda` with constant `kappa`, then averaging over the finite
  image group (contraction controlled by the spectral gap of the
  conjugation representation) yields `q~` in the right-regular algebra with
  `|| q~ - q ||_2 <= 2 delta / kappa`, and `q~` commutes with `pi(h)`
  exactly, so

  ```text
  tau(q u_h q u_h^*) >= 1/2 - O(delta/kappa),
  ```

  against the enemy's `1/4`.  This is the involution-level shadow of the
  sector collapse and pins the entire enemy budget on the outlier sector,
  where coordinate group averaging is unavailable and a uniform
  coordinate spectral gap has not been established.
- **Two descriptions of the forbidden model (2026-08-25, corrected
  2026-09-05).**  (i) Fixed-vector form: in a genuine finite congruence
  representation of `Gamma`, the exact conjugation-fixed spaces for
  `Lambda` and `Gamma` coincide because their images coincide. Extending
  this to arbitrary approximate fixed vectors on outliers would be a
  stronger exclusion statement than the present claim, which retains the
  balanced free-involution moment pattern. Equality of exact fixed spaces
  also does not mean equality of fixed-threshold near-invariant spaces for
  different generating sets. (ii) ucp form: the enemy compression
  `Phi(a) = q pi(a) q` is exactly multiplicative on `C^*(Lambda)` and has
  Stinespring defect of trace exactly `1/4` at `h`
  (`tau(q u_h q u_h^* q) = 1/4` by the freeness moments); so the claim
  says no ucp deformation of the regular character of `Gamma` can be a
  corner homomorphism on the Kazhdan subgroup while carrying this
  `h`-defect and the full freeness hypotheses, once its carrier is an
  outlier. Without the freeness hypotheses, excluding every such corner
  deformation would again be a stronger statement. These descriptions
  expose principal angles and Stinespring defects; neither supplies
  coordinate stability.
- **The descent tower constraint (2026-08-25, late).**  By
  `asymmetric-twist-descends-to-congruence-hnn-enemy` composed with the
  rounding theorem, one enemy forces balanced free central involutions
  over the whole descending chain of co-dense cores
  `Lambda supset C_0(g) supset ...` inside one microstate sequence, with
  zero defect in the ultraproduct.  The tower alone cannot self-destruct
  (each deeper witness is a spectral function of the original data), but
  any future exclusion theorem proved for ONE deeper pair kills the
  entire enemy class at once; the deepest-available pair is therefore the
  cheapest place to attack.
