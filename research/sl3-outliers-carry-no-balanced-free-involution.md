---
rg: 2
id: sl3-outliers-carry-no-balanced-free-involution
kind: claim
title: No uniform lattice outlier carries a balanced central involution free from the S-arithmetic group
distinct_from:
  sl3-z-weakly-ucp-stable: that forbids uniform outliers of the lattice altogether, repairing every hyperlinear approximation to genuine representations; this permits outliers in abundance and forbids only one structure on them -- a balanced free central involution -- so it is implied by stability and strictly weaker as a hypothesis, while still closing the double-swap route.
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
  point of stating the claim is that the converse fails -- nothing here
  requires repairing an outlier, only reading one moment pattern on it --
  so this is the weakest currently-wired hypothesis that closes a route
  to the goal.
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
  exist; property (T) supplies exactly one tool there, the robust Kazhdan
  projection for the conjugation representation on `L^2(M_(d_n))`, whose
  near-invariant subspace contains `s` -- bounding what else it can
  contain is the concrete attack.
- **Splitting self-similarity (structural constraint on refutation).**
  Any enemy splits: the spectral projections of `s` cut the lattice
  microstates into two trace-`1/2` corners, each again of regular type;
  if both corners were near-genuine the whole would be, contradicting
  outlier-ness -- so at least one corner is again an outlier, and the
  enemy propagates down a binary tree of corners.  A refutation by
  construction must therefore build outliers at every scale
  simultaneously; no finite modification of a genuine model can do it.
