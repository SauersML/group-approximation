# gq-pp-higher — piecewise-projective groups of RP^{n-1} over Q containing PGL_n(Q)

## Approach
- Family: piecewise projective / quasi-analytic local models. Signature: "germ extensions add no pieces".
- Done: analytic continuation bounds the globally projective (or affine) elements of any group that is locally
  in a f.g. finitely-piecewise base off a nowhere dense set by the base's piece group. Lane finished its first target.

## Established
- `germ-extensions-omit-standard-gl-n-q` (4a58a2b5b; lane-proved, not refereed): every finite germ extension or
  tower over a f.g. finitely piecewise projective/affine base B (V, T, Scott/RN affine, adelic affine models) has
  G ∩ L ⊆ Δ_B, a f.g. linear group, so it is RF, with no standard GL_n(Q) and no standard unipotent (Q,+).
  Corollary: the rational PIP group of RP^{n-1} (finitely many PGL_n(Q) pieces) is not f.g.
  The finitely-piecewise case G = B is gq-solenoid's `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`.

## Needs
- none

## Dead
- Natural (standard-action) piecewise-projective hosts over Q in every dimension n >= 2, with or without finitely
  many singular points per element: all excluded by the node above.

## Sparks (not pursued by this lane)
- Nonstandard divisibility for n >= 3: the T-bar trick needs an infinite cyclic deck group; RP^{n-1} (n >= 3) has
  pi_1 = Z/2, so lifts to S^{n-1} give only Z/2 central extensions. Look for spaces with Z-covers carrying
  piecewise-projective GL-type actions (a projective line RP^1 inside RP^{n-1}, oriented flag bundles, n-torus =
  gq-tbar-lift-n).
- Germ recursion: in any group containing standard PGL_n(Q), the germ group at a rational point p contains the
  parabolic P_p(Q) ⊇ GL_{n-1}(Q) injectively (identity principle). So germ-type finite presentation criteria need
  f.g. (f.p.) germ groups containing GL_{n-1}(Q): the problem one dimension down, in germ form.
- A base with a non-f.g. piece group needs elements with infinitely many pieces carrying infinitely many primes; with
  finitely many pieces off every neighbourhood of the singular set, the new primes accumulate at singular points.
