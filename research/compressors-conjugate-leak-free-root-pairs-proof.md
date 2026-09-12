---
rg: 2
id: compressors-conjugate-leak-free-root-pairs-proof
kind: route
title: Compute the conjugates on the compressed and complementary summands and read off the leak entries
target: compressors-conjugate-leak-free-root-pairs
requires: []
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/el3-compressor-root-pair-calculus-2026-09-12.md
---

Artifact Section 1.
* Lemma 1 computes all four conjugates explicitly. `g x g^-1` sends `g(u)` to `g(xu)`. Both
  compressors map two coordinates by left multiplication with `s_0`, and the third onto the
  complement through a fixed isomorphism `R -> R^3` built from `t_0`, `T[10] = t_0 t_1` and `t_1 t_1`.
* Lemma 2 identifies the leak-free coefficients: `R t_1 t_1` for `c` on the 23 root, and `s_1 s_1 R`
  for `c'` on the 12 root, using `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1`.
* Corollary 3 gives the simultaneous conjugacies. Their commutators match the conjugated `x_13`, as
  the homomorphism property requires.

*Verification by `gk-vf-linear` (2026-09-12), Section 48 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`: the `c` half passes. The `c'` half is FALSE as stated: `c' x_12(s_1) c'^-1 - 1` has entry `(3,2)` equal to `s_1 t_0 t_0 != 0`. The corrected form is `c' (x_12(s_1 s_1 a''), x_23(b)) c'^-1 = (x_12(a'' t_0), x_23(s_0 b t_0))`, with leak-free set `s_1 s_1 R`, and `delta(s_1 s_1 a'', b) = delta(a'' t_0, s_0 b t_0)`. Correction requested from the author.*

*Corrected by the author (`gk-gate-compress`, 2026-09-12): Lemma 2, Corollary 3 and the consistency check in the artifact now use `s_1 s_1 R` and the adjoint word `T[10]`, with a correction note at the end of Section 1.*

*Resolved (`gk-vf-linear`, 2026-09-12): the corrected `c'` half (53fcaae60a) re-derived and PASS. See the addendum to Section 48 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*

*Verification by `w3-vf-linear` (2026-09-12), Section 1.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS in the corrected form. The unit c' and its coordinate isomorphism re-derived, the kernel of the conjugated nilpotent and the leak entries (t_1 t_1 a t_0, s_1 t_0 a t_0, s_1 t_0 t_1 a t_0) rechecked, leak-free set s_1 s_1 R; the c half spot-checked.*
