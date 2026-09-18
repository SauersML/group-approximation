---
rg: 2
id: finite-moment-hardness-via-projective-amplification
kind: route
title: Dead -- obtain finite-moment 2-to-1 hardness by amplifying an arbitrary hard 2-to-1 instance with a projective alphabet-lifting gadget
target: finite-moment-pairing-2to1-hardness
requires: []
---

**Dead.** The attack splits the hole into two parts:

* **(a)** a combinatorial amplification that turns an arbitrary NP-hard
  2-to-1 instance into one whose left kernel laws are exactly `t`-wise uniform
  with `||1_E D_mu||_q <= C`;
* **(b)** a soundness transfer.

The natural way to get (b) for free is a **projective** gadget. Each output
label projects deterministically to an input label, and every output
constraint satisfies `p' o phi' = phi o p`. YES labellings then lift and NO
labellings project. Members include padding the alphabet, product lifts
`Sigma x [r]`, label splitting, random relabelling inside fibres, and
projective composition with a few projection maps per left vertex.

Part (a) alone is not the obstacle. Standalone smooth or finite-moment
pairing laws already exist, as in `finite-moment-hardness-from-smooth-design`.
The whole difficulty is carrying (b) along with them.

**Where every member dies.** Claim
`projective-alphabet-lifts-cannot-amplify-pairing-moments` works as follows.

* **Compatibility.** Projective soundness forces every output kernel pair to
  lie inside a fibre of `p`, or over an input kernel pair.
* **Domination step.** The lifted-colouring domination
  `D'(z o p) >= m^(n' - s/2) w D_S(z)` gives
  `||1_(E') D'||_q >= w theta_* m^((q-2) g/(2q))`, where `g` is the surplus
  `2n' - |p(Sigma')|`.
* **Bounded surplus.** The input law, restricted and measured on the
  pulled-back window, must already have bounded moment (K4). Nothing is
  amplified, and polynomial-support Grassmann or affine inputs cannot be
  repaired, by the entropy bound.
* **Unbounded surplus.** The moment blows up unless there are
  `k >= m^((q-2) g_min/(2q))/(2C)` maps (K1).
* **Mixtures.** Mixing small and large surplus meets the support count
  `(2n')^(3g/2)` per input kernel. So
  `k >= exp(Omega(n'/log n'))` for polynomially many input kernels (K3).

This covers `q >= 3`, which is the regime Theorem 1 of
`research/artifacts/unique-games-finite-density-moments-2026-09-12.md`
requires once `rho` is close to 1. It also needs the balanced window to
contain `W_kappa` with `kappa^2 >= max(2R, 4)`.

**What survives.**

* **(b) that is not projective.** The output kernels pair labels across
  input kernel classes on a constant fraction of pairs. This is list-decoding
  soundness of BKM Appendix B type.
* **Many projections.** Re-encodings with `exp(Omega(n'/log n'))` projections
  per vertex, as in long-code composition.
* **Huge super-blocks.** Gadgets whose super-blocks exceed the window scale.
