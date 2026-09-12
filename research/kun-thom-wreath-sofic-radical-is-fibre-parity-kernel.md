---
rg: 2
id: kun-thom-wreath-sofic-radical-is-fibre-parity-kernel
kind: claim
title: The sofic radical of the Kun--Thom coset wreath is the fibre-parity kernel over G/EL_r(R)
distinct_from:
  free-lamp-radical-is-free: that computes the sofic radical of the free-lamp amalgam G *_Gamma (Gamma x K) and finds a free collapsing kernel; this computes the sofic radical of the binary coset wreath (Z/2) wr_(G/Gamma) G and finds an elementary abelian 2-group of fibre-even lamp configurations.
  kt-intermediate-coset-wreaths-are-nonsofic: that proves every intermediate coset wreath W_K with N not contained in K is nonsofic; this identifies the smallest normal subgroup of W with sofic quotient, and that quotient is the coset wreath over K = N, which is residually finite.
  sofic-radical-localizes-bernoulli-deficit-witnesses: that says every Bernoulli Rokhlin deficit witness over an arbitrary group folds on its sofic radical; this computes the sofic radical of the Kun--Thom wreath, so over that group the fold is a fibre-even lamp configuration.
  compression-wreath-five-radicals-coincide: that computes the MF, finite, linear and Bohr radicals of the doubling family K^(G*/Gamma*) x| G*; this computes the sofic radical of the Kun--Thom Theorem E coset wreath.
  kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers: that proves a witness needs a non-closed stabilizer and bounds Rad(W) above by the zero-sum configurations over G/Gamma-hat from residual finiteness; this proves the matching lower bound through the rigid defect criterion, identifies Gamma-hat = N = EL_r(R), and describes W/Rad(W).
---

**ESTABLISHED.** Let `Gamma < G` be the Kun--Thom Theorem E pair
(`kun-thom-nonsofic-wreath`): `R = F_q[x_1^(±1),...,x_d^(±1)]`,
`Gamma = EL_r(R_+)`, `G = EL_r(R) x| SL_d(Z)`, `r, d >= 3`. Put

    N = <<Gamma>>_G = EL_r(R),      W = (direct_sum_(G/Gamma) Z/2) x| G,

with lamps `e_x`, and let `pi : G/Gamma -> G/N` be the fibre map. Let `K_even`
be the finite lamp configurations whose support meets every fibre `pi^-1(y)`
in an even number of cosets.

**Theorem.**
1. `Rad_sof(W) = K_even`.
2. `W / Rad_sof(W)` is `W_N = (direct_sum_(G/N) Z/2) x| G`, through summing lamps
   over fibres. `W_N` embeds in `((Z/2) wr SL_d(Z)) x G`, so it is residually
   finite.

In words: every homomorphism from `W` to a sofic group factors through the
fibre-parity quotient `W_N`, and `W_N` is residually finite. The whole failure of
soficity of `W` sits in the elementary abelian 2-group `K_even`.

## Consequences

- **Deficit witnesses.** By `sofic-radical-localizes-bernoulli-deficit-witnesses`,
  every Bernoulli Rokhlin entropy deficit witness over `W` has two points
  `p != p'` with `p^-1 p'` a nontrivial fibre-even lamp configuration. The two
  points lie in one lamp coset, and their difference meets some `N`-fibre of
  `G/Gamma` in at least two cosets.
- **Garden-of-Eden windows.** The same localization holds for the windows of
  `sofic-radical-localizes-garden-of-eden-windows`. `W` is already surjunctive
  (`kun-thom-nonsofic-wreaths-are-surjunctive`), so this is a consistency check.
- **Intermediate wreaths.** `W_K` is nonsofic exactly when `N` is not contained
  in `K` (`kt-intermediate-coset-wreaths-are-nonsofic`), and `W_N` is the largest
  sofic quotient of `W`.
- **Profinite closure.** The profinite closure `Gamma-hat` of `Gamma` in `G` is
  `N`. So the upper bound of
  `kun-thom-wreath-deficit-witnesses-need-nonclosed-stabilizers`, zero sum on
  the fibres of `G/Gamma -> G/Gamma-hat`, is attained, and it is the sofic
  radical.
- **What a lower bound must see.** Every argument that counts through a sofic
  quotient of `W` factors through `W_N` and is blind to every fold. Inside one
  `N`-fibre `N` acts transitively, and there the rigid defect collapses lamps in
  every sofic model.

Derivation: [[kun-thom-wreath-sofic-radical-fibre-parity-proof]].
