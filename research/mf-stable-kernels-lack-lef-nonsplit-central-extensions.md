---
rg: 2
id: mf-stable-kernels-lack-lef-nonsplit-central-extensions
kind: claim
title: A locally MF-stable group has no LEF central Z-extension whose centre meets the commutator subgroup, so a perfect locally MF-stable kernel has no nonsplit LEF central Z-extension
distinct_from:
  mf-radical-is-blind-to-degree-two-windings: that shows every MF model of a group has a realification with all windings zero, so windings cannot prove non-MF; this uses windings in the other direction, as an obstruction to rounding asymptotic representations to exact ones, where one model with a nonzero winding is enough.
  exel-loring-mark-quantization: that is a programme to kill an infinite-order central mark in every corona model of the extension; this works on the base group and uses finite scalar-twisted models of a LEF extension to refute operator-norm stability of the base.
  hs-stability-forces-nonhyperlinear-central-extension: that is the Hilbert--Schmidt analogue with finite central kernels and property (T;FD); this is in operator norm, needs an infinite cyclic centre and no Kazhdan hypothesis, and concludes failure of local MF-stability.
---

**ESTABLISHED (unreviewed).** Proof route: `mf-stable-kernels-lack-lef-nonsplit-central-extensions-proof`.

Let `K = F_S / N` be finitely generated. Say `K` is **locally MF-stable (LS)** if the following
holds for every finite `R ⊂ N`. Whenever `b_i ∈ U(n_i)^S` satisfy `‖r(b_i) − 1‖ -> 0` for every
`r ∈ N`, there are `c_i ∈ U(n_i)^S` with `r(c_i) = 1` for all `r ∈ R` and
`max_s ‖b_i(s) − c_i(s)‖ -> 0`. This is condition (LS) of the w20 hole
`torsion-free-sofic-quotientless-locally-mf-stable-kazhdan-kernel` (on the landing branch).

**Theorem (WK).** Let `1 -> <t> -> Ktilde -> K -> 1` be a central extension, where `t` has
infinite order, such that
- (i) `Ktilde` is LEF, and
- (ii) `<t> ∩ [Ktilde, Ktilde] ≠ 1`.

Then `K` is not LS. More precisely, there is one relator `zhat ∈ N ∩ [F_S, F_S]` such that the
rounding in (LS) already fails for `R = {zhat}`, and hence for every finite `R ⊇ {zhat}`.

**Corollary (perfect case).** If `K` is perfect, (ii) holds exactly when the extension does not
split. So a perfect LS group has no nonsplit LEF central `Z`-extension.

**The invariant and the step where it dies.** The invariant is the Exel--Loring winding
`W_zhat(a) = (1/2πi) Tr log zhat(a)`. It is an integer, and it is locally constant on tuples with
`‖zhat(a) − 1‖ < 1`.
- Exact tuples on `R ∋ zhat` have `W = 0`.
- The scalar-twisted models `b_i` built from the finite approximations of `Ktilde` have
  `zhat(b_i) = e^{2πi d/m_i}·1` and `W(b_i) = n_i d / m_i ≠ 0`.
- An `o(1)`-rounding would force the two windings to be equal. So every member of the class dies
  at the (LS) rounding step for `R = {zhat}`.

**Sanity check.** Take `K = Z^2`, `Ktilde` = the integer Heisenberg group and `zhat = [x,y]`.
Then `b_i` are the Voiculescu clock-and-shift pairs, and (WK) reproduces the classical failure of
operator-norm stability of `Z^2`.

**Consequences for the goal `torsion-free-sofic-exact-mf-radical-over-z`.**
- Every kernel of the w20 LS hole is Kazhdan with no finite quotient. Its abelianization is finite
  by (T), and trivial by (Q), so it is perfect.
- By the Corollary, such a kernel has **no nonsplit LEF central `Z`-extension**. This is a new
  necessary condition, separate from (P1'), (Q) and (P2).
- It bites in the MF regime. There the kernel is itself LEF, by Corollary D2 of
  `locally-mf-stable-kazhdan-kernels-collapse-torus-radicals`. So the MF half of the hole now
  needs a LEF, perfect, quotientless Kazhdan group whose every nonsplit central `Z`-extension
  fails to be LEF.
- In the full-radical regime the condition is a consequence and not an extra cost, since (LS)
  holds there automatically.
- No Kazhdan, torsion-freeness or soficity hypothesis is used. So (WK) is a class kill for
  (LS) in general.

**What (WK) does not decide.**
- Whether some LEF, quotientless Kazhdan group has `H^2(K;Z) = 0`, or only non-LEF nonsplit
  `Z`-extensions.
- Whether the LEF hypothesis on `Ktilde` can be weakened to MF with `t` sent to near-scalars. See
  the proof route, remark (R2).

## Attempts

- **Winding obstruction to (LS) (2026-09-20, swarm-0917-w21-w21-titz-last1).** Established here.
  Proof route: `mf-stable-kernels-lack-lef-nonsplit-central-extensions-proof`.
