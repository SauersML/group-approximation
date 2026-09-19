---
rg: 2
id: h-prime-mf-head-iff-alpha-periodic-w-models
kind: claim
title: An element h of W survives in an MF model of W x|_alpha Z iff, on every window, some head-keeping approximate model theta of W has theta o alpha^m approximately unitarily equivalent to theta for some m depending on the window; for H' = W x|_c Z inside P_{2,2}(J) this is the whole remaining question, and permutation (LEF-type) data never satisfy it
distinct_from:
  p22-head-survival-forces-regular-weak-containment: that shows, for P_{2,2}(J), head survival in an MF model is equivalent to P being MF and to lambda_P being weakly contained in an MF model; this reduces head survival in the index-two subgroup H' of H_mix to a periodicity condition on approximate models of the LEF normal subgroup W under the single automorphism alpha = Ad c, with a period allowed to grow with the window.
  subshift-cycle-core-is-largest-lef-subsystem: that is the LEF/chain-recurrence statement for subshift crossed products; this is the operator-norm MF analogue for an arbitrary group automorphism, acting on the space of approximate models instead of on points.
  amenable-symbol-subgroups-keep-the-jacobson-head: that shows amenable subgroups such as <g,e,u,c> keep the head; this locates the one-generator trap <g,e,u,c> inside H' (c = x_43(S)x_34(1) alone replaces r1, r2) and shows that the obstruction must come from W-models whose alpha-periods defeat every monomial seam.
artifacts:
  - experiments/h-prime-periodic-models-2026-09-17/cycle_block_check.py
  - experiments/p22-conjugation-pigeonhole-2026-09-17/pigeonhole_check.py
---

**ESTABLISHED (swarm-0917 w14, agent-verified, no referee)** by route
`h-prime-mf-head-iff-alpha-periodic-w-models-proof`. No property (T),
spectral gap or trace is used. The artifact exits 0: exact identities over
`J = F_2<S,T|TS=1>`, plus a numerical check of the block-shift identity.

**This is a reduction, not a closure.** `property-t-free-jacobson-head-collapse`
stays OPEN.

**Setting.**
* `W` is a countable group, `alpha` is an automorphism of `W`,
  `G = W x|_alpha Z = <W, c | c w c^-1 = alpha(w)>`, and `h` is in `W`.
* For a finite set `F` in `W` and `delta > 0`, an `(F,delta)`-model is a map
  `theta : W -> U(d)` with `||theta(xy) - theta(x)theta(y)|| <= delta` for
  `x, y` in `F`, and `theta(1) = 1`.
* Write `F^(m) = alpha^0(F) u ... u alpha^m(F)`.
* `h` keeps in `theta` when `||theta(h) - 1|| >= kappa`. Here `kappa > 0` is
  fixed in advance. For an involution any `kappa < 2` gives the same notion
  once `delta` is small.

**Theorem (periodic-model criterion).** The following are equivalent.
1. `h` is not in `Rad_MF(G)`. That is, some operator-norm asymptotic
   homomorphism `G -> U(d_k)` keeps `h` away from `1`.
2. **(PC)** For every finite `F` in `W` and every `delta > 0` there are:
   * an integer `m >= 1`;
   * an `(F^(m), delta)`-model `theta` of `W` that keeps `h`;
   * a unitary `V`,
   such that `max_{w in F} ||theta(alpha^m(w)) - V* theta(w) V|| <= delta`.
3. (PC) holds with `m = 1` for every window.

The content is `2 => 1`. The period `m` may grow without bound as the window
grows. The head is needed only in the first block of the model that the
proof builds.

**Specialization to the H_mix lane.**
* `W = M_2(J) x| EL_2(J)` inside `P = P_{2,2}(J) <= EL_4(J)`, with the
  left Levi acting by `n(Y) -> n(AY)`. `W` is LEF.
* `c = r2 = x_43(S) x_34(1) = diag(1, 1, C^-1)`, where
  `C = [[1+S,1],[S,1]]`. Then `alpha = Ad c` fixes the left Levi and sends
  `n(Y)` to `n(YC)`.
* `c` has infinite order: the S-degree of the first row of `E_11 C^n` is `n`
  (artifact, `n <= 12`, and in general by induction). So
  `H' = <W, c> = W x|_alpha Z`. This is the index-two subgroup of `H_mix`
  that the w14 sibling reduced to: head in `Rad_MF(H_mix)` iff head in
  `Rad_MF(H')`.
* `h = x_13(Q)`.

**Corollary 1 (the flagship through this lane).** Suppose one window
`(F, delta)` admits no (PC) data for `(W, alpha, h)`, and suppose this is
proved without (T). Then the following holds with no (T):
* `h` is in `Rad_MF(H')`, which is contained in `Rad_MF(P)` and then in
  `Rad_MF(EL_4(J))`, because `Rad_MF` is monotone.
* Apply `J -> L_2`, `S -> s_1`, `T -> t_1`. The head goes to
  `x_13(1 + s_1 t_1) = x_13(s_2 t_2)`, which is not `1`. This element lies
  in `Rad_MF(EL_20(L_2))`.
* `EL_20(L_2)` is simple and equals `St_20(L_2)` (Khanh (KH2), T-free). So
  `Rad_MF(St_20(L_2)) = St_20(L_2)`.

Conversely, if (PC) holds on every window, the head survives in an MF model
of `H'`, and so of `H_mix`, and the whole `H_mix` lane is dead.

**Corollary 2 (the one-generator trap lives in H').** The artifact checks
the following exactly over `J`:
* `[g,c] = 1`;
* `g u g^-1 = (c u c^-1)(c^-1 u c)`;
* `[e,u] = [e,c] = 1`;
* `[e, g^-1 u g] = x_13(Q)`.

Here `g = diag([[S,Q],[0,T]], 1)`, `u = x_13(1)` and `e = x_12(1)`. The
single element `c` replaces both `r1` and `r2`. Let
`Gamma_C = <g,e,u,c | those four relators>`. In every finite quotient of
`Gamma_C` the head dies, by the pigeonhole of
`p22-double-parabolic-is-not-lef`: `A = <c-conjugates of u>` is finite,
`g A g^-1 <= A`, so `g^-1 u g` lies in `A`, which `e` centralizes.

**Corollary 3 (LEF-type data never satisfy (PC)).** Let `F` contain the
window `F_0` that the proof needs for the relators of `Gamma_C` and the head
word. Let `delta < sqrt(2)/(4K+2)`, where `K` is the largest power of `c`
in those words. Then no (PC) data exist in which every
`theta(alpha^n(w))` and `V` is a permutation matrix.
* Two distinct permutation matrices are at least `sqrt(2)` apart.
* So the block model built in the proof consists of permutation matrices
  and is exactly multiplicative on the `Gamma_C` window.
* It is therefore a finite quotient of `Gamma_C` that keeps `h` in block 0,
  which contradicts Corollary 2.

In particular, the models that come from LEF of `W` (regular representations
of finite local models) can never be glued with a permutation seam. A
head-keeping periodic model needs a seam `V`, or blocks, that are not
monomial.

**What an obstruction must be.** By the Theorem, `h` is in `Rad_MF(H')`
iff some window `(F, delta)` has the following property. For every `m >= 1`
and every head-keeping `(F^(m), delta)`-model `theta`, the twisted model
`(theta o alpha^m)|_F` is more than `delta` from the unitary orbit of
`theta|_F`.
* So a T-free obstruction is a property of approximate models on one fixed
  window. It must separate `theta o alpha^m` from `theta` up to conjugacy,
  for all `m` at once and uniformly in the dimension.
* Invariants that `alpha^m` fixes for some `m` do not qualify. Examples are
  everything read off a finite quotient of `H'`, and normalized traces.
  For traces: pad `theta` and `V` by a large trivial summand. The padded
  data still satisfy (PC) exactly when the unpadded data do, and the head
  still survives. But the normalized traces of `theta o alpha^m` and of
  `theta` then agree up to any prescribed error on `F`.

**Status of the parts.**
* The Theorem and Corollaries 1 to 3 are proved in the route.
* Whether (PC) holds for `(W, Ad c, x_13(Q))` is OPEN. It is exactly the
  sibling spark "is H' MF with the head", now with a seam required only up
  to a window-dependent power of `c`.
