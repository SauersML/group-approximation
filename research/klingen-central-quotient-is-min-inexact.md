---
rg: 2
id: klingen-central-quotient-is-min-inexact
kind: claim
title: Every Klingen long-root central quotient of Sp4(Z) is min-inexact against B(l^2), hence not locally split
distinct_from:
  klingen-center-kills-isw-condition-one: that shows the Klingen centre cannot serve as the Ioana--Spaas--Wiersma subgroup Lambda (H^2(Z,T)=0); this is about the QUOTIENTS by that centre, and shows that each quotient map C*(E) -> C*(Z^2 x| SL_2(Z), sigma_t) does not commute with the min tensor product with B(l^2).
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that audits a rerun of ISW Theorem A on the parabolic itself; this closes the different route of pushing the non-LLP of Z^2 x| SL_2(Z) (or of its twisted fibres) up to the parabolic through a central quotient.
  kazhdan-fd-block-representation-algebras-are-not-exact: that is non-exactness of a block representation algebra of a Kazhdan group; this is inexactness of specific central-quotient sequences of a full group C*-algebra, obtained from relative (T) and twisted diagonal representations.
  klingen-twisted-fibres-all-fail-llp: that is failure of the LLP for each fibre A_t; this is failure of exactness of each sequence 0 -> I_t -> C*(E) -> A_t -> 0 after tensoring with B(l^2), which is what blocks lifting the LLP-failure to C*(E).
  sp2g-z-full-c-star-algebra-has-llp: this is a fence on one proof mechanism (quotient permanence of the LLP), not a decision of the root.
artifacts:
  - research/artifacts/klingen-central-quotient-2026-09-16.md
---

**CLAIM.**  In `Sp_4(Z)`, with basis `(e1, e2, f1, f2)` and
`J = [[0, I], [-I, 0]]`, let `E = { N(v,c) L(g) }`.  Here `N(v,c)` runs over the
integral Klingen radical and `L(g)` over the Levi copy of `SL_2(Z)` acting on
`span(e2, f2)` (artifact §0).

`E` is isomorphic to the central extension `Z x_c Lambda` of
`Lambda = Z^2 x| SL_2(Z)`.  The cocycle is exactly the one used by
Ioana--Spaas--Wiersma (arXiv:2006.01874, proof of Corollary B):
`c((v,g),(w,h)) = omega(v, g w)`.  The generator `z` of the centre `Z` is the
long-root element `N(0,1)`.

For `t in R` let `q_t : C^*(E) -> A_t = C^*(Lambda, exp(2 pi i t c))` be the
quotient by `u_z = e^{2 pi i t}`, with kernel `I_t`.  Then, for EVERY `t`:

```text
ker( q_t (x) id : C^*(E) (x)_min B(l^2) -> A_t (x)_min B(l^2) )
    is strictly larger than I_t (x)_min B(l^2).
```

Moreover, for the finite set `g_1, ..., g_m` of ISW's Claim `gap`, the operator
system `span{1, W_t(g_i), W_t(g_i)^*}` of `A_t` admits no ucp lift to `C^*(E)`.

**Witness.**

- Choose rationals `s_n -> t` with `0 < |s_n - t| < 1/2`.
- Let `rho_n` be a finite-dimensional unitary representation of `E` with
  `rho_n(z) = e^{2 pi i s_n}`, factoring through `E mod k_n`.  Put
  `pi_n = rho_n(0, .)`.
- Lift ISW's element to `t~ = sum_i u_{(0,g_i)} (x) (conj pi_n(g_i))_n`.

**Upper bound.**  The image of `t~` in `A_t (x)_min prod_n M_{d_n}` has norm at
most `D < m`.  This is ISW's Claim `gap`, applied to the projective representations
`W_u (x) conj(pi_n)`.  Their cocycle `exp(2 pi i (t - s_n) c)` is not symmetric on
`Z^2`, hence not a coboundary there.

**Lower bound.**  The distance from `t~` to `I_t (x)_min prod_n M_{d_n}` is at
least `m`.

- The representations `rho_n (x) ev_n` kill `I_t` asymptotically, because
  `rho_n(u_z) - e^{2 pi i t} -> 0`.
- The maximally entangled vector is fixed by `U (x) conj(U)`.

**Transfer.**  The block-diagonal conditional expectation moves the gap to
`B(l^2)`.

**Consequence.**  Hypothesis (EX) of the quotient-permanence lemma ("LLP passes to
`A/I` when `0 -> I -> A -> A/I -> 0` stays exact after `(x)_min B(l^2)`") fails
for every `(C^*(E), I_t)`.

- So neither ISW's theorem that `C^*(Lambda)` fails the LLP, nor the failure of
  the LLP for the fibres `A_t` (`klingen-twisted-fibres-all-fail-llp`), can be
  transported to `C^*(E)` by these quotients.  The same holds for
  `C^*(Sp_4(Z))`.
- This holds unconditionally, whether or not `C^*(E)` has the LLP.
- The lifted witness has `||t~||_max = ||t~||_min = m` on `C^*(E)`.  Its max/min
  defect at the fibre `t` is compensated at the neighbouring fibres `s_n`.

**Side correction** (artifact §0, (F6)).  With this lattice, the integral Klingen
radical has commutator `[N(e2,0), N(f2,0)] = N(0,2)`.  So it is the index-two
overgroup `H_omega` of `H_3(Z)`, not `H_3(Z)` itself.

## Attempts

- 2026-09-16 (swarm-sp2g-z-full-c-star-algebra-has): proved at `t = 0` (artifact
  §3), then at every `t` (artifact §3A).  Both are direct proofs; see route
  `klingen-central-quotient-min-inexact-proof`.
