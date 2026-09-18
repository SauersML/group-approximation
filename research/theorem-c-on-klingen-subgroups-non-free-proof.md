---
rg: 2
id: theorem-c-on-klingen-subgroups-non-free-proof
kind: route
title: Vanishing of H^2 for free amenable actions, plus a relatively rigid commutator 1-cocycle
target: theorem-c-on-klingen-subgroups-needs-non-free-radical-action
requires: [klingen-heisenberg-pair-has-relative-property-t]
---

Imports.  These are verbatim from arXiv:2006.01874 (Ioana--Spaas--Wiersma),
read from the e-print TeX on 2026-09-17.

- (J1) Remark after Theorem C (line 287): "It is known that
  $\text{H}^2(\Gamma,\text{L}^0(X,\mathbb T))=0$, for any free ergodic
  p.m.p. action $\Gamma\curvearrowright (X,\mu)$, if $\Gamma$ is an
  amenable group \cite{CFW81}, a free group or more generally a
  treeable group \cite{Ki17}."
- (J2) The definition of relative property (T) (line 228), as quoted in
  `klingen-heisenberg-pair-relative-t-proof`.
- (J3) Theorem C (line 262), as summarised in the claim.

**(TK1).**  Theorem C requires `sigma|Lambda` ergodic.  If it is also
essentially free and `Lambda` is amenable or treeable, then (J1) gives
`H^2(Lambda, L^0(X,T)) = 0`.  So `c_n|Lambda` is a coboundary for every
`n`, contradicting the hypothesis.

**(TK2).**  Let `N = <n>` with `n = z^j`.  `n` is central in `Gamma`
because `Sigma` fixes `z`, and it acts trivially on `X`.  Write `M` for
the twisted crossed product `L^infty(X) x|_{sigma,c} Gamma`, with
canonical unitaries `u_g` satisfying `u_g u_h = c(g,h) u_{gh}` and
`u_g f u_g^* = sigma_g(f)`.

*Step 1 (the commutator cocycle).*  `u_n` commutes with `L^infty(X)`
because `sigma_n = id`.  Since `gn = ng`, we get
`u_g u_n u_g^* = beta(g) u_n` with `beta(g) = c(g,n) c(n,g)^*` in
`U(L^infty(X))`.  From `u_{gh} = c(g,h)^* u_g u_h` and commutativity of
`L^infty(X)`:

```text
beta(gh) u_n = u_g beta(h) u_n u_g^* = sigma_g(beta(h)) beta(g) u_n,
```

so `beta` is a 1-cocycle of `Gamma` in `U(L^infty(X))`.  Now let
`c = c_n` vary.  Then `beta_n(g) -> 1` in `L^2` for each `g`, because
`c_n -> 1` in `L^2` and all values are unitaries.

*Step 2 (relative (T)).*  `pi_n(g) xi = beta_n(g) sigma_g(xi)` is a
unitary representation of `Gamma` on `L^2(X)`, by the cocycle identity.
Also `||pi_n(g)1 - 1||_2 = ||beta_n(g) - 1||_2 -> 0`.  By
`(KHT)` and Step 0 of `klingen-heisenberg-pair-relative-t-proof`, the
pair `(Gamma, H)` has a Kazhdan pair.  Invariance under `H` implies
invariance under `Lambda`, so for large `n` there is a nonzero
`eta_n` in `L^2(X)` with `beta_n(h) sigma_h(eta_n) = eta_n` for `h` in
`Lambda`.  Then `|eta_n|` is `Lambda`-invariant, hence a nonzero
constant by ergodicity.  Normalising, `eta_n` is unitary and
`beta_n(h) = eta_n sigma_h(eta_n)^*` on `Lambda`.

*Step 3 (untwist).*  Put `w = eta_n u_n`.  `w` commutes with
`L^infty(X)`.  For `h` in `Lambda`:

```text
u_h w u_h^* = sigma_h(eta_n) beta_n(h) u_n = eta_n u_n = w.
```

Choose a transversal `S` for `N` in `Lambda` with `e` in `S`.  Define
`u'_{s n^a} = u_s w^a`.  Each `u'_lambda` is `b(lambda) u_lambda` with
`b(lambda)` in `U(L^infty(X))`, because `u_n^a` is `u_{n^a}` times a
unitary of `L^infty(X)`.  So the cocycle
`c'(lambda,mu) = u'_lambda u'_mu u'^*_{lambda mu}` is cohomologous to
`c_n|Lambda`.  Since `w` commutes with every `u_s` and with
`L^infty(X)`:

```text
u'_{lambda n^a} = u'_lambda w^a,
u'_{lambda n^a} u'_{mu n^b} = u'_lambda u'_mu w^{a+b} = c'(lambda,mu) u'_{lambda mu n^{a+b}},
```

so `c'(lambda n^a, mu n^b) = c'(lambda, mu)`.  Hence `c'` is inflated
from a cocycle on `Lambda/N`.

`Lambda/N` is a finite central extension of `Lambda/(Lambda ∩ <z>)`,
which is of finite index in `Z^2`.  This proves `(TK2)`.

**Remarks (not load-bearing).**

- Inflation from `Lambda/N` has kernel `T * e_N`.  Here `e_N` is the
  class of `N -> Lambda -> Lambda/N`, and `T = L^0(X,T)^Lambda` by
  ergodicity.  This follows from the Lyndon--Hochschild--Serre sequence,
  with `d_2` on `Hom(N, L^0)^{Lambda}`.  So the scalar area-form classes
  (the Corollary B supply on `Z^2 x| Sigma`) die on inflation, which
  matches `isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals`.
- If `z` acts essentially freely, then `Stab_Lambda(x)` meets the center
  trivially.  Its commutator subgroup lies in
  `[H,H] ∩ Stab = 1`, so it is abelian.  This is case (S2).
