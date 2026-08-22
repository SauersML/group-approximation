---
rg: 2
id: sp4-fd-projective-multiplier-finiteness-proof
kind: route
title: Determinant torsion plus the Deligne circle plus Stover's finite-quotient kernel bound the realizable classes
target: sp4-fd-projective-multiplier-is-finite
requires: []
---

All literature statements below were source-verified 2026-08-21.
Inputs: Stover, arXiv:2407.07680, Theorem 1.5 and the sentence following
it; Hain, arXiv:math/0203057, Section 2 and the `A_2` computation quoted
there from Igusa; Balasubramanian--Omar, arXiv:1308.4934, Theorem 4.1
(Bender's presentation).  Everything else is hand-checkable homological
algebra plus Malcev's theorem on finitely generated linear groups.

Write `Gamma = Sp_4(Z)`, `T = R/Z` (additive), `G~` the universal cover
of `Sp_4(R)`, `Gamma~` the preimage of `Gamma` in `G~`.  The deck group
`pi_1(Sp_4(R)) = Z<z>` is central in `G~`, so

```text
1 -> Z<z> -> Gamma~ -> Gamma -> 1                             (FP1)
```

is a central extension; let `w in H^2(Gamma,Z)` be its class.  For
`n >= 1` let `Gamma_n` be the preimage of `Gamma` in the degree-`n`
connected cover `G~/<z^n>`; then `Gamma_n = Gamma~/<z^n>` is the central
`Z/n`-extension with class the pushforward of `w` along `Z -> Z/n`.

**Stover's input** (arXiv:2407.07680, Thm 1.5, Deligne): for `g >= 2`,
`n >= 3`, `Gamma_n` is a `Z/n` central extension of `Sp_2g(Z)` that is
not residually finite; moreover, for the center `Z = Z/n` of `Gamma_n`,
"the intersection of the kernels of all homomorphisms from `Gamma_n`
onto finite groups is `2Z`".

**Step 0 (H_2 is finitely generated of rank one).**  `Gamma` has a
finite presentation with 2 generators and 8 defining relations (Bender,
J. Algebra 65 (1980) 328-331, quoted as Theorem 4.1 of arXiv:1308.4934).
By Hopf's formula, for `Gamma = F/N`, `H_2(Gamma,Z) = (N cap [F,F])/[F,N]`
is a subgroup of `N/[F,N]`, which is generated as an abelian group by the
images of the 8 relators (conjugates of a relator are congruent to it
mod `[F,N]`); hence `H_2(Gamma,Z)` is finitely generated, and `H_1`,
`H_2` of `Gamma` are finitely generated.  Rank: by universal coefficients
`H^2(Gamma,Q) = Hom(H_2(Gamma,Z),Q)` (Ext into the divisible group `Q`
vanishes), and Hain (arXiv:math/0203057, Section 2) records the natural
isomorphism `H^*(Sp_g(Z),Q) = H^*(A_g,Q)` (Siegel space is contractible
and the action is discontinuous and virtually free) together with
Igusa's computation that the rational cohomology of `A_2` is
"1-dimensional in degrees 0 and 2, and trivial elsewhere".  So
`Hom(H_2,Q) = Q` and

```text
H_2(Gamma,Z) = Z<h> + F,   F finite,  t := |F|.               (FP2)
```

**Step 1 (coefficient structure).**  Universal coefficients with the
divisible group `T` (Ext term vanishes) gives, naturally,

```text
H^2(Gamma,T) = Hom(H_2(Gamma,Z),T) = T x Hom(F,T).            (FP3)
```

**Step 2 (R is a torsion subgroup).**  `R` is a subgroup: tensor
products multiply exact cocycles and complex conjugates invert them,
both staying finite-dimensional.  Torsion: if `pi: Gamma -> U(d)` has
cocycle `c` then taking determinants gives `c(g,h)^d =
det pi(g) det pi(h) det pi(gh)^{-1}`, a coboundary; so `d.[c] = 0`.
Hence `R` lies in the torsion subgroup of `(FP3)`.

**Step 3 (the Deligne circle is the identity component).**  The 5-term
exact sequence of `(FP1)` with trivial coefficients `T` has
transgression `tg: Hom(Z,T) -> H^2(Gamma,T)`, `tg(psi) = -psi_*(w)`
(cocycle-level computation below), and `im(tg) subset ker(infl)`.  Put
`D := { psi_*(w) : psi in Hom(Z,T) }`.  Under `(FP3)` and the
naturality of universal coefficients, `psi_*(w)` corresponds to
`psi o phi_w` where `phi_w in Hom(H_2,Z)` is the Hom-part of `w`
(the `Ext(H_1,Z)`-part of `w` dies in `Ext(H_1,T) = 0`).  Since
`Hom(F,Z) = 0`, `phi_w = d . h^*` for some integer `d`.

*`d != 0`:* otherwise `w` lies in the image of `Ext(H_1(Gamma),Z)`,
a finite group (`H_1` finitely generated), so `w` has finite order
`t_0`; choose `n >= 3` coprime to `t_0`; the class of `Gamma_n` (the
pushforward of `w`) is then killed by both `t_0` and `n`, hence zero,
so `Gamma_n = Gamma x Z/n`.  But `Gamma` is finitely generated and
linear, hence residually finite (Malcev), and then so is
`Gamma x Z/n` — contradicting Stover's Theorem 1.5.  So `d != 0`.

*`D` is the full circle:* `D` is the image of the divisible group
`Hom(Z,T) = T` under a homomorphism, hence divisible, so its projection
to the finite factor `Hom(F,T)` is trivial; and its circle coordinate
`psi(d) = d.psi(1)` runs over ALL of `T` because `d != 0` and `T` is
divisible.  Hence

```text
D = T x {0} = identity component of H^2(Gamma,T).             (FP4)
```

**Step 4 (realizable classes on the circle have order <= 2).**  Let
`gamma in R cap D`, realized by `pi: Gamma -> U(d')` with normalized
exact cocycle `c` (normalize so `c(1,.) = c(.,1) = 1`, `pi(1) = 1`).
Since `gamma in D subset ker(infl)` (for `psi_*(w)` the pullback
cocycle is `psi o (p^*w~)` and `p^*w~ = -delta k` where
`x = z^{k(x)} sigma(p(x))` for a set-section `sigma`), we get
`p^*c = delta b` for some `b: Gamma~ -> T`.  On the central `Z`,
`p^*c` is identically `1`, so `psi_0 := b|_Z: Z -> T` is a
homomorphism, and `b(z^k x) = psi_0(k) + b(x)` for all `x`.  Writing
`sigma(g)sigma(h) = z^{w~(g,h)} sigma(gh)` and evaluating
`delta b` on `(sigma(g), sigma(h))` gives

```text
c = delta(b o sigma) - psi_0 o w~,   i.e.  gamma = -(psi_0)_*(w).  (FP5)
```

Define `rho(x) := pi(p(x)) - b(x)` twist, i.e.
`rho(x) = e(-b(x)) pi(p(x))` with `e(s) = exp(2 pi i s)`; by
`p^*c = delta b` this `rho` is a GENUINE unitary representation of
`Gamma~` on `C^{d'}`, and `rho(z^k) = e(-psi_0(k)) . 1` is scalar.
By `(FP4)` and `(FP5)`, the order `n` of `gamma` equals the order of
`d . psi_0(1)` in `T`, which divides the order of `psi_0(1)`.  Suppose
`n >= 3`.  Then `psi_0(1)` has order `>= 3`, so `rho(2z) != 1`.  The
group `Gamma~` is finitely generated (lifts of Bender's two generators
plus `z`), so `rho(Gamma~)` is a finitely generated linear group, hence
residually finite (Malcev); pick a finite quotient `q` of `rho(Gamma~)`
with `q(rho(2z)) != 1` and set `Phi := q o rho: Gamma~ ->> E`, `E`
finite.  Let `M` be the order of `Phi(z)`; since `Phi(z)^2 =
Phi(2z) != 1`, `M >= 3`.  `Phi` kills `z^M`, hence factors through
`Gamma_M = Gamma~/<z^M>` as a homomorphism ONTO the finite group `E`
that is nontrivial on the image of `2z`, an element of `2(Z/M)` —
contradicting Stover's kernel sentence for `Gamma_M`.  Hence `n <= 2`:

```text
R cap D subset {0, 1/2}.                                      (FP6)
```

**Step 5 (assembly).**  For `alpha in R` write `alpha = (alpha_T,
alpha_F)` under `(FP3)`.  Then `t.alpha = (t.alpha_T, 0) in D`, and
`t.alpha in R` (Step 2, subgroup), so by `(FP6)` `2t.alpha = 0`.  A
bounded-exponent subgroup of `T x Hom(F,T)` is finite:
`R subset {x : 2t.x = 0}`, of cardinality at most `2t . t`.  This
proves `(FM1)` and the theorem.
