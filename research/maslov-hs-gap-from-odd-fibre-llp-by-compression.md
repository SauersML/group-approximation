---
rg: 2
id: maslov-hs-gap-from-odd-fibre-llp-by-compression
kind: route
title: Lift a tracial Maslov model through LLP, dilate it by Stinespring, and hit the uniform compression gap
target: maslov-mod3-projective-defect-gap
requires:
  - sp4-mod3-twisted-fibres-have-llp
  - deligne-sep8-moving-parameter-compression-gap
---

Let `A=C^*(Gamma;alpha)`, `Gamma=Sp_4(Z)`, with canonical unitaries `u_g`.
Adjusting `alpha` by a coboundary `f:Gamma->T` changes `u_g` to `f(g)u_g`
and changes no commutator norm below. So we may take
`alpha=exp(2 pi i t b)` with `t=1/3` (or `2/3` for `alpha^2`), where `b` is
the integral covering cocycle. Fix a Kazhdan pair `(S,kappa)` for `Gamma`
as in `deligne-sep8-moving-parameter-compression-gap`.

**Step 1 (a failing gap gives a tracial homomorphism).** If the defect gap
fails, there are unitary tuples in `U(d_n)` whose normalized-HS
`alpha`-relator defects tend to zero. Along a free ultrafilter `omega`,
their classes satisfy the `alpha`-projective relations exactly in
`M_omega=prod_omega (M_(d_n),tr_(d_n))`. The universal property of the
twisted group C-star algebra gives a unital star-homomorphism
`Theta:A -> M_omega`. This is the map built in
`brown-ucp-generator-lift-closes-maslov-gap`. Choose unitary
representatives `V_n(s)` of `Theta(u_s)`, `s in S`.

**Step 2 (LLP gives coordinate ucp maps).** Realize `M_omega` as the
quotient of `prod_n M_(d_n)` by the ideal of bounded sequences whose
normalized two-norm tends to zero along `omega`. Let `E` be the finite
dimensional operator system spanned by `1`, `u_s` and `u_s^*` for `s in S`.
By the lifting property of `A` (Kirchberg's LLP, used in the same form as
(LHA2) of `llp-makes-hyperlinear-traces-amenable`), `Theta|_E` has a ucp lift
`E -> prod_n M_(d_n)`. Extend each coordinate to a ucp map
`phi_n:A -> M_(d_n)` by Arveson's extension theorem. Then

```text
eta_n = max_(s in S) ||phi_n(u_s)-V_n(s)||_(2,tr_(d_n)) ->_omega 0.   (LC1)
```

**Step 3 (Stinespring).** Write `phi_n(a)=W_n^* sigma_n(a) W_n` with
`sigma_n` a unital representation of `A` on `H_n` and `W_n` an isometry
from `C^(d_n)`. Then `pi_n(g)=sigma_n(u_g)` is an exact
`exp(2 pi i t b)`-projective unitary representation of `Gamma`, and
`P_n=W_nW_n^*` is a projection of rank `d_n`. Identify `P_nH_n` with
`C^(d_n)` by `W_n`. The corner `A_s=P_n pi_n(s) P_n` is then `phi_n(u_s)`.
The identity used in `deligne-sep8-moving-parameter-compression-gap-proof`,

```text
||[P,U]||_HS^2 = 2 Tr(P-(PUP)^*(PUP))    (U unitary, P finite rank),
```

gives

```text
||[P_n,pi_n(s)]||_HS^2 / d_n = 2 tr_(d_n)(I-phi_n(u_s)^*phi_n(u_s)).
```

**Step 4 (the estimate).** Put `Y=phi_n(u_s)` and `V=V_n(s)`. Since
`I=V^*V`, we have `I-Y^*Y=V^*(V-Y)+(V-Y)^*Y`. Here `Y` is a contraction,
and `|tr(A^*B)|<=||A||_2||B||_2` for the normalized trace. So

```text
tr_(d_n)(I-Y^*Y) <= 2||V-Y||_2 <= 2 eta_n,
max_(s in S) ||[P_n,pi_n(s)]||_HS / sqrt(rank P_n) <= 2 sqrt(eta_n).
```

**Step 5 (contradiction).** Since `t` is `1/3` or `2/3`, it lies outside
`{0,1/2}`. So `deligne-sep8-moving-parameter-compression-gap` bounds the
left side below by `kappa>0` for every `n`. But by (LC1) the right side
tends to zero along `omega`. This is a contradiction, so the defect gap
holds in both nontrivial sectors.

**What is and is not used.** Only local lifts on the Kazhdan generator system
are needed, and only for homomorphisms into tracial matrix ultraproducts.
Restricting the quotient to the norm corona `prod M_(d_n)/(+) M_(d_n)`, the
same Steps 2-5 exclude operator-norm models directly, because
`||.||_2<=||.||_op`. By the vacuity principle of
`twisted-generator-liftability-implies-e3-nonhyperlinear`, liftability
for all homomorphisms into one of these quotients is equivalent to the
corresponding gap. The genuine strength of the requirement lies in LLP
quantifying over all quotients and all ucp maps.

**Relation to nearby nodes.**

- `brown-ucp-generator-lift-closes-maslov-gap`: that assumes generator liftability TGL1 for every tracial homomorphism, which is goal-hard by vacuity, and uses the no-amenable-trace theorem; this assumes the lifting property of the twisted fibre and uses only the Kazhdan compression gap.
- `nonhyperlinear-from-odd-maslov-fibre-llp`: that sends fibre LLP to the flagship non-hyperlinear-group through amenable traces and Thom's corner criterion; this sends fibre LLP to the Maslov defect gap itself, so the same hole also feeds the Deligne HS collapse, stable non-hyperlinearity and, through deligne-opnorm-sectors-empty-from-hs-defect-gap, the MF-radical goal.
- `twisted-generator-liftability-implies-e3-nonhyperlinear`: that proves generator liftability excludes tracial models through the Kazhdan corner lemma; this derives the needed lifts from LLP of the fibre and closes with the quantitative compression gap.
