---
rg: 2
id: deligne-parameter-tori-corestrict-only-through-maslov-line
kind: claim
title: Tensor induction of norm models from finite-index subgroups of Sp4(Z) sees only the Maslov-invariant part of their parameter tori
distinct_from:
  ce-twist-set-is-a-hecke-stable-closed-subgroup: that is the tracial (Connes-embeddable) twist set with tensor induction as a transport map; this is the operator-norm set, proves the transfer identities TI o res = index and res o TI = sum of conjugates, and uses them to show the non-Maslov directions corestrict to zero.
  deligne-parameter-group-is-a-virtual-invariant: that moves parameters along the Maslov line only, by restriction, additive twisted induction and division; this treats the whole multiplier torus of a finite-index subgroup, including the non-Maslov directions, and the multiplicative (tensor) induction back to Sp4(Z).
  deligne-finite-parameter-group-has-period-prime-to-three: that is the open period claim; this proves a transport dichotomy that kills one class of attacks on it and leaves it OPEN.
---

**ESTABLISHED** (elementary, given the imports of the route).

**Setting.** `Gamma = Sp_4(Z)`, `b` the integral universal-covering cocycle, `e(t) = exp(2 pi i t)`, and `P_op` as
in `deligne-sep7-norm-parameter-closed-subgroup`. For a finite-index subgroup `H` put

```text
P(H) = { [omega] in H^2(H,T) : there are U_n : H -> U(d_n), U_n(e) = I, with
         ||U_n(g)U_n(h) - omega(g,h)U_n(gh)||_op -> 0 for every fixed g, h }.
R(H) = { [omega] : omega is the multiplier of an exact projective rep H -> U(d), d < infinity }.
```

Let `T_0(H)` be the identity component of `H^2(H,T) = Hom(H_2(H),T)`, with Lie algebra `H^2(H,R)`. Let
`P(H)^0` be the identity component of `P(H)` and `W(H) <= H^2(H,R)` its Lie algebra. Let `TI` be tensor induction
`H^2(H,T) -> H^2(Gamma,T)`, with cochain formula as in the route, and `tau = d(TI) : H^2(H,R) -> H^2(Gamma,R)`.

**THEOREM.**

1. **(T1) Structure.** `P(H)` is a closed subgroup of `H^2(H,T)` and `R(H) <= P(H)`.
   - Restriction maps `P(Gamma)` into `P(H)`.
   - `TI` maps `P(H)` into `P(Gamma)` and `R(H)` into `R(Gamma)`.
   - For normal `H`, `P(H)` is stable under the conjugation action of `G = Gamma/H`.
   - `P(Gamma) cap T_0(Gamma) = { e(theta b) : theta in P_op }`, and `T_0(Gamma)` is exactly the Maslov circle
     `{ e(theta b) }`.
2. **(T2) Transfer identities.** `TI o res = [Gamma:H]`. For normal `H`, `res o TI = sum_(g in G) g^*`. The same
   identities hold for `tau` on real cohomology.
3. **(T3) Dichotomy.** For every finite-index `H`, the following are equivalent:
   - `P_op = R/Z`;
   - `res[b] in W(H)`;
   - (for normal `H`) `W(H)^G != 0`.

   If instead `P_op` is finite (`= (1/m)Z/Z`), then:
   - `tau(W(H)) = 0`;
   - `TI(P(H)^0) = 0`;
   - for normal `H`, `W(H)` lies in the sum of the nontrivial `G`-isotypic components of `H^2(H,R)`.

   So on the finite branch, `TI` factors through the finite component group `P(H)/P(H)^0`.
4. **(T4) Exact points.** `R(Gamma) cap T_0(Gamma) <= { e(theta b) : theta in (1/2)Z/Z }`. Hence
   `TI(y + p)`, for `y in R(H)` and `p in P(H)^0`, lies in `{0, e(b/2)}` whenever it lies on the Maslov circle, on the
   finite branch.

**Corollary (class killed).** Consider an attempt to prove `1/3 in P_op => P_op = R/Z`, or to produce any new
parameter in `P_op`, by building norm models of a finite-index `H` in some multiplier direction and
tensor-inducing them back to `Gamma`. The attempt may use Hecke correspondences `TI o c_g^* o res` and any
continuous deformation inside `P(H)`. It then dies:

- *Continuous families.* These die at the step "apply `tau`". The invariant is the `G`-invariant part `W(H)^G` of
  the parameter Lie algebra, which is the Maslov component `W(H) cap R res[b]`. By (T3) it is nonzero only when
  `P_op = R/Z` already holds. Every continuous family of norm models in the Mess (non-Maslov) directions of
  `H^2(H,R)` corestricts to the zero class.
- *Exact points.* Exactly realizable, that is profinite, points die at Mal'cev plus Deligne (T4).
- *What survives.* To reach `e(b/3)` by tensor induction on the finite branch, one needs a point
  `y in P(H) \ (P(H)^0 + R(H))`. That is a class of a non-identity component of `P(H)` that has norm models but no
  exact finite-dimensional realization, with `TI(y) = e(b/3)`.

This proves nothing about whether `1/3 in P_op`. `deligne-finite-parameter-group-has-period-prime-to-three` stays OPEN.
