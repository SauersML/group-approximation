---
rg: 2
id: leavitt-unit-projective-hs-lift-proof
kind: route
title: Lift a projective ultraproduct model through the vanishing Schur multiplier and use simplicity
target: leavitt-unit-hyperlinear-iff-projective-hs-model
requires:
  - leavitt-steinberg-map-iso-from-rank-three
  - leavitt-gl-equals-el-and-perfect-unit-group
  - binary-leavitt-unit-group-is-simple
---

Write `H = L_(F_2)(1,2)^x`.

**(1 => 2).** A hyperlinear countable group has maps `phi_n` with genuine
defects `||phi_n(g)phi_n(h) - phi_n(gh)||_2 -> 0` and `tr phi_n(g) -> 0` for
`g != 1`, by the standard tensor-power amplification. Then `pdef_n` is at most
the genuine defect. For a unitary `u` and the normalized trace,

```text
min_(lambda in T) ||u - lambda||_2^2 = 2 - 2|tr u|,
```

so `pdist_n(g) -> sqrt 2` for every `g != 1`.

**(2 => 1).**
1. **The ultraproduct image.** Fix a free ultrafilter `omega` with
   `lim_omega pdist_n(g_0) = c > 0`, put `M = prod_omega M_(d_n)`, and
   `x(g) = (phi_n(g))_omega in U(M)`. For `g,h`, choose minimizers `lambda_n`
   in `pdef_n(g,h)` and let `lambda = lim_omega lambda_n`. Then
   `||phi_n(g)phi_n(h) - lambda phi_n(gh)||_2 <= pdef_n(g,h) + |lambda_n - lambda|`,
   so `x(g)x(h) = lambda x(gh)`. Hence `pi(g) = x(g)T` is a homomorphism
   `H -> U(M)/T`.
2. **Lifting.** Pull back `1 -> T -> U(M) -> U(M)/T -> 1` along `pi`. This
   gives a central extension of the abstract group `H` by the abstract group
   `T`. Its class lies in

   ```text
   H^2(H;T) = Hom(H_2(H;Z),T) (+) Ext(H_1(H;Z),T)
   ```

   by universal coefficients. Now `H_1(H;Z) = 0` because `H` is perfect
   (`leavitt-gl-equals-el-and-perfect-unit-group`), and `H_2(H;Z) = 0` by
   `(KH1)` of `leavitt-steinberg-map-iso-from-rank-three` at `r = 1`. So the
   extension splits, and there is a homomorphism `rho : H -> U(M)` with
   `rho(g) in x(g)T`. Two splittings differ by a homomorphism `H -> T`, which
   is trivial since `H` is perfect, so `rho` is unique.
3. **Nontriviality.** For every `lambda in T`,
   `||x(g_0) - lambda||_2 = lim_omega ||phi_n(g_0) - lambda||_2 >= c`. So
   `rho(g_0)` is not scalar, and in particular `rho(g_0) != 1`.
4. **Faithfulness.** The kernel of `rho` is a proper normal subgroup of `H`,
   hence trivial by `binary-leavitt-unit-group-is-simple`. So `rho` is
   injective, and `||rho(g) - 1||_2 > 0` for `g != 1` because the trace on `M`
   is faithful. A countable subgroup of `U(prod_omega M_(d_n))` is hyperlinear.

**The two consequences in the claim.**
- If `w` has exponent sum zero in each letter, write `rho(g) = mu(g) x(g)`
  with `mu(g) in T`. The scalars cancel, so `w(x) = w(rho) = rho(w) = 1`.
- A commutator `[a,b]` is such a word. So `[a,b] = 1` in `H` forces
  `lim_omega ||[phi_n(a),phi_n(b)] - 1||_2 = 0`. For a finite subgroup `F`, the
  projective class of `pi|_F` is the class of the genuine representation
  `rho|_F`, which is zero.
