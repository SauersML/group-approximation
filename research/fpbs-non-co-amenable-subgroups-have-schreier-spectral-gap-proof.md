---
rg: 2
id: fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap-proof
kind: route
title: Følner sets give invariant means, Eymard induction lifts means to the group, and the Cheeger inequality bounds the Schreier operator
target: fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap
requires: []
---

Notation is that of the claim. Each `x -> xs` is a bijection of `I\Gamma`, and
`A(x,y) = #{s in S : xs = y}` is symmetric, because `s -> s^(-1)` bijects arcs
`x -> y` with arcs `y -> x`. So `P = A/D` is a bounded self-adjoint operator
with nonnegative entries.

**(a), step 1: `h = 0` gives an invariant mean.** Let `F_n` be finite with
`|∂F_n|/|F_n| -> 0`. For `s in S`:
- `|F_n s \ F_n| <= |∂F_n|`, since these points are the endpoints of arcs
  `(x,s)` leaving `F_n`;
- `|F_n \ F_n s| = |F_n s^(-1) \ F_n| <= |∂F_n|`.

Put `m_n(phi) = |F_n|^(-1) sum_(x in F_n) phi(x)`. Then
`|m_n(phi(· s)) - m_n(phi)| <= ||phi||_∞ |F_n s Δ F_n| / |F_n| -> 0`. A weak*
cluster point of `(m_n)` is a mean invariant under each `s in S`, hence under
`Gamma`, and `I` is co-amenable. Contrapositive: if `I` is not co-amenable,
then `h > 0`.

**(a), step 2: Cheeger.** Take `g >= 0` finitely supported.
- *Co-area.* An arc `(x,s)` with exactly one of `x, xs` in `{g > t}` is a
  boundary arc of that set, or the reverse of one. So

  ```text
  sum_(x,s) |g(x) - g(xs)| = 2 ∫_0^∞ |∂{g > t}| dt >= 2h ∫_0^∞ |{g > t}| dt = 2h sum_x g(x).
  ```

- *Apply it to `g = f^2`* with `f >= 0`, and use Cauchy–Schwarz:

  ```text
  2h ||f||^2 <= (sum_(x,s) (f(x)-f(xs))^2)^(1/2) (sum_(x,s) (f(x)+f(xs))^2)^(1/2)
             <= (2D <(I-P)f,f>)^(1/2) (4D ||f||^2)^(1/2).
  ```

  Here `<(I-P)f,f> = (2D)^(-1) sum_(x,s) (f(x)-f(xs))^2`, and
  `sum_(x,s) (f(x)+f(xs))^2 <= 2 sum_(x,s) (f(x)^2 + f(xs)^2) = 4D ||f||^2`.
- *Result.* `<Pf,f> <= (1 - h^2/(2D^2)) ||f||^2` for `f >= 0` finitely
  supported, and by density for `f >= 0` in `ℓ^2`.
- *All `f`.* For arbitrary `f`, `|<Pf,f>| <= <P|f|,|f|>`, because `P` has
  nonnegative entries. Since `P` is self-adjoint,
  `||P|| = sup_(||f||=1) |<Pf,f>| <= 1 - h^2/(2D^2)`.
- *Return probabilities.* `P^m(I,I) = <P^m δ_I, δ_I> <= ||P||^m`, so
  `rho_I <= ||P||`.

**(b): Eymard induction.** Let `I` be amenable and co-amenable. Let `n` be a
right-invariant mean on `ℓ^∞(I)`, which exists since `I` is amenable, and `m`
a `Gamma`-invariant mean on `ℓ^∞(I\Gamma)`. Choose a section `sigma` with
`sigma(x) in x` for every coset `x`. For `f in ℓ^∞(Gamma)` put

```text
f~(x) = n( i -> f(i sigma(x)) ),        M(f) = m(f~).
```

- *Independence of the section.* Another section differs by
  `sigma'(x) = i_0 sigma(x)`, which right-translates the function
  `i -> f(i sigma(x))`. Right invariance of `n` shows `f~` does not change.
- *`M` is a mean.* It is positive, with `M(1) = 1`.
- *Right invariance of `M`.* For `gamma in Gamma`, put
  `f_gamma(g) = f(g gamma)`. Then
  `f_gamma~(x) = n(i -> f(i sigma(x) gamma))`, and `sigma(x) gamma` lies in the
  coset `x gamma`, so `f_gamma~(x) = f~(x gamma)`. Invariance of `m` gives
  `M(f_gamma) = M(f)`.

So `Gamma` has a right-invariant mean and is amenable. Contrapositive: in a
nonamenable group every amenable subgroup is not co-amenable. Then (a) gives
`rho_I < 1`.

**(c).**
- *No infinite amenable subgroup.* An infinite amenable subgroup would be
  co-amenable by hypothesis, and not co-amenable by (b).
- *Periodic.* An element of infinite order generates an infinite amenable
  subgroup `Z`.
- *Infinite subgroups are nonamenable.* An infinite amenable subgroup is
  excluded above.
- *Normal subgroups.* For normal `N`, `N\Gamma = Gamma/N` with `Gamma` acting by
  right multiplication through the quotient. So co-amenability of `N` is
  amenability of `Gamma/N`.

**Class membership.**
- *Tarski monsters.* In a Tarski monster every proper subgroup is finite, so
  its only infinite subgroup is the group itself, and that subgroup is
  co-amenable. Ol'shanskii's monsters are nonamenable.
- *Groups with infinite-order elements.* They are excluded by periodicity.
- *Linear groups.* Burnside–Schur: a finitely generated periodic linear group
  is finite.
- *Acylindrically hyperbolic groups.* They contain loxodromic elements, which
  have infinite order (Dahmani–Guirardel–Osin).
- *Products `T x T'`.* With `T` infinite and `T'` nonamenable, `T` is an
  infinite subgroup with nonamenable quotient `T'`. ∎
