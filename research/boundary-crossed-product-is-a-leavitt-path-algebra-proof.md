---
rg: 2
id: boundary-crossed-product-is-a-leavitt-path-algebra-proof
kind: route
title: An explicit Cuntz–Krieger family of cylinder projections and translated units, injective by simplicity and onto because it contains the generators
target: boundary-crossed-product-is-a-leavitt-path-algebra
requires:
  - leavitt-path-algebras-purely-infinite-simple-criterion
artifacts:
  - research/artifacts/sk-hyperlinear-boundary-a-reduction-2026-09-13.md
---

Convention for `L_k(E)`: `s(e) e = e = e r(e)`, `e^* e' = delta_(e,e') r(e)`, and `sum_(s(e)=v) e e^* = v` for every
vertex `v`. The edge `e_(ab)` has `s = a` and `r = b`. Two cylinder facts are used:
- (I1) `g C(w) = C(gw)` when the product `gw` is reduced;
- (I2) `C(a) = ⊔_(b != a^(-1)) C(ab)`, and `∂F_d = ⊔_(a in A) C(a)`.

**1. Relations.** Put `S_(ab) = P_(C(ab)) u_a`. By (I1), `u_a P_(C(b)) = P_(aC(b)) u_a = P_(C(ab)) u_a`, and
`S_(ab)^* = u_(a^(-1)) P_(C(ab)) = P_(C(b)) u_(a^(-1))`.
- `P_(C(a)) S_(ab) = S_(ab)`, since `C(ab) ⊆ C(a)`; and `S_(ab) P_(C(b)) = S_(ab)`.
- `S_(ab)^* S_(a'b') = u_(a^(-1)) P_(C(ab) ∩ C(a'b')) u_(a')`. This vanishes unless `(a,b) = (a',b')`, and then it
  equals `P_(a^(-1)C(ab)) = P_(C(b))`.
- `sum_(b != a^(-1)) S_(ab) S_(ab)^* = sum_b P_(C(ab)) = P_(C(a))` by (I2).
- The `P_(C(a))` are orthogonal idempotents with sum `1`.

So `rho` is a unital ring homomorphism.

**2. Injective.**
- `E_d` is finite and has no sinks: every vertex emits `2d-1 >= 3` edges.
- It is strongly connected. `a -> b` is an edge unless `b = a^(-1)`. In that case `a -> c -> a^(-1)` for any
  `c ∉ {a, a^(-1)}`, which exists because `2d >= 4`.
- Every cycle has an exit, since out-degrees are at least 2.

By `leavitt-path-algebras-purely-infinite-simple-criterion`, `L_k(E_d)` is simple. Since `rho(1) = 1 != 0`, `rho` is
injective.

**3. Onto.** `sum_(b != a^(-1)) S_(ab) = P_(C(a)) u_a`. The ghost edges `e_(a^(-1) b)^*` with `b != a` map to
`P_(C(b)) u_a`, and their sum is `(1 - P_(C(a))) u_a`. So `u_a` lies in the image for every letter `a`, hence so does
every `u_g`.

For a reduced word `w = ga` with `g` in `F_d`, (I1) gives `u_g P_(C(a)) u_(g^(-1)) = P_(C(w))`. So the image contains
every cylinder indicator. These span `LC(∂F_d, k)`, and together with the `u_g` they generate `R_∂`.
