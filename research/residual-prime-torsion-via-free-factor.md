---
rg: 2
id: residual-prime-torsion-via-free-factor
kind: route
title: Add a free cyclic factor to kill the finite radical while keeping the invisible torsion
target: hyperbolic-group-trivial-radical-residual-prime-torsion
requires:
  - non-virtually-torsion-free-hyperbolic-group
  - finite-torsion-carrier-virtual-torsionfree-criterion
---

Let `G` be word-hyperbolic and not virtually torsion-free.  By the finite
torsion-carrier criterion (hyperbolic groups have finitely many conjugacy
classes of finite subgroups), `R_f(G)` contains a nonidentity element of finite
order; a suitable power `x` has prime order.  Put

```text
H = G * Z,     Z = <t>.
```

1. **`H` is word-hyperbolic.**  A free product is hyperbolic relative to its
   factors, and a finitely generated group hyperbolic relative to hyperbolic
   subgroups is word-hyperbolic.  Both statements are quoted in the
   introduction of Osin, arXiv:math/0510195v3, pp. 2--3 (read 2026-09-11:
   "Free products of groups and their small cancellation quotients ... are
   hyperbolic relative to the factors" and "if a finitely generated group `G`
   is hyperbolic relative to a collection of hyperbolic subgroups, then `G` is
   a hyperbolic group itself").
2. **`x in R_f(H)`.**  Every homomorphism `H -> F` to a finite group restricts
   to a homomorphism `G -> F`, which kills `R_f(G)`.
3. **`H` has trivial finite radical.**  Let `K ⊴ H` be finite.  A finite
   subgroup of a free product is conjugate into a factor (Kurosh subgroup
   theorem, or: a finite group acting on the Bass--Serre tree fixes a vertex).
   `Z` is torsion-free, so `K <= uGu^(-1)` for some `u in H`.  Normality gives
   `K = tKt^(-1) <= tuGu^(-1)t^(-1)`, hence

   ```text
   K <= u ( G  intersect  w G w^(-1) ) u^(-1),     w = u^(-1) t u.
   ```

   The image of `w` under the retraction `H -> Z` is `t != 1`, so `w notin G`.
   A factor of a free product is malnormal (normal forms), so
   `G intersect wGw^(-1) = 1` and `K = 1`.

So `H` has trivial finite radical and prime-order torsion `x` in its finite
residual.  `H` is non-elementary (it contains the free product of a nontrivial
group with `Z`), so the dichotomy's non-elementary alternative applies to `x`.
`QED`

The free factor does all the work of discarding a central finite residual:
even when `R_f(G)` is finite and central in the finite radical of `G` (the
persistent-class shape), `R_f(H)` contains the normal closure of `x` in `H`,
which is infinite.
