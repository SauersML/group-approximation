---
rg: 2
id: hyperlinear-residual-amenable-restriction-proof
kind: route
title: Pass to the quotient by the kernel's residual and apply extension permanence
target: hyperlinear-residual-restricts-along-amenable-quotients
requires:
  - amenable-quotient-preserves-metric-approximability
  - hyperlinear-elementwise-visibility
  - local-approximation-properties-are-marked-closed
---

## Why sufficient

Write `Res(K)` as in the claim. All groups are countable.

**(R1) `K/Res(K)` is hyperlinear.** Put `Kbar = K/Res(K)` and let
`xbar != 1` in `Kbar`, the image of `x` in `K` with `x` not in `Res(K)`.
There is a homomorphism `rho` from `K` into a hyperlinear group with
`rho(x) != 1`. Replace its target by the countable subgroup `H = rho(K)`,
which is hyperlinear by the hereditary clause of
`local-approximation-properties-are-marked-closed`. Since `Res(K) <= ker rho`,
`rho` factors as
`rhobar : Kbar -> H`. By the necessity half of
`hyperlinear-elementwise-visibility`, `rho(x)` is tracially visible in `H`
with some constant `c > 0`. For a finite `F` in `Kbar` and `delta > 0`, take a
model `phi` of `H` with defect at most `delta` on `rhobar(F)` and
`Re tr(phi(rho(x))) <= 1-c`. Because `rhobar` is a homomorphism,
`phi o rhobar` has defect at most `delta` on `F` and the same trace at
`xbar`. So every `xbar != 1` is tracially visible in `Kbar`, and the
sufficiency half of `hyperlinear-elementwise-visibility` makes `Kbar`
hyperlinear.

**(R2) `Res(N)` is normal in `G`.** For an automorphism `alpha` of `N` and a
homomorphism `rho` from `N` into a hyperlinear group, `rho o alpha` is again
such a homomorphism, so `alpha(Res(N)) = Res(N)`. Conjugation by elements of
`G` restricts to automorphisms of `N`.

**(R3) `Res(N) <= Res(G) intersect N` always.** Let `g` in `N` with `g` not in
`Res(G)`. Some homomorphism `rho : G -> H` into a hyperlinear group has
`rho(g) != 1`. Its restriction maps `N` onto the subgroup `rho(N)` of `H`.
Subgroups of hyperlinear groups are hyperlinear (hereditary clause of
`local-approximation-properties-are-marked-closed`), so `g` is not in `Res(N)`.

**(R4) (i) implies (ii).** Let `G/N` lie in `C`. By (R2) `Res(N)` is normal in
`G`, and

```text
1 -> N/Res(N) -> G/Res(N) -> G/N -> 1
```

is exact. The kernel is hyperlinear by (R1) and the quotient is in `C`, so by
(i) `G/Res(N)` is hyperlinear. If `g` in `N` is not in `Res(N)`, its image in
`G/Res(N)` is nontrivial, so `g` is not in `Res(G)`. Hence
`Res(G) intersect N <= Res(N)`, and (R3) gives equality.

**(R5) (ii) implies (i).** Let `N` be hyperlinear and normal in `G` with
`G/N` in `C`. Then `Res(N) = 1`, so by (ii) `Res(G) intersect N = 1`. The
quotient map `G -> G/N` lands in a hyperlinear group, so `Res(G) <= N`. Hence
`Res(G) = 1`, and by (R1) `G = G/Res(G)` is hyperlinear.

**(R6) Part 1.** For `C` the amenable groups (which are hyperlinear), (i) is
the extension clause of `amenable-quotient-preserves-metric-approximability`:
an extension of a hyperlinear group by an amenable group is hyperlinear. By
(R4) this gives (ii), which is part 1.
