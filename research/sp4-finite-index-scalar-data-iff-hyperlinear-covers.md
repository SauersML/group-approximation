---
rg: 2
id: sp4-finite-index-scalar-data-iff-hyperlinear-covers
kind: claim
title: Scalar ISW data on a finite-index subgroup of Sp4(Z) is a circle of hyperlinear finite central covers
artifacts:
  - research/artifacts/sp4-llp-decide-2026-09-13.md
distinct_from:
  maslov-ce-subgroup-classifies-finite-deligne-covers: that classifies the finite cyclic quotients of the integral Deligne extension of Sp4(Z) along the Maslov circle; this treats every finite-index subgroup and every infinite-order integral class, adds finite atomic actions, and shows the covers involved are almost never residually amenable.
  sp4-isw-theorem-c-embeddable-twist-data-exists: that is the Theorem C packet over an arbitrary ergodic action; this proves that packets over finite transitive actions are scalar packets on finite-index subgroups, and rewrites those as hyperlinearity of finite central covers.
  sp4-finite-index-fd-projective-multiplier-is-finite: that proves exact finite-dimensional realizability is finite on every finite-index subgroup; this consumes it to show that the hyperlinear covers needed here are not residually amenable.
---

Let `Gamma = Sp_4(Z)` and let `Gamma' <= Gamma` have finite index `m`.
For `x in H^2(Gamma',Z)` let `E_x` be the central extension of `Gamma'` by
`Z` with class `x`, and put `E_x^(n) = E_x/nZ`.  Write `e(t) = exp(2 pi i t)`
and

```text
E_CE(Gamma') = { [omega] in H^2(Gamma',T) :
                 L_omega(Gamma') is Connes embeddable }.
```

**THEOREM.**  The following are equivalent.

1. There are `c_n in Z^2(Gamma',T)`, none a coboundary, with
   `c_n(g,h) -> 1` for all `g, h`, and every `L_(c_n)(Gamma')` Connes
   embeddable.
2. `E_CE(Gamma')` has positive dimension.  (It is always a closed subgroup
   of the compact abelian Lie group `H^2(Gamma',T)`.)
3. Some infinite-order `x in H^2(Gamma',Z)` has `E_x^(n)` hyperlinear for
   every `n >= 1`.                                              (FIC1)

Moreover:

- **(FIC2)** for every infinite-order `x`, only finitely many `E_x^(n)` are
  residually amenable; and condition 3 makes `E_x` itself hyperlinear;
- **(FIC3)** if `b_2(Gamma') = 1`, conditions 1-3 at `Gamma'` are
  equivalent to `sp4-small-maslov-twisted-group-factors-are-ce`;
- **(FLA1)** let `A = l^infty(Gamma/Gamma')` carry the translation action
  and the uniform trace.  If `c_n in Z^2(Gamma, U(A))` are non-coboundaries
  with `||c_n(g,h) - 1||_2 -> 0` for all `g, h`, and every twisted crossed
  product `A x|_(c_n) Gamma` is Connes embeddable, then condition 1 holds at
  `Gamma'`.

**What it does to the lifting hole.**  Condition 1 is an
Ioana--Spaas--Wiersma Theorem 4.3 packet at `A = C1` for the Kazhdan group
`Gamma'` (arXiv:2006.01874, pp. 17-18, quoted in the artifact), so it makes
`C^*(Gamma')` fail LLP, hence `C^*(Sp_4(Z))` too, because LLP passes to
subgroups.  (FLA1) says Theorem 4.3 over a finite transitive action of
`Sp_4(Z)` supplies nothing beyond condition 1 on a finite-index subgroup.
So the atomic and scalar refutation mouths of
`sp2g-z-full-c-star-algebra-has-llp` together amount to

```text
some finite-index Gamma' <= Sp_4(Z) and some infinite-order
x in H^2(Gamma',Z) have every finite cyclic cover E_x^(n) hyperlinear,
```

and by (FIC2) no family of such covers can be certified through finite or
amenable quotients.  At level one this is the Maslov circle again
(`maslov-ce-subgroup-classifies-finite-deligne-covers`).  A genuinely new
circle needs `b_2(Gamma') >= 2`; no congruence Betti number is computed
here.
