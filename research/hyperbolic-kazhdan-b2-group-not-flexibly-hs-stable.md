---
rg: 2
id: hyperbolic-kazhdan-b2-group-not-flexibly-hs-stable
kind: claim
title: A torsion-free hyperbolic Kazhdan group with positive second Betti number that is not flexibly HS-stable
distinct_from:
  classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan: that shows class-wide stability of hyperbolic Kazhdan groups would contain stability of every finitely presented Kazhdan group, and uses this only as a screen; this refutes the class-wide hypothesis outright, inside the b_2 >= 1 torsion-free class.
  kazhdan-hyperbolic-b2-group-flexibly-hs-stable: that asks for one flexibly stable hyperbolic Kazhdan group with b_2 >= 1; this exhibits a member of the same class that is not flexibly stable, so the class property alone never suffices.
  rf-kazhdan-group-not-flexibly-hs-stable: that refutes flexible stability for the non-hyperbolic affine symplectic group, which contains Z^2; this transports the refutation into a word-hyperbolic group with b_2 >= 1.
  ghb7-is-not-flexibly-hs-stable: that asks instability of one specific hyperbolic Kazhdan group with torsion and b_2 = 0; this proves instability of a Belegradek--Osin cover, which says nothing about GHB_2(7).
artifacts:
  - research/hyperbolic-kazhdan-b2-group-not-flexibly-hs-stable-proof.md
---

**ESTABLISHED (unreviewed).** Let `g >= 2` and `Γ_g = Z^(2g) ⋊ Sp_(2g)(Z)`. Let `H` be a
torsion-free non-elementary hyperbolic Kazhdan group. Then there is an exact sequence

```text
1 -> N -> G -> Γ_g -> 1
```

with the following properties:

1. `G` is word-hyperbolic, torsion-free, non-elementary and finitely presented;
2. `G` has property (T), and so does `N`, which is a quotient of `H`;
3. `b_2(G;Q) >= b_2(Γ_g;Q) >= 1`;
4. `G` is **not** flexibly Hilbert--Schmidt stable (Dogon--Vigdorovich, Definition 1.2).

Moreover, `G` carries the Ioana--Spaas--Wiersma obstruction itself. The pullback `G~` of the
integral Heisenberg cover `Γ~_g` has property (T). It is a central `Z`-extension of `G` with
finite abelianization, and it has finite quotients in which the centre survives with order
`k`, for every `k >= 3`.

Derivation: `hyperbolic-kazhdan-b2-group-not-flexibly-hs-stable-proof`.

## What this kills

**The class-wide hypothesis is false.** Suppose a stability argument applies to some class
`C` of hyperbolic Kazhdan groups. If `C` contains a Belegradek--Osin cover of `Γ_g`, the
argument is wrong. Some examples of such classes:

- all hyperbolic Kazhdan groups;
- all torsion-free hyperbolic Kazhdan groups with `b_2 >= 1`;
- all relative small-cancellation quotients `(H * F)/⟨⟨R⟩⟩` of a free product of a
  torsion-free hyperbolic Kazhdan group with a free group. This is the shape of the
  Belegradek--Osin construction (Olshanskii-type small cancellation over `H * F`; the
  construction was not re-read for this node, so this item is only as good as that
  description).

Before this node, `classwide-hyperbolic-kazhdan-hs-stability-covers-fp-kazhdan` recorded
only a *screen*: such an argument would imply non-hyperlinearity of the Leavitt unit group,
so it would be suspiciously strong. Now the screen is replaced by a refutation. The failing
step is exactly step 4 of `classwide-hyperbolic-kazhdan-hs-stability-proof`, the hypothesis
"`G` is flexibly HS stable", which fails for `G` above.

**Which features do not help.** Hyperbolicity, torsion-freeness, finite presentation, (T)
and `b_2 >= 1` together do not force flexible rounding. So a proof of
`kazhdan-hyperbolic-b2-group-flexibly-hs-stable` for a candidate must use a feature that
some Belegradek--Osin cover of `Γ_g` lacks. One such feature is the absence of a Kazhdan
central `Z`-extension whose centre survives at unbounded orders. That is the central gate used
in `ghb7-instability-via-visible-central-extension` and
`ghb7-centre-survival-via-degree-two-goodness`. By item "Moreover", `G` has such an extension,
and its instability is that gate firing. So the gate is not vacuous on hyperbolic Kazhdan
groups with `b_2 >= 1`, and this node calibrates it there.

**Independent second witness (remark, not a route).** Put Cornulier's finitely presented
non-Hopfian Kazhdan group `Q_C` (`cornulier-non-hopfian-kazhdan-groups-are-mf`) in place of
`Γ_g`. `Q_C` is MF, hence hyperlinear, and it is not residually finite. By
`flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear`, no group mapping onto
`Q_C` with Kazhdan kernel is flexibly stable. So its Belegradek--Osin covers are unstable
hyperbolic Kazhdan groups for a reason that does not use `H^2`. That witness gives no `b_2`
control.

**What is not claimed.** Nothing is claimed about the density-model random groups, the
`GHB(7)` congruence kernel, Linial--Meshulam groups or any other named candidate. Nothing is
claimed about residual finiteness or hyperlinearity of `G`.

DERIVATION
hyperbolic-kazhdan-b2-group-not-flexibly-hs-stable-proof
