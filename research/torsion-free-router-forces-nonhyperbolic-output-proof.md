---
rg: 2
id: torsion-free-router-forces-nonhyperbolic-output-proof
kind: route
title: A surviving normal generator conjugate to its own square spans BS(1,2), which no hyperbolic or residually finite output can hold
target: torsion-free-router-forces-nonhyperbolic-output
requires:
  - hnn-torsion-theorem
  - cprime-one-sixth-presentations-hyperbolic-and-torsion-free
  - torsion-free-mf-radical-routing-saturation
  - universal-mf-quotient
  - central-quotients-of-residually-finite-groups-are-mf
  - hyperbolic-cubulated-groups-are-residually-finite
artifacts:
  - research/artifacts/torsion-free-router-nonhyperbolic-output-2026-09-16.md
---

Full details are in the artifact.

**Embedding lemma (internal, §1).**  Model `BS(1,m)` as `Z[1/|m|] x| Z`.
Let `f` be a homomorphism out of `BS(1,m)` for which `f(t)` has infinite
order, and let `K = ker f`.

* `K` meets `Z[1/|m|]` trivially.  A nonzero `r = n m^-j` in `K` conjugates
  to `t^n` in `K`, which is impossible.
* Any `(r, k)` in `K` gives the commutator `(r,k) t (r,k)^-1 t^-1 = (m^k - 1, 0)`
  in `K`.  So `k = 0`.

Hence `f` is injective.

**(A)(a).**  `Q != 1` and (TFR3) force `q(d) != 1`.  Torsion-freeness makes
`q(d)` of infinite order, and `q(x) q(d) q(x)^-1 = q(d)^m`.  The embedding
lemma applies.

**(A)(b).**  Fact H: word-hyperbolic groups contain no `BS(1,m)` with
`|m| >= 2`, because infinite-order elements are undistorted and
`|d^(m^k)| <= 2k|x| + |d|`.  This is imported inline.  It was checked
verbatim on Wikipedia, *Hyperbolic group*, fetched 2026-09-16; the classical
sources are Gromov and Bridson--Haefliger III.Gamma.  It is not re-derived.

**(A)(c).**  [[cprime-one-sixth-presentations-hyperbolic-and-torsion-free]]
makes such presentations define word-hyperbolic groups, which contradicts
(b).

**(A)(d).**  An injective surjection is an isomorphism; pull back (TFR3).

**Test instance (§2).**  `E_1` is the HNN extension of `F(t, s)` with stable
letter `a` sending `t` to `t^2`, so it is torsion-free by
[[hnn-torsion-theorem]].  Killing `t` leaves `F(a, s)`.  Acylindrical
hyperbolicity comes from the Bass--Serre tree of `BS(1,2) * <s>`:

* edge stabilizers are trivial, which gives acylindricity (explicit
  constants in the artifact);
* `ts` is loxodromic;
* `<a, s>` is free of rank two;
* Osin's trichotomy, arXiv:1304.1246, Theorem 1.1, finishes.

This check certifies only that the input is legitimate.

**(A').**  Here `q(d) != 1`, so (TFR1) holds and
[[torsion-free-mf-radical-routing-saturation]] gives `Rad_MF(Q) = Q`.  Then:

* `Q` is not MF, by [[universal-mf-quotient]];
* `Q` is not residually finite, since residually finite groups are MF by
  [[central-quotients-of-residually-finite-groups-are-mf]] with trivial
  center;
* `Q` is not a classical `C'(1/6)` group, since those are residually finite
  by [[hyperbolic-cubulated-groups-are-residually-finite]].
