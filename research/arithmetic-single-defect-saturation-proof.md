---
rg: 2
id: arithmetic-single-defect-saturation-proof
kind: route
title: Sandwich the defect between one normally generating element and the whole quotient
target: arithmetic-single-defect-saturation
requires:
  - two-generated-single-element-hull-router
  - concrete-compression-source
  - affine-congruence-source-is-kazhdan
  - normal-kazhdan-defect-non-mf
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
  - GroupApproximation/Sofic/SingleDefectSaturation.lean
  - GroupApproximation/Sofic/BareDefectSource.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
---

## Why sufficient

The whole saturation step is a two-inclusion sandwich; everything else on this
route is bookkeeping or is consumed as data.

**The certified element.**  [[concrete-compression-source]] supplies, kernel-
checked, the arithmetic HNN skeleton over `P = Gamma(3) ltimes Z^3` and one
Britton-certified marked commutator `sigma = [t c t^-1, p_0] != 1`.  It lies in
the defect by `BareDefectSourceData.witness_commutator_mem_defectNormal`
(`BareDefectSource.lean:152`) — note that the certified defect element is this
*commutator*, not the protected element `s` itself, which is not in the defect.

**The routing datum, consumed not constructed.**
[[two-generated-single-element-hull-router]] yields `q : R ->> Q` with `Q`
two-generated, finitely presented, torsion-free, acylindrically hyperbolic,
Kazhdan by inheritance from the partner, and

```text
<< q sigma >>^Q = Q.
```

**The sandwich.**  `sigma in D_E` and `q` is a homomorphism, so
`q sigma in D_Q`, hence `<< q sigma >>^Q <= D_Q` because `D_Q` is normal.
With the routing identity,

```text
Q = << q sigma >>^Q <= D_Q <= Q,   so   D_Q = Q.
```

In the repository's interface this is precisely the field
`defect_surjective : D.core.defectNormal.map quotient = ⊤`
(`BareDefectSource.lean:380`), which then feeds `mapped_defectNormal_eq_top`
(`:430`).

**Survival falls out.**  If `q sigma = 1` then `<< q sigma >>^Q = 1`, so
`Q = 1`; contrapositively `Q != 1` gives `q sigma != 1`.  Since
`q sigma = [q s, q iota p_0]`, a trivial `q s` would make the commutator
trivial, so `q s != 1` — the field `protected_ne_one`
(`BareDefectSource.lean:382`).  The nontriviality of `Q` that this consumes is
supplied by the router, not by `sigma`.

**The detector, unchanged.**  Apply [[normal-kazhdan-defect-non-mf]] with
source `P` — Kazhdan by [[affine-congruence-source-is-kazhdan]], which the
detector genuinely reads — ambient `Q` (countable, being finitely presented),
and normal Kazhdan subgroup `K = ⊤`: nontrivial, normal, Kazhdan, and inside
its own defect by the sandwich.  This is exactly the path
`coronaMFResidual_eq_top` already takes at `BareDefectSource.lean:441`, via
`KazhdanCompressionCore.normalKazhdan_le_coronaMFResidual`.  Conclusion
`Rad_MF(Q) = Q`, and full MF residual passes through surjections, so every
nontrivial quotient of `Q` inherits it.

## What this route does not establish

**It is not a new analytic mechanism.**  The killing theorem is the existing
normal-Kazhdan compression obstruction, unmodified.  This route only discharges
that theorem's hypothesis at `K = ⊤`; if the detector were withdrawn, nothing
here would survive as an obstruction.

**It is not a zero-input end-to-end Lean theorem, and must not be labelled
one.**  The routing identity `<< q sigma >>^Q = Q` is the acylindrically
hyperbolic step and is *consumed as data*.  Mathlib has no theory of
acylindrical hyperbolicity, none is developed here, and the repository's
formalization boundary is deliberately the routing datum rather than Hull's
proof.  The credited inputs, none of them repository results:

- Hull, *Small cancellation in acylindrically hyperbolic groups*, GGD 10
  (2016) 1077--1119 — the two-stage common-quotient machinery, including the
  injectivity clause 7.1(b) and the finitely generated case of Corollary 7.4;
- Osin, *Acylindrically hyperbolic groups*, TAMS 368 (2016) 851--888 — the
  s-normality lemma making the normal closure of one nontrivial element act
  non-elementarily, hence a suitable reservoir;
- Minkowski — torsion-freeness of the congruence subgroup `Gamma(3)`;
- Britton / Serre — the HNN normal form giving both `sigma != 1` and
  torsion-freeness of the extension (Lyndon--Schupp IV.2, in-repo as
  [[hnn-torsion-theorem]]).

A finitely presented torsion-free **non-elementary** hyperbolic Kazhdan
partner is also still required and is not removed by this route; see
[[torsion-free-hyperbolic-kazhdan-partner-exists]] and the degeneracy guard in
the artifact, the unqualified form of that statement being degenerate.

**Relation to the assembled route.**  [[defect-saturation-from-arithmetic-source]]
runs the same construction end to end against a different target.  This route
is not an alternative to it and does not compete with it: it isolates the one
algebraic implication inside its saturation step, states it for an arbitrary
compression source rather than only the arithmetic one, and records the
survival derivation that the assembled route performs inline.  Anyone checking
only the sandwich should read that route for the surrounding construction.

## Formalization status

The sandwich and the survival derivation are elementary subgroup algebra —
normality of the defect, `Subgroup.normalClosure_le`, and one commutator
collapse — and are formalizable against the existing `BareRoutingData`
interface with no new analytic content.  Doing so would replace two stored
fields by one hypothesis plus `Nontrivial Q`.  That work is not yet on disk and
nothing above should be read as claiming it is; what is kernel-checked today is
everything downstream of `defect_surjective` and `protected_ne_one`, which is
the full-radical consequence package at `BareDefectSource.lean:441-511`.
