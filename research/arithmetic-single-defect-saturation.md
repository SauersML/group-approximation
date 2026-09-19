---
rg: 2
id: arithmetic-single-defect-saturation
kind: claim
title: One certified defect element saturates the routed quotient and forces its own survival
distinct_from:
  concrete-compression-source: that claim is the SOURCE stage — it produces the arithmetic HNN skeleton and Britton-certifies one nontrivial marked commutator, and stops there; this one is the SATURATION stage, which consumes that certified element plus a routing quotient and concludes that the whole defect fills the quotient.
  normal-kazhdan-defect-non-mf: that claim is the ANALYTIC detector — given a nontrivial normal Kazhdan subgroup inside the defect it kills every corona representation; this one is pure group theory feeding that detector, and supplies precisely the hypothesis `K = ⊤` at which the detector is applied.  No operator algebra occurs here.
  two-generated-single-element-hull-router: that claim is the routing EXISTENCE statement, and is the acylindrically hyperbolic input this one consumes as data; this one asserts no quotient exists and proves only what follows once one does.
  defect-saturation-full-mf-radical: that claim is an EXISTENCE statement about a group `G` with full MF radical; this one is a conditional implication about any routed quotient and asserts no existence.
artifacts:
  - research/artifacts/arithmetic-single-defect-saturation-2026-08-23.md
  - GroupApproximation/Sofic/SingleDefectSaturation.lean
  - GroupApproximation/Sofic/BareDefectSource.lean
  - GroupApproximation/Sofic/LiteralAffineCongruenceSource.lean
---

**This is not a new analytic non-MF mechanism.**  It is a new *construction
route* into the existing normal-Kazhdan defect engine
([[normal-kazhdan-defect-non-mf]]), which is unchanged and already
kernel-checked.  Nothing below improves the detector; it only shows that the
detector's hypothesis can be discharged at `K = ⊤` from a single certified
defect element, with no simple subgroup anywhere.

Let `D` be a compression source datum — a Kazhdan base `iota : P -> E`, a
compressing letter `u`, and a protected element `s` commuting with the
compressed base — with defect

```text
D_E = << [s, iota p] : p in P >>^E,
```

and let `sigma = [s, iota w]` be one marked commutator that is *certified
nontrivial* (Britton, at the arithmetic source of
[[concrete-compression-source]]).  Suppose a routing quotient `q : E ->> Q`
onto a nontrivial group satisfies

```text
<< q sigma >>^Q = Q.
```

Then the **entire** defect saturates,

```text
Q = << q sigma >>^Q <= D_Q <= Q,   so   D_Q = Q,
```

and consequently the normal-Kazhdan detector applies with `K = ⊤`: `Q` is
normal in itself, Kazhdan by inheritance from the routing partner, and
contained in its own defect.  Hence `Rad_MF(Q) = Q`, every homomorphism from
`Q` to the unitary group of a norm matrix corona is trivial, and — full MF
residual passing through surjections — every nontrivial quotient of `Q`
inherits both properties.

**Survival is proved, not assumed.**  The repository's routing datum carries
*two* independent fields, `defect_surjective` and `protected_ne_one`
(`BareDefectSource.lean:380,382`), and derives nontriviality of the quotient
*from* the second (`quotientNontrivial`, `BareDefectSource.lean:425`).  Under
the single normal-generation hypothesis above the dependency inverts and the
second field becomes a theorem: if `q sigma = 1` then `<< q sigma >>^Q` is
trivial, so `Q = 1`, contradicting nontriviality; and `q sigma != 1` forces
`q s != 1`, since `q sigma = [q s, q iota w]` collapses when `q s` does.  So
one hypothesis about a *specific element surviving* is traded for one
hypothesis about the *target group being nontrivial* — strictly weaker, and
certifiable without reference to `sigma` at all.

To be exact about what is new here, since the field is already derivable:
`SmallCancellationRouter.RoutingLemmaData.toBareRoutingData` discharges
`protected_ne_one` from the router's **injectivity on the protected set**
(`BareDefectSource.lean:354-358`).  The derivation above is an *alternative*
one that uses no injectivity clause at all — only normal generation and
`Nontrivial Q`.  That matters because the injectivity clause is Hull's 7.1(b),
one of the two pressure points singled out in the adversarial audit of
[[defect-normally-generates-torsion-free-quotient]]; a survival argument that
does not consult it shortens the part of the trust surface that is
paper-level.  It does not remove a field from the interface, and it does not
touch the case where the routed quotient is trivial.

**No simplicity anywhere.**  The certified element is a length-four commutator
in an HNN extension, not an element of an embedded simple group, and its
survival comes from the displayed normal-generation identity rather than from
protection by simplicity.  No finitely presented simple torsion-free group, no
universal torsion-free host, and no Fournier--Facio input occurs.

**Trust boundary — this route is NOT a zero-input Lean theorem.**  The routing
datum `<< q sigma >>^Q = Q` is exactly the acylindrically hyperbolic /
small-cancellation step of [[two-generated-single-element-hull-router]]: Hull,
*Small cancellation in acylindrically hyperbolic groups*, GGD 10 (2016)
1077--1119, together with the s-normality lemma of Osin, *Acylindrically
hyperbolic groups*, TAMS 368 (2016) 851--888, which makes the normal closure of
one nontrivial element a suitable reservoir.  Mathlib has no theory of
acylindrical hyperbolicity and none is developed here; the datum is **consumed
as data**, paper-level and unformalized, exactly as
[[defect-normally-generates-torsion-free-quotient]] consumes it.  What is
kernel-checked is everything downstream of the datum.  The source side is
independently checked: torsion-freeness of the arithmetic base rests on
Minkowski's congruence theorem and of the extension on the Britton/Serre normal
form for HNN extensions (Lyndon--Schupp IV.2, in-repo as
[[hnn-torsion-theorem]]).  None of these four results is a repository result.

Property (T) is removed from the construction and routing problem — no step
above uses it — but **not** from the detector, which still needs (T) of the
source and of the routed normal subgroup.  A (T)-free version would require a
new operator-norm rigidity theorem, not a further rearrangement of this group
theory.
