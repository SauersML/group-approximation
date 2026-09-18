---
rg: 2
id: internal-torsion-free-single-word-router
kind: claim
title: Internally route one torsion-free word onto a two-generated acylindrical quotient
root: true
distinct_from:
  two-generated-single-element-hull-router: that imports Hull--Osin small cancellation as a paper-level black box; this requires the routing construction and its normal-form proof inside the repository, with no literature premise.
  bespoke-routing-lemma: that is tailored to a compression defect and a Property-T partner and currently bottoms out in a cited Greendlinger lemma; this takes an MF-radical word directly and permits no Kazhdan partner.
---

**OPEN INTERNAL ROUTER.**  Given a finitely presented torsion-free
acylindrically hyperbolic group `E`, a nonidentity `d in E`, and a finite
protected set containing `d`, construct in-repository a surjection

```text
q:E->>Q
```

such that `Q` is nontrivial, two-generated, finitely presented, torsion-free,
and acylindrically hyperbolic, `q` is injective on the protected set, and

```text
normalClosure_Q(q(d))=Q.                               (TFR3)
```

No cited small-cancellation theorem may occur as a premise of the final Lean
declaration.  A direct formalization of the needed normal-form/Greendlinger
argument is acceptable; a wrapper around `two-generated-single-element-hull-router`
or `greendlinger-free-product-lemma-citation` is not.

## Attempts

**Surjectivity is unnecessary, and (TFR3) is elementary once it is dropped
(swarm-0917, reframing).**  The consumer `torsion-free-mf-radical-routing-saturation`
never uses that `q` is onto.  `mf-radical-saturation-along-any-homomorphism`
records the same conclusion for any homomorphism.  With that relaxation,
`torsion-free-embedding-normal-generation-router` (ESTABLISHED) proves the
normal-generation clause internally.  It embeds any finitely presented
torsion-free `E` into a finitely presented torsion-free `P` with
`normalClosure_P(d)=P`, using `n+1` HNN extensions and one amalgam with the
chain gadget `<x,y,z | x z x^-1=z^2, z y z^-1=y^2>` over the free pair
`(d,c)`.  The protected set survives because the map is injective.  No
acylindrical hypothesis on `E` is used.

What this does not give: two generation and acylindrical hyperbolicity of
the target.  That residual is isolated as
`two-generated-acylindrical-normal-generation-upgrade`, with the new route
`property-t-free-torsion-free-via-embedding-router`.  The same session
recorded one obstruction.  Every HNN-final two-generation step (Neumann,
Higman--Neumann--Neumann) has a stable-letter exponent-sum epimorphism onto
`Z` that kills the protected word, so it destroys `(TFR3)`.  Alternating
gadget amalgams with HNN two-generation regresses without terminating.  This
claim itself (surjective, from an acylindrically hyperbolic input) remains
OPEN.

**Zero marginal impact, and the last import of the routing chain removed
(swarm-0917, d-ptf-router, reframing).**  *Domination.*  Every live route
that uses this claim also needs a finitely presented torsion-free seed `E`
with `1 != d in Rad_MF(E)`.  Such a seed is exactly
`property-t-free-torsion-free-fp-non-mf-seed`, and
`property-t-free-torsion-free-via-embedding-router` already finishes from it
without this claim.  So a proof of the surjective router changes no goal
status.  The seed is the last missing prerequisite, and effort belongs there.

*Internal acylindricity.*  The established upgrade still imported
Minasyan--Osin.  That import is now gone:

* `malnormal-edge-amalgam-tree-action-is-acylindrical` (elementary): if the
  edge group is malnormal in one factor, 3-paths in the Bass--Serre tree have
  trivial stabilizers.  Acylindricity follows with `R = 2ε+5` and
  `N = 4ε+2`, and `tb`, `bt` are independent loxodromics.
* `two-generated-acylindrical-upgrade-without-minasyan-osin`: a second
  amalgam `(Q_1*<t>) *_{C'} F(a,b)` over the fixed malnormal
  `C' = <a, ba^2b^2, baba^{-1}b, b^3ab^{-1}>`, with `t^4 <-> a`,
  `st <-> ba^2b^2`, `ct^2 <-> baba^{-1}b` and `sct^3 <-> b^3ab^{-1}`.

*Where it stops.*  Malnormality of `C'` and triviality of
`<t,b | t=bt^8b^2, t^2=bt^4bt^{-4}b, t^3=b^3t^4b^{-1}>` are finite
computations, done by two independent coset enumerators.  They are not yet
by-hand derivations.  The script's search also found no malnormal
`<a,y_1,y_2>` with all `|y_i| <= 4`: every malnormal completion needs words of
length 5.  Surjectivity is still unaddressed.  An internal proof would need
small cancellation over a hyperbolic group, which is formalizing Hull--Osin,
and by the domination above it would buy nothing.
