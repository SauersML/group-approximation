---
rg: 2
id: fixed-perfect-seed-composition-no-go-proof
kind: route
title: Classify black-box AND, OR, and common-gate seed compositions
target: fixed-perfect-seeds-do-not-black-box-exactify-tv
requires:
  - taller-vidick-positive-noise-collapses-central-sign
  - tv-central-flags-and-private-slacks-cannot-exactify
---

# Classify black-box AND, OR, and common-gate seed compositions

## 1. The only TV fact used

For every positive noise parameter, the Taller--Vidick support contains two
LCS equations

$$
L=J^a,
\qquad
L=J^{a+1},                                              \tag{1}
$$

with exactly the same left-hand-side group word \(L\).  This is the
support calculation in
[taller-vidick-positive-noise-collapses-central-sign](taller-vidick-positive-noise-collapses-central-sign.md).
Every perfect LCS strategy is represented in its tracial GNS model by
\(J=-I\) and all positive-weight equation relations.  Equations (1) would
then give \(J=I\), a contradiction.  Thus the positive-noise test
\(T_\epsilon\) has no perfect commuting-operator strategy.

No quantitative estimate from the Taller--Vidick soundness theorem is
needed below.

## 2. Positive mixtures and parallel AND retain the obstruction

First let a composite verifier run the unchanged test \(T_\epsilon\) with
probability \(\lambda>0\), and some seed test otherwise.  If its overall
acceptance probability is one, positivity of loss gives

$$
0=1-\omega
 =\lambda(1-\omega_T)+(1-\lambda)(1-\omega_S).          \tag{2}
$$

Both summands are nonnegative, so \(\omega_T=1\).  This contradicts
Section 1.

The same conclusion holds for the standard parallel AND product.  Let its
question law be the product of the source and seed question laws, and let it
accept exactly when both coordinate predicates accept.  Suppose a
commuting correlation wins with probability one.  Fix any seed question
pair \((s,t)\) in the support of the seed law.  For source questions
\((x,y)\), marginalize the seed answers from the composite correlation at
the question pair \(((x,s),(y,t))\).  The resulting numbers form a valid
commuting correlation for the source game: they are marginals of the same
commuting measurement model with \(s,t\) fixed.

Every supported combined question has acceptance probability one.  Since
the AND predicate is bounded above by the source predicate, the source
predicate also has acceptance probability one on every supported
\((x,y)\).  The marginal is therefore a perfect strategy for
\(T_\epsilon\), again contradicting Section 1.

This argument permits arbitrary entanglement between the two coordinates;
it does not assume the composite strategy is a tensor product.

## 3. A common noncentral gate is forced to vanish

A seed flag need not be central.  Nevertheless, no single operator can
compress both equations in (1) onto a nonzero active subspace.

Let \(\pi\) be any representation with \(\pi(J)=-I\), and abbreviate
\(\pi(L)\) to \(L\).  Let \(F\) be an arbitrary bounded operator; it may
belong to a noncommuting seed algebra.

For a common left gate, suppose

$$
F(L-\pi(J)^a)=0,
\qquad
F(L-\pi(J)^{a+1})=0.                                   \tag{3}
$$

Subtracting gives

$$
F\bigl(\pi(J)^{a+1}-\pi(J)^a\bigr)
 =-2(-1)^aF=0,                                         \tag{4}
$$

so \(F=0\).  The identical calculation on the right proves the same result
for a common right gate.

For a compression gate, suppose instead

$$
F^*(L-\pi(J)^a)F=0,
\qquad
F^*(L-\pi(J)^{a+1})F=0.                                \tag{5}
$$

Subtraction gives

$$
-2(-1)^aF^*F=0,                                        \tag{6}
$$

and hence \(F=0\).  Taking \(F=p\) covers compression by an arbitrary
projection \(p\), with no assumption that \(p\) commutes with \(L\), the
source variables, or the seed variables.

Therefore an AND flag which uses the same seed support for every old TV
relation has zero support in any perfect \(J=-I\) model.  Noncentrality by
itself does not evade the positive-noise contradiction.  An escape would
have to assign different gates to the two relations, in a way coupled to
their source data; Section 3 makes no assertion about that case.

## 4. OR and bypass compositions inherit the seed's finite value

Now let \(S\) be a fixed finite game with commuting value one.  For the
standard parallel OR product, tensor any finite-dimensional strategy for
\(S\) with an arbitrary finite-dimensional strategy for \(T_\epsilon\).
Whenever the seed coordinate accepts, the OR predicate accepts.  Thus every
finite seed strategy of value \(v\) gives a finite composite strategy of
value at least \(v\), and taking suprema yields

$$
\omega_q(T_\epsilon\mathbin{\mathrm{OR}}S)
 \geq \omega_q(S).                                     \tag{7}
$$

The same proof applies to any bypass construction with the following
black-box property: every finite-dimensional seed strategy extends to a
composite strategy whose acceptance is at least the seed acceptance.  It
does not matter how badly the source coordinate is played.

There are exactly two cases.

- If \(\omega_q(S)=1\), then (7) makes the composite finite-dimensional
  supremum one.  Nonattainment of a perfect finite-dimensional seed
  strategy is not a constant soundness gap and cannot witness
  non-hyperlinearity through this composition.

- If \(\omega_q(S)<1\), then \(S\) already has commuting value one and a
  strict finite-dimensional value gap.  When \(S\) is itself an LCS, it is
  already the exact perfect-completeness ingredient sought by the
  reduction.  The OR wiring has assumed the hard object rather than
  produced it.

This dichotomy is independent of whether the commuting perfect strategy of
\(S\) is finite- or infinite-dimensional.  The relevant distinction for
the target problem is robust finite approximability, measured by the
supremum \(\omega_q(S)\), not merely existence of a finite-dimensional
maximizer.

## 5. Boundary of the no-go

Sections 2--4 rule out the advertised black-box routes:

- unchanged positive-weight subtests and parallel AND cannot become
  perfectly complete;
- one common seed gate is annihilated even when it is noncentral;
- OR and free bypass inherit finite value one from any seed that is only a
  nonattainment example;
- a seed with strict finite value gap already contains the desired
  separation.

What remains is not a standard product.  It would require
relation-dependent noncommuting gates or shared slacks tied to the source
queries, together with two new proofs: a perfect global commuting strategy
for the rewired equations, and a reverse decoder showing that every
near-perfect finite-dimensional strategy yields a forbidden source
strategy.  Those gates can no longer be treated as a fixed seed black box.
This route neither constructs them nor rules them out.
