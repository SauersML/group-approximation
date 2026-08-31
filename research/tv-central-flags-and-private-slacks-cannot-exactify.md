---
rg: 2
id: tv-central-flags-and-private-slacks-cannot-exactify
kind: claim
title: Central flags and private parity slacks cannot exactify the Taller--Vidick test
artifacts:
  - research/tv-flag-slack-direct-sum-no-go-proof.md
distinct_from:
  taller-vidick-positive-noise-collapses-central-sign: that extracts the two contradictory positive-noise equations and proves J equals one; this classifies three proposed repairs of that contradiction.
  lcs-parity-gadgets-preserve-odd-dictator-affine-hull: that treats arbitrary atomwise scalar-extendable parity gadgets; this gives sharper direct-sum, central-word-gating, and private-slack conclusions for the Taller--Vidick pair.
  reverse-kleene-does-not-remove-tv-completeness-loss: that rules out a self-referential limit argument; this rules out finite accept flags and equationwise slack exactifiers.
---

Fix any positive-noise Taller--Vidick test
\(L^\epsilon(u,B,\pi)\), \(0<\epsilon<1\).  Its support contains two equations
with the same folded left word \(L\) and opposite parity signs:

$$
L=J^a,
\qquad
L=J^{a+1}.                                             \tag{1}
$$

Three natural perfect-completeness repairs have exact no-go theorems.

1. **Direct-sum flag.**  Let \(p\) be a central projection selecting a block
   on which the original equations (1) are still enforced.  In a prospective
   perfect \(J=-I\) model,

   $$
   p(L-J^a)=p(L-J^{a+1})=0
   $$

   implies \(p=0\).  Equivalently, a convex direct sum containing a
   positive-weight original-test block cannot be perfect.  All weight must
   move to the slack block, so a source-independent finite-dimensional
   accept block destroys soundness.

2. **Central word flag.**  Let \(t\) be a central involution commuting with
   all source variables.  In the universal group \(G_0\times\langle t\rangle\),
   every word has unique form \(v\,t^e\).  If a proposed relation becomes a
   tautology in the source variables when \(t=1\), then \(v=1\), and the
   relation is only \(t^e=1\).  It cannot become a nontrivial source relation
   when \(t=-1\).  Thus an ordinary LCS/group word cannot implement the
   source-oblivious conditional relation "check \(r=1\) only on one central
   flag sector."  The desired expression
   \(p_-(t)(r-1)=0\) is additive, not a group-word equality.

3. **Private parity slack.**  Replacing each parity equation
   \(r_i=J^{b_i}\) by

   $$
   r_i s_i=J^{b_i}
   $$

   with a fresh private involution \(s_i\) makes the entire system
   classically perfect regardless of the source: choose arbitrary scalar
   signs for the old variables, set \(J=-1\), and define
   \(s_i=J^{b_i}r_i^{-1}\).  For the pair (1), two private slack words \(A,B\)
   merely replace the contradiction by \(A^{-1}B=J\), which has the scalar
   solution \(B=AJ\).

Therefore a flag, slack, or direct sum cannot obtain perfect completeness
for free.  Any surviving exactifier must use source-dependent shared
auxiliaries or noncentral cross-context structure whose perfect slack sector
itself has no finite-dimensional model.  Proving that property is already
the missing perfect LCS separation, not a consequence of the
\(1-\epsilon\) Taller--Vidick strategy.

This is a scoped no-go.  It does not rule out genuinely new shared,
noncentral equations or a new zero-noise decoder.
