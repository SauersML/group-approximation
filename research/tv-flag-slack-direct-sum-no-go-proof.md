---
rg: 2
id: tv-flag-slack-direct-sum-no-go-proof
kind: route
title: Eliminate source-oblivious flag, slack, and direct-sum exactifiers
target: tv-central-flags-and-private-slacks-cannot-exactify
requires:
  - taller-vidick-positive-noise-collapses-central-sign
---

# Eliminate source-oblivious flag, slack, and direct-sum exactifiers

## 1. The exact positive-noise pair

Taller--Vidick Definition 4.1 samples \(f,g\), an independent Bernoulli mask
\(\mu\), and sets \(g'=fg\mu\); the verifier then imposes one folded
three-variable parity equation.  See
[Definition 4.1 and Proposition 4.1](https://arxiv.org/html/2507.22444v2#S4)
in arXiv:2507.22444v2.  Their completeness lemma gives only
\(1-\epsilon\), while the decoder obtains the factor
\(4\epsilon\delta^2\); see
[lines 409--435 of the HTML version](https://arxiv.org/html/2507.22444v2#S4).

The prerequisite
`taller-vidick-positive-noise-collapses-central-sign` makes the relevant
support calculation explicit.  For any folded query \(f\), choose the two
positive-probability masks \(\mu=f^\uparrow\) and
\(\mu=-f^\uparrow\), with query \(f\) in the first equation and \(-f\) in
the second.  Both make \(g'=g\).  Folding identifies the left generator and
reverses the sign.  Hence the finite LCS presentation contains

$$
L=J^a,
\qquad
L=J^{a+1}                                               \tag{1}
$$

for one and the same group word \(L\).  The following arguments use only
(1).

## 2. A direct-sum block carrying the old test has zero support

Let \(\pi\) be any representation in which \(\pi(J)=-I\).  Suppose
\(p\) is a projection commuting with the represented variables and the old
equations are required on \(p\mathcal H\).  Algebraically,

$$
p(\pi(L)-\pi(J)^a)=0,
\qquad
p(\pi(L)-\pi(J)^{a+1})=0.                               \tag{2}
$$

Subtracting the two identities gives

$$
p\,\pi(J)^a(I-\pi(J))=0.
$$

Since \(\pi(J)=-I\), this is \(2p\pi(J)^a=0\).  Therefore

$$
p=0.                                                    \tag{3}
$$

No nonzero block of a perfect \(J=-I\) model can retain both old
positive-noise equations.

The same fact at strategy level is just positivity of loss.  If a flagged
direct sum is the convex combination

$$
q=\theta q_{\rm old}+(1-\theta)q_{\rm slack},
$$

then its loss on the finite test is

$$
1-\omega(q)
 =\theta(1-\omega(q_{\rm old}))
  +(1-\theta)(1-\omega(q_{\rm slack})).                 \tag{4}
$$

The explicit pair (1) gives \(\omega(q_{\rm old})<1\) in every operator
model.  Thus \(\omega(q)=1\) forces \(\theta=0\), unless the equations
themselves were changed on that block.  A direct sum does not convert the
near-perfect honest block into an exact one; it discards it.  If the
remaining slack block is a fixed finite-dimensional accept block, the same
block is a perfect strategy on NO instances and the soundness gap is zero.

## 3. A central group word cannot be a conditional relation

The desired direct-sum gate is often written informally as "if the flag is
active, check \(r=1\)."  Let \(t\) be a central involution and

$$
p_-(t)=\frac{I-t}{2}.
$$

At the level of a \(*\)-algebra, the conditional relation is

$$
p_-(t)(r-I)=0.                                          \tag{5}
$$

Expression (5) is a sum of group elements.  It is not an ordinary group-word
identity.

There is a sharp normal-form reason.  Let \(G_0\) be the universal group of
the source generators before the proposed conditional constraints; it may
already include involution relations and the commutations that are meant to
hold in both sectors.  Adjoining a central flag without further relations
gives

$$
G_0\times C_2.
$$

Every element has a unique form

$$
v\,t^e,
\qquad v\in G_0,\quad e\in\{0,1\}.                      \tag{6}
$$

Suppose a proposed group-word relator \(w(t,X)=1\) is source-obliviously
inactive at \(t=1\): after that specialization it is the identity element of
\(G_0\), for arbitrary source generators.  By (6), its \(G_0\) component is
\(v=1\).  Hence \(w=t^e\).  Imposing \(w=1\) either does nothing or pins the
flag; it cannot impose a nontrivial relation on the source generators at
\(t=-1\).

This applies simultaneously to any finite list of such source-oblivious
word gates.  An LCS equation is a particularly restricted group-word
relation, so it cannot do better.  A relation such as \(tr=1\) is not a
counterexample: at \(t=1\) it already imposes \(r=1\), and at \(t=-1\) it
imposes the opposite sign rather than freeing the branch.

The normal-form argument deliberately does not cover source-dependent
shared auxiliaries.  Those are not a free accept flag; their extension
problem can carry the whole missing separation.

## 4. Fresh equationwise slacks make a scalar perfect model

Consider an arbitrary finite binary LCS with old parity equations

$$
r_i=J^{b_i}.
$$

The most literal slack repair replaces them by

$$
r_i s_i=J^{b_i},                                        \tag{7}
$$

where \(s_i\) is a fresh involutory variable appearing in no other parity
equation.  Give every old variable an arbitrary scalar sign, set \(J=-1\),
and define

$$
s_i:=J^{b_i}r_i^{-1}\in\{+1,-1\}.                       \tag{8}
$$

All local commutations hold automatically in one dimension, every \(s_i\)
is an involution, and (7) holds.  Thus (7) has a one-dimensional
\(J=-1\) representation for every source instance.  Its LCS game is
classically perfect, so it has no NO-instance soundness at all.

More locally, suppose the two equations (1) are replaced by

$$
LA=J^a,
\qquad
LB=J^{a+1},                                             \tag{9}
$$

where \(A,B\) are slack words.  Solving for \(A,B\) gives

$$
A^{-1}B=J.                                              \tag{10}
$$

The old conclusion \(J=1\) is gone, but only because the slack absorbs the
central sign.  In scalar dimension one, choose either sign for \(A\) and
put \(B=AJ\).  Private slacks therefore remove the obstruction and the
soundness simultaneously.

Sharing and constraining the slacks can prevent this scalar extension only
by coupling different source contexts.  Acyclic sharing is covered by
`join-tree-overlap-gadgets-have-no-contextual-escape`; atomwise
scalar-extendable parity sharing is covered by
`lcs-parity-gadgets-preserve-odd-dictator-affine-hull`.  Cyclic,
nonclassical, source-dependent sharing is outside the present theorem, but
it is a new finite presentation and needs its own reverse decoder.

## 5. Exact residual gate

The three conclusions are disjoint and exhaustive for the advertised
simple repairs:

- retaining the old equations on a nonzero direct-sum block is impossible;
- a source-oblivious central word flag cannot express conditional checking;
- fresh private parity slacks create a scalar perfect strategy.

Accordingly, a successful exactification cannot merely attach a finite
accept sector to the published \(1-\epsilon\) strategy.  It must delete or
replace positive-noise equations and introduce source-dependent shared
structure whose perfect commuting sector survives but whose finite
near-perfect sectors decode back to the source BCS.  That is precisely the
new zero-noise/shared-auxiliary theorem still missing from the
Taller--Vidick route.
