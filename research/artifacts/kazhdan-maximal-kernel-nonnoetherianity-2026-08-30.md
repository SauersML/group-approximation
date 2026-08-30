# Kazhdan maximal kernels are not normally Noetherian

## Result

There is one finitely presented torsion-free word-hyperbolic property-`(T)`
group with continuum many characteristic maximal proper normal subgroups
which are not finitely normally generated.  Their quotients may simultaneously
be taken infinite, simple, torsion-free, pairwise non-isomorphic and
property-`(T)`.

This is a consequence of two primary sources plus the elementary countability
of finite presentations.  It appears not to have been incorporated in Cairn
before this audit.

## Source 1: the fixed ambient group

Arzhantseva--Steenbock, [*Rips construction without unique
product*](https://arxiv.org/abs/1407.2441), Corollary 1, constructs a
torsion-free Gromov-hyperbolic group with Kazhdan's property `(T)` and without
the unique-product property.  It is infinite and non-elementary, and
hyperbolicity gives finite presentability.

## Source 2: continuum many simple characteristic quotients

Coulon--Fournier-Facio, [*Infinite simple characteristic
quotients*](https://arxiv.org/html/2312.11684v2), Corollary 4.2, in the
revision dated 24 August 2026, states that a torsion-free non-elementary
hyperbolic group has continuum many pairwise non-isomorphic infinite simple
characteristic quotients with any prescribed set of prime torsion orders.
Choosing the empty set keeps the quotients torsion-free.  Property `(T)`
passes to every quotient.

## The finite-presentation extraction

Only countably many isomorphism types of groups have finite presentations.
Consequently continuum many quotients in Source 2 are not finitely presented.
Their characteristic kernels are maximal proper normal subgroups because the
quotients are nontrivial and simple.  Since the ambient hyperbolic group is
finitely presented, a kernel is finitely normally generated if and only if
its quotient is finitely presented.  Thus continuum many of these maximal
kernels are not finitely normally generated.

## Exact Boone--Higman consequence

The Chatterji--Kassabov route still asks an existential and construction-
specific question: whether its explicit elementary-matrix envelope has
**some** finitely normally generated maximal kernel which misses the embedded
simple core.  The theorem above does not decide that.

What it does decide is the proposed generic shortcut.  Property `(T)` cannot
supply `Max-n`, even in the much narrower class of torsion-free finitely
presented word-hyperbolic groups.  Any successful proof for the
Chatterji--Kassabov envelope must use its matrix/ring structure or a selected
quotient, not Kazhdan normal-lattice Noetherianity.

