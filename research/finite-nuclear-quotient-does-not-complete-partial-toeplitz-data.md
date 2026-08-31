---
rg: 2
id: finite-nuclear-quotient-does-not-complete-partial-toeplitz-data
kind: claim
title: Finite nuclear quotients do not complete arbitrary partial Toeplitz data
requires:
  - finite-positive-definite-window-is-a-relative-corner-selector
  - operator-system-face-colimit-need-not-have-concrete-group-order
distinct_from:
  exact-core-multiplicative-domain-does-not-descend-to-normal-quotient: that gives a ucp map on a free-group algebra whose minimal dilation detects a killed normal conjugate; this gives a quantitative nonextension gap for partially positive data even when the desired quotient algebra itself is finite-dimensional and nuclear.
  z2-cross-operator-system-colimit-gap-citation: that imports the qualitative infinite-lattice C-star-envelope obstruction from arXiv:2603.29958; this gives an explicit two-by-two witness on the finite square and a normalized-HS lower bound.
  finite-positive-definite-window-is-a-relative-corner-selector: that proves a full positive-definite finite-group table produces the desired corner; this shows that facewise positivity on a generating pattern does not produce that full table.
---

Let

[
G=C_2	imes C_2=langle a,bmid a^2=b^2=1, ab=baangle,qquad
Delta={1,a,b}.
]

On (H=mathbb C^2), put

[
X=egin{pmatrix}0&1\1&0end{pmatrix},qquad
Z=egin{pmatrix}1&0\0&-1end{pmatrix},
]

and define the partial operator-valued function

[
f(1)=1,qquad f(a)=X,qquad f(b)=Z.                    	ag{FNQ1}
]

Then (f) is positive definite on the positivity domain (Delta).
Nevertheless, if (F:G	o M_2) is a normalized positive-definite function
and

[
eta=max{|F(a)-X|_{2,2},|F(b)-Z|_{2,2}},
]

then

[
2leq 4eta+2sqrt{2eta},qquad
etageq {3-sqrt5over4}.                              	ag{FNQ2}
]

In particular (f) has no positive-definite extension to (G), and it
cannot even be approximated by restrictions of full positive-definite
functions with normalized-Hilbert--Schmidt error tending to zero.

The target algebra is

[
C^*(G)congmathbb C^4.
]

It is finite-dimensional, nuclear, locally reflexive, quasidiagonal, RFD,
MF, and has both LP and LLP.  Thus none of those ambient properties, alone
or in combination, upgrades arbitrary facewise-positive generator data to
the full finite Toeplitz certificate required by
`finite-positive-definite-window-is-a-relative-corner-selector`.

The missing hypothesis is complete-order compatibility with the concrete
group Fourier system, equivalently positivity after all difference
identifications and translated relation rows have been inserted.  LLP
lifts a ucp map already defined on a concrete operator system; it does not
turn a map which is only ucp on the universal coproduct of its faces into
such a map.  MF and quasidiagonality construct existential matrix models of
the algebra or of a scalar trace; they do not repair a prescribed
matrix-valued partial function.

This is the finite quantitative counterpart of
Kakariadis--Leimbach--Todorov--van Suijlekom,
*Operator systems and positive extensions over discrete groups*,
[arXiv:2603.29958](https://arxiv.org/abs/2603.29958), especially Example
5.4, Corollary 5.9, and Theorem 5.21.  Their two-axis domain in
(mathbb Z^2) separates the universal face coproduct from the concrete
commuting Fourier system; the Pauli square makes the obstruction finite and
gives the explicit gap (FNQ2).

For the authenticated Iwahori problem this is a firewall, not a
counterexample.  Its prescribed microstates satisfy additional arithmetic
relations which may force the needed complete-order compatibility.  What
cannot be used as the forcing argument is LLP, MF, local reflexivity,
quasidiagonality, or finite-dimensional nuclearity by itself.  A successful
proof must exploit those arithmetic relations to control the complete
moving quotient table (equivalently every translated normal-closure row).
The Iwahori gate and the nonhyperlinear-group root remain open.

DERIVATION
pauli-square-positive-extension-gap-proof
