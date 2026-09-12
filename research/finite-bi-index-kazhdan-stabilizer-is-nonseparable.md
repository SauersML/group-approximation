---
rg: 2
id: finite-bi-index-kazhdan-stabilizer-is-nonseparable
kind: claim
title: Every infinite finite-rank Kazhdan stabilizer is nonseparable and forces a non-Haagerup actor
distinct_from:
  hs-stable-finite-bi-index-kazhdan-pair-exists: that asks for a stable host; this proves two structural filters that every candidate host must violate.
  very-flexible-actor-stability-closes-finite-rank-pauli-host: that turns an LLP--RFD actor into a nonhyperlinear Pauli host; this identifies why all present a-T-menable and subgroup-separable actor classes miss the hypothesis.
  kun-thom-coset-action-has-infinite-orbit-rank: that excludes one named action by an explicit infinite double-coset quotient; this applies abstractly to every finite-rank infinite action.
---

**ESTABLISHED STRUCTURAL NO-GO.**

Let (Hle G) and suppose
[
 |Hackslash G/H|<infty.                                	ag{FBI1}
]

1. If (H) is separable in (G), then ([G:H]<infty).
2. Consequently, if (G/H) is infinite, then (H) is not separable in
   (G).
3. If moreover (H) is infinite and has property ((T)), then (G) does
   not have the Haagerup property.

The first assertion is elementary but strong.  Every intermediate subgroup
(K), (Hle Kle G), is a union of (H)-double cosets: if (kin K),
then (HkHsubseteq K).  Hence (FBI1) implies that there are only finitely
many intermediate subgroups, at most
[
 2^{|Hackslash G/H|}.                                   	ag{FBI2}
]
Separability says
[
 H=igcap_{substack{Kge H\\[G:K]<infty}}K.             	ag{FBI3}
]
The family in (FBI3) is finite by (FBI2), so its intersection has finite
index in (G).  This proves (1) and (2).

For (3), the Haagerup property passes to subgroups.  A discrete group with
both the Haagerup property and property ((T)) is finite: its proper affine
isometric action has a fixed point and hence a bounded orbit, forcing the
group itself to be finite.  Thus an infinite Kazhdan (H) cannot lie in a
Haagerup (G).

These facts sharply constrain the actor sought by the finite-rank
shared-Pauli route.  An infinite transitive finite-rank action
(Gcurvearrowright G/H) with Kazhdan stabilizer must have all of the
following features:
[
 [G:H]=infty,qquad |Hackslash G/H|<infty,qquad
 H	ext{ finitely generated and nonseparable in }G,        	ag{FBI4}
]
and the actor (G) must be non-Haagerup.

There are two immediate search consequences.

- No LERF actor can work.  Property ((T)) makes (H) finitely generated,
  so LERF would make (H) separable, contradicting (FBI4).
- None of the current very-flexibly stable classes in
  Fournier-Facio--Willett, arXiv:2603.18456v2, Theorem 1.2, can work.  The
  authors explicitly note after Question 1.8 and in the proof of Corollary
  7.19 that all those examples are a-T-menable.

The RFD requirement does not contradict (FBI4), but makes the target more
specific.  If (G) is finitely generated and (C^*(G)) is RFD, then (G)
is residually finite.  Indeed, for (g
e1), RFD supplies a
finite-dimensional unitary representation (pi) with (pi(g)
e I).
The finitely generated linear group (pi(G)) is residually finite by
Malcev, so a finite quotient of (pi(G)), and hence of (G), separates
(g).  Thus a finitely presented LLP--RFD actor for the Pauli construction
would have to be
[
 	ext{residually finite but not LERF, with a specified nonseparable
 infinite Kazhdan subgroup of finite bi-index}.            	ag{FBI5}
]

This does not prove that LLP excludes such a packet.  It proves that all
Haagerup and subgroup-separable constructions are unavailable and isolates
the exact exotic subgroup geometry that an LLP--RFD construction must
have.
