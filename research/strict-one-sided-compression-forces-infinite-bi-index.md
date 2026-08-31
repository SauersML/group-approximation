---
rg: 2
id: strict-one-sided-compression-forces-infinite-bi-index
kind: claim
title: A strict one-sided compressor forces infinitely many double cosets
distinct_from:
  kun-thom-coset-action-has-infinite-orbit-rank: that uses the arithmetic projection for the explicit Laurent actor; this proves infinite orbit rank for every strict compression pair.
  finite-bi-index-kazhdan-stabilizer-is-nonseparable: that derives nonseparability from finite bi-index; this shows that the one-sided compression mechanism never reaches finite bi-index in the first place.
  fournier-facio-torsion-free-skeleton: that records the published compression pair; this proves its coset action has infinite rank.
---

**ESTABLISHED GENERAL OBSTRUCTION.**

Let (Hle G), and suppose that some (tin G) is a strict one-sided
compressor:
[
 tHt^{-1}<H.                                                	ag{SCI1}
]
Then
[
 |Hackslash G/H|=infty.                                  	ag{SCI2}
]

Indeed, for every (nge1),
[
 Ht^{-n}H=t^{-n}H.                                          	ag{SCI3}
]
To see this, for (hin H),
[
 ht^{-n}=t^{-n}(t^nht^{-n}),
]
and (t^nHt^{-n}le H).

The right cosets in (SCI3) are pairwise distinct.  If (m>n) and
[
 t^{-m}H=t^{-n}H,
]
then (t^{m-n}in H).  But repeated conjugation of the strict inclusion
(SCI1) gives
[
 t^kHt^{-k}<Hqquad(kge1),                                 	ag{SCI4}
]
whereas (t^kin H) would imply (t^kHt^{-k}=H).  This contradiction
proves (SCI2).

There is an immediate infranormal consequence.  Recall
[
 P_H={gin G:gHg^{-1}le H}.
]
If (P_H) generates (G) and (H) is not normal, then some
(tin P_H) must make the inclusion strict.  Otherwise every element of
(P_H) would normalize (H), hence so would the group it generates.
Therefore
[
 H	ext{ infranormal but not normal in }G
 quadLongrightarrowquad |Hackslash G/H|=infty.        	ag{SCI5}
]

Thus every pair covered by Kun--Thom's nonsofic wreath theorem has an
infinite-rank coset action.  The finite-rank shared-Pauli presentation and
the strict-compression Kun--Thom mechanism are structurally disjoint; no
choice of the explicit Laurent parameters can make the same stabilizer
satisfy both.

The Fournier--Facio torsion-free pair is also covered directly.  In the
notation of arXiv:2608.02025v2,
[
 Gamma=pi(P),qquad
 t_1Gamma t_1^{-1}=pi(P_1)leGamma.
]
The nontrivial simple group (pi(S)) lies in (Gamma), while the proof
gives
[
 pi(P_1)cappi(S)=1.
]
Hence (t_1Gamma t_1^{-1}<Gamma), and (SCI2) gives
[
 |Gammaackslash G/Gamma|=infty.                        	ag{SCI6}
]
So that published torsion-free nonsofic construction cannot instantiate a
finite-rank actor either.
