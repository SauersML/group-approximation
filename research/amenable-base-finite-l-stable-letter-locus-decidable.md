---
rg: 2
id: amenable-base-finite-l-stable-letter-locus-decidable
kind: claim
title: Amenable-base finite L-presentations and their raw stable-letter simulators cannot encode totality
distinct_from:
  genuine-hnn-switches-over-amenable-bases-are-sigma1: that treats a genuine one-edge HNN extension and records the endomorphism mapping-torus case; this treats arbitrary finite substitution-orbit relators and the raw non-genuine simulator with any finite number of substitution letters.
  finite-graphs-of-amenable-groups-have-sigma1-locus: that classifies genuine finite Bass--Serre assemblies; here the substitutions need not descend to injective edge maps before the presentation kills their stable kernels.
  amenability-of-finite-presentations-is-pi2-complete: that is the open hardness root; this closes the direct finite-L-presentation and substitution-letter routes from an amenable base.
---

**ESTABLISHED.** Let
[
B_e=langle X_emid Q_eangle
]
be a computable family of finite presentations, all presenting amenable
groups. For each (e), let
(Sigma_e={sigma_{e,1},ldots,sigma_{e,s(e)}}) be a finite list of
endomorphisms of the free group (F(X_e)), supplied by their values on
(X_e), and let (R_esubset F(X_e)) be finite.

First form the finite (L)-presentation
[
L_e=
F(X_e)ig/
leftlangle!leftlangle
Q_ecup{sigma(r):sigmainSigma_e^*, rin R_e}
ightangle!ightangle .                         	ag{LNS1}
]
Then every (L_e) is amenable: it is a quotient of (B_e). Thus the
amenable locus of ((L_e)) is all indices, independently of every
substitution orbit or stable kernel.

The direct finite stable-letter simulator is
[
T_e=leftlangle X_e,t_1,ldots,t_{s(e)} middle|Q_e, R_e, t_i^{-1}xt_i=sigma_{e,i}(x)
 (xin X_e, 1leq ileq s(e))ightangle .          	ag{LNS2}
]
No invariance or injectivity hypothesis is needed. Its exact amenability
criterion is
[
T_e	ext{ is amenable}quadLongleftrightarrowquad s(e)leq 1.       	ag{LNS3}
]

For (s(e)=0), (T_e) is a quotient of the amenable group (B_e).
For (s(e)=1), let (A_e) be the image of (B_e) in (T_e). It is
amenable, and the defining relations give
(t^{-1}A_etleq A_e). Hence
[
N_e=igcup_{ngeq0}t^nA_et^{-n}
]
is an amenable directed union, is normal in (T_e), and
(T_e/N_e) is cyclic. Thus (T_e) is amenable even when the substitution
has a nontrivial stable kernel or does not descend to an endomorphism of
(B_e) before that kernel is killed.

For (s(e)geq2), killing every (xin X_e) defines an epimorphism
[
T_e	woheadrightarrow F(t_1,ldots,t_{s(e)}).
]
Therefore (T_e) is nonamenable. Consequently the amenable index set of
every computable family ((T_e)) is the syntactic set
[
{e:s(e)leq1},
]
which is recursive (indeed decided directly from the finite input), while
the amenable index set of ((L_e)) is constant. Neither can be the
nonrecursive (Pi^0_2)-complete set (mathrm{TOT}).

This remains true when the amenable base is a fixed finitely presented
solvable group with undecidable word problem: undecidable equality changes
neither quotient closure nor the free quotient in (LNS2). A possible
(Pi^0_2)-hardness construction must therefore leave this class. In
particular it must introduce relations among the controller letters that
destroy the free quotient, start before stable closure from a nonamenable
base, or use a finite-presentation mechanism not expressible as an
amenable-base quotient or a raw substitution-letter simulator.

DERIVATION
[[amenable-base-finite-l-presentations-stable-letter-proof]]
