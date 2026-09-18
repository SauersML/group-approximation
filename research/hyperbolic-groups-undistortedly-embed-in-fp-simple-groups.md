---
rg: 2
id: hyperbolic-groups-undistortedly-embed-in-fp-simple-groups
kind: claim
title: Every hyperbolic group has an undistorted (quasi-isometric) embedding into a finitely presented simple group, and every full contracting RSG is undistorted in its finitely presented simple twisted Brin-Thompson group
distinct_from:
  hyperbolic-groups-satisfy-boone-higman: that imports the BBMZ embedding into a finitely presented simple group; this proves that the same chain of embeddings is undistorted at every step.
  hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups: that is Zaremsky's full question, with a host of type F_infinity; this settles its quasi-isometric half, with a host that is finitely presented but not known to be F_infinity.
  full-group-label-length-bounds-distortion: that is the general undistortion lemma; this is its application to the BBMZ chain.
---

**ESTABLISHED** by `hyperbolic-undistorted-fp-simple-embedding-proof` (lane proof, not independently
reviewed; no priority claimed, bounded arXiv-only search).

**Statement.**
1. For every hyperbolic group `G` there is a finitely presented simple group `S` and an embedding
   `G -> S` that is a quasi-isometric embedding of word metrics, i.e. `G` is undistorted in `S`.
   Concretely `S = SV_Γ` for the full contracting RSG `Γ = [[ G*Z | ∂_h(G*Z) ]]` of BBMZ
   (arXiv:2309.06224, Theorem `thrm:hyp_to_contracting` and Proposition `prop:contr_to_simple`).
2. Every full contracting RSG `Γ` is undistorted in the finitely presented simple twisted Brin–Thompson
   group `SV_Γ` of `prop:contr_to_simple`. Here `Γ` acts on the orbit `S` of a rational point.

**What this answers.** It answers, for hyperbolic groups, the "(quasi-isometrically?)" refinement of
Zaremsky's question (arXiv:2201.00711v1, TeX main.tex l.495–497; recorded as
`hyperbolic-groups-quasi-isometrically-embed-in-fp-simple-groups`): "Do each of the following groups embed
(quasi-isometrically?) into a finitely presented simple group (even of type F_∞?) … hyperbolic groups."

The "(even of type F_∞?)" refinement stays OPEN. It asks for `SV_Γ`, or some other undistorted host, to
be of type F_∞. For `SV_Γ` this is tied to BBMZ Question `quest:F_infty` (are full contracting RSGs of type F_∞?) and
to the Belk–Zaremsky type F_n conjecture for twisted Brin–Thompson groups.

**Scope.** Finite hyperbolic groups are trivial cases. The lemmas used are
`full-group-label-length-bounds-distortion` and
`g-free-z-acts-locally-faithfully-on-horofunction-boundary`, plus the BBMZ imports listed in the route.
