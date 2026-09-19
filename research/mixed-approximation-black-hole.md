---
rg: 2
id: mixed-approximation-black-hole
kind: claim
title: A finitely presented mixed sofic/MF approximation black hole
artifacts:
  - docs/COMPRESSION_COLLAPSE_MF_RADICAL.md
---

Credit: derived from Fournier-Facio's small-cancellation suggestion
(personal communication, 2026-08-14, in the context of his
arXiv:2608.02025) and the amplifier of his arXiv:2512.09180
Proposition B (session development, GPT-5.6-assisted, unrefereed).
The two FF papers play distinct roles and must not be conflated:
arXiv:2608.02025 (+ Hull/Osin, as in
[[defect-saturation-full-mf-radical]]) supplies the torsion-free
compression-configuration existence input; arXiv:2512.09180
Proposition B is the separate simple-envelope amplifier that would
supply the universal-embedding refinement.  Neither input is
source-verified at theorem level for this claim's purposes
(2512.09180's Propositions B/C in particular have not been read
against the PDF), and nothing here is formalized.

Claim: there is a 2-generated finitely presented property-(T)
acylindrically hyperbolic group whose every nontrivial quotient is
simultaneously nonsofic and non-MF; consequently it is pointwise
Hamming-stable and operator-norm-stable while being neither sofic nor
MF.

Refinement (UNSUPPORTED in current artifacts — flagged 2026-08-15): "it
can be arranged to contain every finitely generated recursively
presented group."  The only universality available in the artifacts is
the universal finitely presented **torsion-free** group `U` of
`docs/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md` §1, which
contains every finitely presented torsion-free group — a strictly
weaker statement.  The f.g.-recursively-presented version would have to
come from the `C` parameter of arXiv:2512.09180 Proposition B, which no
artifact works out.  Do not build on the refinement until that is done.

Mixed-quotient plumbing exists in Stability/MixedApproximation.lean;
the existence input for the unrefined claim is the same Hull/Osin
program as [[defect-saturation-full-mf-radical]] (audited 2026-08-15,
see `docs/TORSION_FREE_NORMAL_GENERATION_HULL_QUOTIENT.md` §9) plus the
nonsofic heredity of
[[defect-normally-generates-torsion-free-quotient]] item 3.

## Why this sits off the root graph

Two reasons, and the second is the binding one.

The inputs are not source-verified at theorem level — arXiv:2512.09180's
Propositions B and C have not been read against the PDF — so an edge from here
into a root would put unverified literature on a path to a program target,
which is exactly what the trust-surface discipline forbids.

And the conclusion does not fit either root that looks close.  It carries no
torsion-free adjective, so it cannot feed
[[torsion-free-finitely-presented-non-mf]]; and its group is nonsofic by
construction, so it cannot feed [[finitely-presented-sofic-non-mf]].  The
landmark it would serve — finitely presented, every nontrivial quotient
simultaneously nonsofic and non-MF — is not a node, and should not become one
until the amplifier is verified.
