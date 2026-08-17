---
rg: 2
id: boone-higman-via-universal-leavitt-host
kind: route
title: Embed the coefficient ring into this repository's finitely presented strongly simple Leavitt algebra
target: boone-higman-conjecture
requires: []
artifacts:
  - GroupApproximation/Leavitt/LeavittSimplicity.lean
  - GroupApproximation/Leavitt/FinitePresentation.lean
  - research/artifacts/boone-higman-audit-2026-08-17.md
---

This repository already owns, machine-checked, the object the ring lane wants
at the far end: `L_K(1,2)` is finitely presented
(`Leavitt/FinitePresentation.lean`, including an absolute finite ring
presentation over `F_2`) and strongly simple in the sharp form
`x != 0 => exists a, b : a x b = 1` (`Leavitt/LeavittSimplicity.lean`), with
finitely generated elementary groups (`Leavitt/ElementaryGroup.lean`),
perfect at rank at least three (`Leavitt/ElementaryPerfect.lean`) and with no
nontrivial finite quotients (`Leavitt/ElementaryNoFiniteQuotients.lean`).

The route: embed the coefficient ring `Z[G~]` — or a suitable `K`-algebra
built from it — into `L_K(1,2)`, and inherit both simplicity and finite
presentation from the host instead of manufacturing them.

Dead at `weyl-algebra-blocks-a-universal-leavitt-host`.  There is no
universal-host theorem to cite: Bilich--Hazrat--Nam prove the first Weyl
algebra does not embed in `L_K(1,2)`, because the Heisenberg equation
`xy - yx = 1` is unrealizable in any Steinberg algebra.  A route that needs
"every finitely presented `K`-algebra embeds" is refuted outright.

**What survives the demolition.**  A great deal, and this is why the route is
recorded rather than deleted.  The same paper proves *positive* embedding
results — Bergman algebras, and Leavitt path algebras of finite graphs
satisfying condition (L) — so the embeddable class is large and the specific
group rings of the Boone--Higman construction are not known to be excluded.
What is refuted is only the blanket form.  A live Leavitt route would have to
identify the coefficient algebra concretely and prove an embedding for it,
and it could not lean on generality at any point.

**A second reason the general form was never going to work.**  Even granting
an embedding `Z[G~] <= L_K(1,2)`, simplicity of the host does not give the
envelope: what is needed is a finitely presented simple *group*, and the
elementary group of a simple ring is finitely presented only under
Krstić--McCool-type hypotheses on the ring, which is a separate finiteness
question with the same shape as the one the whole region is stuck on.  Host
simplicity would have removed the ideal problem, not the presentation
problem.
