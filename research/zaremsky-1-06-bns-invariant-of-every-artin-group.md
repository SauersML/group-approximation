---
rg: 2
id: zaremsky-1-06-bns-invariant-of-every-artin-group
kind: claim
title: "Zaremsky Problem 1.6 resolved: compute the BNS invariant Sigma^1(A) of an arbitrary Artin group"
root: true
distinct_from:
  artin-sigma1-is-connected-dominant-living-subgraph: that is one candidate answer, the living-subgraph formula; this is the problem itself, resolved by any correct explicit description valid for every Artin group
  artin-sigma1-conjecture-known-families: that records the families of Artin groups where the formula is already proved; this asks for every Artin group
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 1, Problem 6, verbatim:
"Compute the BNS-invariant Σ1(A) for an arbitrary Artin group."

This claim is the question. It is established only through an answer route:

- **Living-subgraph formula**: `zaremsky-1-06-by-living-subgraph-formula`
  requires `artin-sigma1-is-connected-dominant-living-subgraph`.

Never write a `requires: []` route into this claim. If that formula is refuted,
the refutation alone does not answer the problem: a corrected explicit formula
has to be stated and proved, and it gets its own answer route.

**Reading.** `A = A_Γ` for a finite simplicial graph `Γ` with edge labels
`l(e) >= 2`, relations `uvu... = vuv...` (`l(e)` letters each side). A character
is a nonzero homomorphism `χ : A_Γ -> R`; `Σ^1(A_Γ)` is the Bieri–Neumann–Strebel
invariant inside the character sphere `S(A_Γ)`. "Compute" means an explicit rule,
in terms of the labelled graph `Γ` and the values `χ(v)`, deciding membership.
Along an odd edge `χ(u) = χ(v)`, since the two generators are conjugate.

**Status (checked 2026-09-13).** Open in general. The candidate rule is the
Σ¹-conjecture, first stated explicitly by K. Almeida (J. Group Theory 21 (2018)
189–228) and quoted as Conjecture 1.1 / 2.16 in M. Escartín-Ferrer,
arXiv:2501.08692v3 (14 July 2025). Meier (Proc. LMS 74 (1997)) proved one
inclusion and a weak form of the other (`artin-sigma1-living-subgraph-bounds`);
the formula is proved for the families in `artin-sigma1-conjecture-known-families`.
No later paper deciding it was found (arXiv listing and citing-paper search,
bounded; MathSciNet not reached).

## Attempts

- 2026-09-13 (z1-06-bns-artin): region opened; known results imported with
  exact statements from Escartín-Ferrer arXiv:2501.08692v3 §1–§4. Work toward
  the missing inclusion (disconnected living subgraph implies `[χ]` not in `Σ^1`)
  is recorded under `artin-sigma1-is-connected-dominant-living-subgraph`.
