---
rg: 2
id: bffhz-q33-is-normal-finite-generation-of-mixed-identities
kind: claim
title: BFFHZ Question 3.3 at rank k says the k-variable mixed identities of G are normally finitely generated, it descends to all lower ranks, and it forces a finite basis over overgroups
requires:
  - bffhz-q32-forces-finitely-based-mixed-identities
distinct_from:
  bffhz-q32-forces-finitely-based-mixed-identities: that derives a finite basis over overgroups from BFFHZ Question 3.2 (finite presentation of the automorphism action image); this is the analogous statement for the companion Question 3.3 (finite presentation of G * F_k modulo its mixed identities), with a sharper, normal-closure form and descent in the rank.
  bffhz-q32-for-fp-simple-groups: that is the open Question 3.2; this is an equivalent reformulation and consequences of Question 3.3, which it does not imply or follow from as far as shown here.
  fp-simple-group-with-non-finitely-based-mixed-identities: that asks for a witness group; this shows such a witness answers Question 3.3 negatively at every rank.
artifacts:
  - research/artifacts/gq-bh-bh-bbmz-problems-status.md
---

**ESTABLISHED** by `bffhz-q33-mixed-identities-proof` (lane proof, elementary, not
reviewed; no priority claimed).

## The question

Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, Question 3.3, as
transcribed in `research/artifacts/gq-bh-bh-lit-survey.md` §3: "For G a finitely
presented simple group, is the quotient of G∗F_n by the Jacobson radical J_G(G∗F_n)
finitely presented?"

Here `J_G(G * F_k)` is the intersection of the kernels of all homomorphisms
`G * F_k -> G` that restrict to the identity on `G`. So it is `J_k(G)`, the set of
`k`-variable mixed identities of `G`, in the notation of
`bffhz-q32-forces-finitely-based-mixed-identities`. This reading of BFFHZ's
definition is the standard one. The definition itself was not re-read at source.

## Statement

Let `G` be a finitely presented group and `k >= 1`. Write `Q3.3(G,k)` for "the
quotient `(G * F_k) / J_k(G)` is finitely presented".
1. **Reformulation.** `Q3.3(G,k)` holds iff `J_k(G)` is the normal closure in
   `G * F_k` of finitely many elements.
2. **Descent.** `Q3.3(G,k)` implies `Q3.3(G,j)` for every `1 <= j <= k`.
3. **Finite basis.** `Q3.3(G,k)` implies that `J_j(G)` is finitely based over
   overgroups for every `j <= k`, in the sense of
   `bffhz-q32-forces-finitely-based-mixed-identities`. If `G` also has solvable
   word problem, then `J_1(G), ..., J_k(G)` are recursive, by part (C) of that node.
4. **MIF groups.** If `G` is mixed-identity-free, then `J_k(G) = 1` and `Q3.3(G,k)`
   holds for every `k`.

## Consequences

- **A single witness kills every rank.** A finitely presented simple group `G` with
  `J_1(G)` not finitely based over overgroups
  (`fp-simple-group-with-non-finitely-based-mixed-identities`) answers Question 3.3
  negatively at every rank `k`. By `bffhz-q32-forces-finitely-based-mixed-identities`,
  the same group answers Question 3.2 negatively at every rank `n >= 2`. So one
  witness settles both published questions for `G`.
- **Answered for T (update 2026-09-18).** Every open case of Question 3.3 is a non-MIF
  finitely presented simple group. For Thompson's `T`, whose one-variable mixed identities
  are decidable (`thompson-t-mixed-identity-problem-is-decidable`), the answer is negative
  at every rank: `thompson-t-mixed-identities-are-not-finitely-normally-generated` shows
  `J_1(T)` is not finitely normally generated in `T * Z`. Part 2 then gives every rank.
- **No implication with Question 3.2 is shown in either direction.** Question 3.2
  gives a finite basis through substitution instances, which is weaker than part 1.
  Question 3.3 says nothing about the automorphism action.
