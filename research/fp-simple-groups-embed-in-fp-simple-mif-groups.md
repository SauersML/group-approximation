---
rg: 2
id: fp-simple-groups-embed-in-fp-simple-mif-groups
kind: claim
title: Every finitely presented simple group embeds in a finitely presented simple mixed-identity-free group
distinct_from:
  boone-higman-conjecture: that embeds decidable finitely generated groups in finitely presented simple groups; this starts from a finitely presented simple group and asks for a finitely presented simple overgroup with no mixed identities, which is what makes it land in a twisted Brin--Thompson group.
  aut-free-groups-satisfy-permutational-boone-higman: that imports the Aut(F_n) theorem and the universality of twisted Brin--Thompson groups among finitely presented simple MIF groups (Corollary D); this is the open question of whether every finitely presented simple group has such an overgroup.
---

**OPEN.** Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, pose it as
Question 3.4: "Does every finitely presented simple group embed in a finitely
presented simple MIF group?" The question number was confirmed by lane
`bh-reviewer` from the PDF text on MSI (review artifact §12, 43f7e25d3).

**Why it matters.**
- **Universality:** their Corollary D says finitely presented simple twisted
  Brin--Thompson groups are universal among finitely presented simple highly
  transitive groups, and more generally among finitely presented simple MIF
  groups.
- **BFFHZ's remark:** a positive answer makes the permutational Boone--Higman
  conjecture equivalent to Boone--Higman, and a negative answer refutes the
  permutational conjecture. The route for the first half is
  `permutational-boone-higman-via-mif-envelopes`.
- **Not verified here:** that remark was not re-derived line by line.

## Attempts

The claim was opened on 2026-09-12 by lane `bh-twisted-brin-thompson` as the
explicit hinge between the two conjectures.

1. **Relative automorphism reformulation (2026-09-13, lane `solve-bh-q34`):
   an equivalence, not an answer.** By
   `pbh-passes-to-relative-free-group-automorphisms`, for a finitely presented
   simple `S` and `n >= 2`, this question for `S` holds exactly when
   `Aut_S(S * F_n)` embeds in some group with an action of type (A). For
   centerless `S` that group is finitely presented (BFFHZ Proposition 1.1), so
   the question becomes one permutational instance for an explicit finitely
   presented group. A positive answer to BFFHZ Question 3.2 for `S` would give it.
2. **Faithfulness through a larger target: unclear, and constrained.** Acting
   on `Hom_S(S * F_n, M)` for a simple MIF overgroup `M ⊋ S`, not required to be
   finitely presented, makes the action faithful: a kernel element changes some
   `x_i` by a mixed identity of `M` with constants in `S`. Precomposition
   preserves the image subgroup `⟨S, φ(x_1), ..., φ(x_n)⟩`, so finitely many
   orbits of points already forces `M` to have only finitely many subgroups of
   that form. Finitely many orbits of pairs and finite generation of stabilizers
   were not examined. Restricting to tuples inside `S` brings back the original
   kernel.
3. **Rank one: blocked by a known open problem.** For `n = 1` the action on
   `Hom_S(S * F_1, S) = S` is faithful for every nontrivial centerless `S` (BFFHZ
   Observation 2.4). But BFFHZ note right after it that finitely many orbits of
   pairs would need finitely many conjugacy classes, "and it is an open question
   whether it can ever occur for a finitely presented infinite G". This is
   Makowsky's problem FP19, as recorded in
   `research/artifacts/ideas-2026-09-13/bh/bh-pbh-separation.md`.
4. **Leavitt unit groups: test not decided.** The repo's finitely presented simple
   Leavitt unit groups (`binary-leavitt-unit-group-is-simple`,
   `leavitt-unit-group-finitely-presented`) contain Thompson-type permutation
   units, but they are not groups of homeomorphisms of the Cantor space, so BFFHZ
   Remark 3.5 does not apply. Expanding the characteristic-2 unipotent
   commutator `[1+e, x(1+e)x^-1]` with `e^2 = 0` and `f = x e x^-1` gives
   `1 + ef + fe + efe + fef + efef`. Nothing forces this to equal 1, but no
   explicit witness `x` was exhibited, so it is not excluded as a mixed identity.
   No mixed identity and no MIF proof was found.
5. **Leavitt unit groups: settled positively (2026-09-13, lane
   `solve-q34-known-actors`).** For every prime `p`,
   `L_(F_p)(1,2)^× / F_p^×` acts faithfully and 2-transitively on the lines of the
   Chen module of the tail class of `0^∞`, with finitely generated line stabilizers
   (`leavitt-units-act-two-transitively-on-chen-module-lines`). So it is of type (A)
   and this question holds for these groups
   (`leavitt-unit-groups-mod-scalars-satisfy-pbh`, not independently reviewed).
   - **Binary case.** It was reached independently through the Cantor module
     (19108f02e).
   - **Still open.** The tensor-square Leavitt unit groups, where the germ ring becomes
     a two-variable Laurent ring.
   - **Census.** `research/artifacts/q34-known-actors-coverage-2026-09-13.md` records
     the family-by-family coverage.
