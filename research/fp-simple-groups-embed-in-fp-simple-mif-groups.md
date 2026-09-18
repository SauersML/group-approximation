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
6. **Binary Leavitt unit group: MIF, which decides the test of Attempt 4
   (2026-09-13, lane `solve-mif-leavitt-units`).** `binary-leavitt-unit-group-is-mif`
   shows that `L_(F_2)(1,n)^×` has no mixed identity for every `n >= 2`. It has not
   been independently reviewed.
   - **How.** The criterion `linearly-transitive-groups-without-finite-rank-elements-are-mif`
     is a linear analogue of high transitivity. On the Cantor module, depth-`K` matrix
     units extend every finite-dimensional partial isomorphism, and simplicity of the
     algebra gives `g - 1` infinite rank for `g != 1`.
   - **Consequences.** `U = L_(F_2)(1,2)^×` is itself a finitely presented simple MIF
     group. So this question holds for `U` with `U` as its own overgroup, Theorem E
     applies to `U`, and the commutator of Attempt 4 is not a mixed identity.
   - **Not known.** Whether `U` is highly transitive. BFFHZ Remark 3.5 (l.730--731) knows
     of no finitely presented simple group that is MIF but not highly transitive.
   - **Scope.** Over `F_p` with `p > 2` the unit group has central scalars, so MIF is
     claimed only over `F_2`. The quotients of Attempt 5 were not tested for MIF.
   - **Commutator subgroups of Röver--Nekrashevych groups.** These are already covered
     by BFFHZ Remark 3.5 (`bh-reviewer/2503.21882.txt` l.733--738): "This includes any
     finitely presented simple groups of homeomorphisms of the Cantor space
     {1,...,n}^N that contain the commutator subgroup of the Higman–Thompson group V_n.
     In particular this includes Thompson's group V itself, along with all finitely
     presented commutator subgroups of Röver–Nekrashevych groups V_n(G) [Nek18,
     Theorem 4.7]."
     - BFFHZ call these "obviously" highly transitive, hence MIF by the Hull--Osin
       dichotomy.
     - That dichotomy is arXiv:1501.04182, `HTA-final.tex` l.937--943, theorem
       `dichoto`, cited by BFFHZ as [HO16, Theorem 5.9]: "Let $G$ be a highly
       transitive countable group. Then one of the following two mutually exclusive
       conditions holds. (a) $G$ contains a normal subgroup isomorphic to
       $Alt(\mathbb N)$. (b) G is MIF."
     - The high-transitivity argument is not written out in BFFHZ and was not
       re-derived here.
7. **Tensor-square Leavitt unit groups: settled positively (2026-09-13, lane
   `solve-q34-tensor-leavitt`).**
   - **The action.** `leavitt-square-units-act-two-transitively-on-chen-lines`:
     `(L_p ⊗ L_p)^× / F_p^×` acts faithfully and 2-transitively on the lines of
     `F_p[D × D]`. The vector stabilizer is generated by a corner copy of the unit group,
     one transvection, `g ⊗ g`, and two nilpotent transvections `w_1`, `w_2`.
   - **The germ ideal.** It is `(s_1 − 1, s_2 − 1)`, which is not principal. A four-move
     reduction through a fresh point replaces the Euclidean algorithm, and it needs only
     unimodularity.
   - **Conclusion.** `leavitt-square-unit-groups-mod-scalars-satisfy-pbh` (ESTABLISHED, not
     independently reviewed): these finitely presented simple groups satisfy PBH, so they
     answer Question 3.4 positively.
   - **The unit groups themselves.** `prime-field-leavitt-units-act-with-type-a-on-chen-vectors`
     lifts both line actions to nonzero vectors, where the pair orbits are still finite.
     This gives `L_(F_p)(1,2)^×` and `(L_p ⊗ L_p)^×` type (A) actions. For odd `p` it
     establishes `prime-field-leavitt-unit-groups-satisfy-pbh` through
     `prime-field-leavitt-pbh-via-chen-module-vectors`.
   - **Graph algebras.** In characteristic two, `char-two-leavitt-path-unit-groups-satisfy-pbh`
     already covers `L_F(E)^×` by embedding. Their finite presentation and simplicity stay
     OPEN (`f2-leavitt-path-unit-groups-fp-simple-steinberg`), so they add no new finitely
     presented simple instance of the question yet.
8. **Precomposition on larger targets: the stabilizer and pair clauses kill every
   infinitely presented target (2026-09-17, lane `swarm-0917-w4-bh-mif`).** This
   settles what Attempt 2 left unexamined. By
   `precomposition-type-a-target-is-finitely-presented` (ESTABLISHED, elementary, not
   independently reviewed), let `Aut_S(S * F_n)` act by precomposition on an invariant
   set `Ω ⊆ M^n`, where `M ⊇ S`. Suppose `Ω` contains a redundant generating tuple
   `b = (b_1, ..., b_{n-1}, 1)` with `⟨S, b_1, ..., b_{n-1}⟩ = M`.
   - **Stabilizer clause.** A finitely generated `Stab(b)` forces `ker π_b` to be
     finitely normally generated, so `M` is finitely presented.
     - **The invariant.** The displacement subgroup `D = ⟨⟨α(g)g^{-1} : α ∈ Stab(b)⟩⟩`.
       It is finitely normally generated by the images of the generators on `x_i`.
     - **Why it is the whole kernel.** It contains `x_n` through `x_1 -> x_1 x_n`, and
       every relator not involving `x_n` through `x_n -> x_n w`.
   - **Pair clause.** Finitely many orbits of pairs force `M` to have finitely many
     normal subgroups. The pair `(b, (b_1, ..., b_{n-1}, ℓ))` has invariant
     `{y : (1, y) ∈ H} = ⟨⟨ℓ⟩⟩`. They also force `C_M(S)` to be finite, because
     `c b c^{-1}` lies in the orbit of `b` for `c ∈ C_M(S)` and gives the graph of `inn(c)`.
   - **Where the class dies.** Every infinitely presented simple MIF overgroup dies at
     type (A) clause (ii) once `Ω` contains a redundant tuple. That covers `Ω = M^n` and
     the set of all generating tuples when `n` exceeds the relative rank. This includes
     overgroups from Osin-type small cancellation or inductive limits, and any target
     with unsolvable word problem.
   - **Survivors.** Only finitely presented targets survive, with finitely many normal
     subgroups, finite `C_M(S)`, and no `w ∈ S * F_n` vanishing on the orbit. If `M` is
     a finitely presented simple MIF group, the question for `S` is already answered.
     So the route can only add something through finitely presented targets that are
     MIF relative to `S` but not known to be MIF.
   - **Not covered.** Orbits with no redundant tuple give only
     `D ⊇ ⟨⟨N ∩ (S * F(x_k : k ≠ i)) : i⟩⟩`.
9. **A route through V times minimal free SFT full groups (2026-09-17, lane
   `swarm-0917-w5-bh-mif`).** This is the first route in the graph with this claim
   as target: `fp-simple-mif-embedding-via-permutational-boone-higman`. It fires
   through `permutational-boone-higman-via-v-times-aperiodic-sft-full-groups`
   once the two OPEN premises of the Boone--Higman route
   `boone-higman-via-v-times-aperiodic-sft-full-groups` are proved:
   - (P1) `decidable-groups-embed-in-fp-groups-with-minimal-free-sft`;
   - (P2) `v-times-minimal-free-sft-alternating-full-groups-are-fp`.
   - **New ESTABLISHED pieces (elementary, not independently reviewed).**
     - `v-times-minimal-action-groupoid-clopens-are-equivalent`: all nonempty clopen
       sets of `C × X` are equivalent under `G_V × (Λ ⋉ X)` for any minimal `Λ ⋉ X`.
       Match fibres over atoms with `V`, then cover `X` by translates of the
       projection, starting with the projection itself.
     - `fp-clopen-transitive-full-cantor-groups-have-type-a-actions`: fullness,
       clopen-transitive local maps and finite presentation give a type (A) clopen
       action, with stabilizers `D × D` and at most 16 pair orbits. This removes the
       standard-V hypothesis of `fp-full-binary-cantor-groups-have-type-a-actions`,
       which is why the Boone--Higman route had left the type (A) corollary
       unclaimed.
     - `fp-v-times-minimal-action-full-groups-have-type-a-actions`: the case
       `D = F(G_V × (Λ ⋉ X))`.
   - **Chain.** `S` has solvable word problem (Kuznetsov). By (P1),
     `S <= Λ <= F(T) = A(T)`, and (P2) makes this finitely presented. Its clopen
     action is type (A), so `S ∈ B_A`. BFFHZ Theorem C, (i) implies (iv), gives the
     MIF overgroup.
   - **Where it can die.** Only at (P1) or (P2). The passage from (P2) to type (A)
     uses only minimality. Neither premise mentions mixed identities or `S`.
   - **Consequence for the graph.** Question 3.4 and both conjectures now share one
     two-premise decomposition. A counterexample to Question 3.4 would refute (P1)
     or (P2). With `q34-counterexample-necessary-conditions`, such a counterexample
     `S` would be an f.p. simple group placed in no f.p. `Λ` with a minimal free SFT
     for which `A(G_V × (Λ ⋉ X))` is finitely presented.
10. **Question 3.2 as a route, and a structural obstruction to it (2026-09-17,
   lane `c-mif`).**
   - **The route.** `q34-from-bffhz-q32-for-fp-simple-groups` makes the implication
     of Attempt 1 an explicit route. Its only open prerequisite is the published
     Question 3.2 (`bffhz-q32-for-fp-simple-groups`), used at `n = 2`: the image of
     `Aut_S(S * F_2)` on `S^2` is a type (A) actor containing `S`.
   - **The obstruction.** `bffhz-q32-forces-finitely-based-mixed-identities`
     (ESTABLISHED, not independently reviewed) shows the following. If that image is
     finitely presented at rank `n`, finitely many normal generators of the kernel
     yield a finite set `W` of mixed identities. Every overgroup `M ⊇ S` satisfying
     `W` then satisfies all of `J_1(S), ..., J_(n-1)(S)`. Equivalently, those sets are
     normal closures of the substitution instances of `W`. This implies, and so
     strengthens, the recursiveness condition of `a2-kernel-removal-forces-recursive-kernel`.
   - **What would kill the route.** An infinite finitely presented simple group whose
     `J_1` is not finitely based over overgroups
     (`fp-simple-group-with-non-finitely-based-mixed-identities`, OPEN). It refutes
     Question 3.2 at every rank, but it is not a counterexample to this question.
     Thompson's `T` is the first test case, and its decidable mixed identities do not
     settle it.
   - **Not shown.** The converse, that a finite basis gives finite presentation, is
     not claimed. The free-group analogue recorded there shows that kernels of such
     actions need not be normally generated by transvections.
