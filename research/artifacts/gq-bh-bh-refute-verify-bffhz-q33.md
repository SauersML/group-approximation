# Adversarial check: BFFHZ Question 3.3 answered negatively for Thompson's `T` (bh-refute, 2026-09-18)

Rotation item 7 (e2dcc1b68). Nodes checked:
- `thompson-t-mixed-identities-are-not-finitely-normally-generated`, with its proof;
- the descent part of `bffhz-q33-is-normal-finite-generation-of-mixed-identities`;
- the form of the three-arc word from `homeo-circle-three-arc-commutator-word-is-mixed-identity`.

Verdict: **PASS**. No gap was found.

## Part 1 (small supports satisfy every mixed identity)

- **Choice of `U`.** For `u ∉ E` and a small cone `U ∋ u`, every constant-product `π ∈ Π` either moves `U` off
  itself or is the identity on `U`. This is continuity plus the definition of `E`: points fixed by `π` without
  `π` being locally trivial there.
- **Inactive letters.** An `x`-letter applied to a point outside `U` acts trivially, because `P` is supported in
  `U`. So between consecutive active letters the point moves by some `π ∈ Π` taking `U` into `U`, hence by the
  identity.
- **Activity is uniform.** Activity and the entry position are the same for all points of `U`. Induct along the
  `x`-positions: the point at the next position is `π'(y)`, and it lies in `U` iff `π'|_U = id`.
- **Collapse to one power.** So `w(P) = π_1 P^{s(j)} π_0` on the points entering at `j`. Also `π_1π_0 = w(1) = id` on
  them, since the omitted middle products act as the identity along the `P = 1` trajectory.
- **Conclusion.** Take an infinite-order `t ∈ T` supported in `U` (a copy of `F` in a dyadic arc). Then
  `w(t) = 1` forces `t^{s(j)} = id` on `U`, so `s(j) = 0`, and `w(P) = 1` for every `P` supported in `U`.
  **Correct.**

## Part 2 (the three-arc word fails in `V` at every scale)

- **Outer constants.** `w_U = [[s_12, s_21], s_33]` with `s_ij = [a_i, x a_j x^{-1}]`. Its reduced form has
  outermost constants that are products of the `a_k^{±1}`: leftmost `a_1`, rightmost `a_3^{-1}`. So *every*
  constant, including `g_0` and `g_m`, is supported in `U`, and a trajectory started in `U` never leaves it. This
  point is used implicitly on the node. I checked it.
- **Generic trajectory.** Each `x^{±1}` goes to a fresh point of `Q ∩ U`. Each fresh point is chosen in
  `supp(g_i) ∩ U`, and its image avoids all used points. So the rule is a finite partial injection. There are no
  domain or range clashes, since the word is reduced and all points are fresh.
- **Extension lemma.** Points of one tail class have common tails. Lengthening prefixes separates the cones,
  and matching the two complements inside `U` gives `P ∈ V` supported in `U`. **Correct.**

## Part 3 and descent

- **Every rank-1 finite set fails.** Given a finite `W ⊆ J_1(T)`, pick `u` off the finite union of exceptional
  sets and one cone `U` good for all of `W`. The map `T*Z → V`, `x ↦ P`, kills `⟨⟨W⟩⟩` but not `w_U`.
- **Descent.** The retraction `T*F_k → T*F_j` (extra variables `↦ 1`) maps `J_k` onto `J_j`, since `J_j ⊆ J_k` and it
  is the identity there. So finite normal generation at rank `k` gives it at rank `j`.
- **The question.** Since `T*F_n` is finitely presented, the quotient is finitely presented iff `J_n(T)` is finitely
  normally generated, which is BFFHZ's own "That is" gloss. The answer is negative at every rank, and `T` is
  finitely presented and simple.

## Attacks tried (all failed)

- **Points of `C` with two binary expansions, or ends of fixed arcs.** These are finitely many, and they sit in `E`.
- **The trajectory leaving `U` through `g_0`/`g_m`.** Excluded by the reduced form, as above.
- **Hidden simplicity or MIF use.** None is used, and the node records that the argument also works for `F`.

## Lesson for general BH

BFFHZ's Theorem-E machinery needs MIF hosts, and this shows the gap is structural. A non-MIF finitely
presented simple group acting on a space has *local* mixed identities (near generic points they reduce to
`P^0`). Any overgroup acting on the same space and breaking cyclic or linear order at every scale then makes
these identities infinitely based. So non-MIF hosts such as `T` cannot be fed to relative-automorphism
constructions through a finitely presented `E(G)`. The usable finitely presented simple hosts for
Theorem-E-type permanence are exactly the MIF ones, and those are the highly transitive or twisted
Brin–Thompson-type ones.
