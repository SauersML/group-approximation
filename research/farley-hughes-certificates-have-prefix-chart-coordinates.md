---
rg: 2
id: farley-hughes-certificates-have-prefix-chart-coordinates
kind: claim
title: Every Farley–Hughes finiteness certificate (finitely many domain types, an expansion scheme that is 0-connected with every E(b) finite, as in FH Thm 8.2 and Prop 8.10) has finite chart coordinates in which every element of Γ_S is a prefix chart swap followed by a structure-group element and the structure groups act by finite tables; so twisted connectors disappear after recoordinatization, seed orbits are evaluable in time 2^O(n) whatever the structure groups are, the word problem of Γ_S is exponential over those of the structure groups, and the hard-seed form of gate 1 via Farley–Hughes is dead for every certificate, not only in tree coordinates
distinct_from:
  generation-axiom-closes-the-rover-door-in-tree-coordinates: that closes door (b) assuming tree coordinates with prefix connectors and uses (S5) with König; this removes the tree-coordinate and prefix-connector hypotheses, using instead the finiteness and 0-connectivity of the expansion scheme, which FH's finiteness theorems require.
  generation-axiom-rover-door-review: that referee review leaves twisted connectors, i.e. certificates without coherent coordinates, open; this shows every certificate FH's theorems can use has coherent chart coordinates with prefix connectors.
  finite-type-farley-hughes-groups-are-exponentially-capped: that caps certificates whose maximal structure groups are finite or finite-state; this caps seed orbits for every FH certificate, with arbitrary (even hard) structure groups.
  rover-nekrashevych-engines-cap-orbit-evaluation-exponentially: that caps restriction-closed self-similar structures; this needs no restriction closure and no self-similarity hypothesis, and derives the self-similar tables from the expansion scheme.
  finitary-permutations-force-singleton-domains: that shows seed orbit points are singleton domains; this is used as an input, to give seed orbit points finite chart addresses.
  fp-self-similar-groups-with-arbitrarily-hard-word-problem: that is the word-problem branch as a target; this shows it is the only hardness channel an FH certificate has, and states the exact requirements on the structure group.
---

**ESTABLISHED (lane bh-gate1-abstract, 2026-09-19; lane proof, not independently reviewed; referee requested).**
Items 1–3 and 5 are proved below; item 4, the complexity accounting, is a proof sketch with an explicit recursion.
No priority is claimed: all machinery is Farley–Hughes's. Read at source, arXiv:2010.08035v1:
Def. 3.12, Conv. 3.9, Cor. 3.8, Prop. 3.24, Def. 4.2, Def. 4.7, Def. 4.10, Def. 4.12, Def. 4.18, Prop. 4.20,
Prop. 4.22, Def. 4.23, Prop. 4.24, Lemma 4.25, Cor. 4.26, Def. 6.1, Def. 6.6, Thm 8.2, Prop. 8.10.

## The hypotheses, verbatim

- **Thm 8.2.** "Let 𝕊 be an S-structure with finitely many domain types, such that the group 𝕊(D,D) has type F∞
  for each D ∈ 𝒟⁺. Let ℰ be an expansion scheme such that (1) ℰ is n-connected for all n; (2) ℰ is rich in
  contractions; (3) each set ℰ(b) (b ∈ ℬ) is finite. The group Γ_S has type F∞."
- **Prop. 8.10.** "Let 𝕊 be an S-structure with finitely many domain types, such that the group 𝕊(D,D) has type
  F_n for each D ∈ 𝒟⁺. Let ℰ be an (n−1)-connected expansion scheme such that (1) each set ℰ(b) (b ∈ ℬ) is
  finite, and (2) […]. The group Γ_S has type F_n."
- **Def. 6.6.** "We say that ℰ is n-connected if, for each b ∈ ℬ and each pseudovertex v satisfying {b} ⪇ v,
  lk({b}, Δ(ℰ(b))_{[{b},v]}) is (n−1)-connected."
- **Def. 6.1(3)** (Ŝ-invariance): "for each ŝ ∈ Ŝ, and each b ∈ ℬ for which ŝ·b is defined, ŝ·ℰ(b) = ℰ(ŝ·b)."

Call `(𝕊, ℙ, ℰ)` an **FH certificate** if 𝕊 has finitely many domain types and ℰ is a 0-connected expansion
scheme with every `ℰ(b)` finite. Every application of Thm 8.2, or of Prop. 8.10 with `n ≥ 1`, supplies one.
Here 0-connected means the link above is (−1)-connected, i.e. **nonempty**:

> **(E0)** for every `b` and every pseudovertex `v ⪈ {b}` there is `w ∈ ℰ(b)` with `{b} ⪇ w ≤ v`.

## Notation

- **Types and representatives.** Types are 𝕊-types (Def. 4.7). For each type `τ` fix a representative domain
  `R_τ`, and put `b_τ = [id, R_τ]` and `H_τ = 𝕊(R_τ, R_τ)`, a group by (S1)–(S4). For every nonempty domain `E`
  fix `κ_E ∈ 𝕊(R_(t(E)), E)`, with `κ_(R_τ) = id`.
- **Normal form of classes.** `[f, E] = [f κ_E, R_(t(E))]`: take `h = κ_E^(-1) ∈ 𝕊(E, R)` in Def. 4.10, using (S3).
  Also `[g, R_ρ] = [g', R_ρ']` iff `ρ = ρ'` and `g = g' h` for some `h ∈ H_ρ`, since 𝕊(R_ρ, R_ρ') ≠ ∅ forces
  equal types.
- **Charts.** For each type `τ`, each `w ∈ ℰ(b_τ)` with `w ≠ {b_τ}` (a *chart system at `τ`*), and each class
  of `w`, choose `c : R_ρ → R_τ` with that class equal to `[c, R_ρ]`. These `c` are the **charts**. Each is a
  locally determined partial bijection, and the images of the charts of one system partition `R_τ`.
  - The chart set `C` is **finite**, because there are finitely many types, each `ℰ(b_τ)` is finite, and each
    pseudovertex is finite.
- **Chart words.** A chart word is a composable product `ω = c_1 c_2 ⋯ c_m` with `c_i : R_(ρ_i) → R_(ρ_(i−1))`.
  It is a partial bijection `R_(ρ_m) → R_(ρ_0)`; the empty word is `id`.

## Theorem

Let `(𝕊, ℙ, ℰ)` be an FH certificate.

1. **Chart lemma.** For every type `σ` and every pseudovertex `q ≥ {b_σ}`, every class of `q` equals `[ω, R_ρ]`
   for some chart word `ω` of length `≤ |q| − 1`.
2. **Prefix connectors.** Fix a partition of `X` into domains `M_1, …, M_r` (Conv. 3.9) and put `κ_i = κ_(M_i)`.
   For every `γ ∈ Γ_S` there are finitely many triples `(i, ω', ρ)` whose sets `κ_i ω'(R_ρ)` partition `X`, such
   that on each of them
   `γ = (κ_j ω) ∘ h ∘ (κ_i ω')^(-1)` for some index `j`, chart word `ω` and `h ∈ H_ρ`.
   So in chart coordinates every element of Γ_S is a **prefix chart swap followed by a structure-group element**:
   no twisted connectors.
3. **Finite tables.** Each `h ∈ H_τ` permutes the finite set `ℰ(b_τ)`. For each chart `c` of a system `w` there
   is a chart `c'` of the system `h·w` and an element `k ∈ H_ρ` with `h c = c' k`. For a finite generating set
   `A_τ` of `H_τ`, fix these `k` as `A_ρ`-words. Then `H` acts on chart words by a finite table: a finite wreath
   recursion over the finite chart graph.
   - For each pair of chart systems `w, w''` at `τ` there are finitely many **transition rules**
     `c ω = c'' ω'' h`, with `h ∈ H`, relating the two systems on a common refinement.
4. **Caps (sketch).** Let `Γ ≤ Γ_S` be finitely generated, with each generator given in the form of item 2.
   - **(a) Orbits.** For a point `y` such that `{y}` is a domain, computing `γ(y)` from a word `γ` of length
     `n`, and deciding `γ(y) ∈ U` for a fixed finite union of domains `U`, takes time `2^(O(n))`, with constants
     depending only on the certificate and the generators. **This never consults a word problem of any `H_τ`.**
   - **(b) Word problem.** `WP(Γ)` reduces in time `2^(O(n))` to the word problems of the `H_τ`, with queries of
     length `2^(O(n))`.
5. **Structure groups.** If the domains separate points, each `H_τ` acts faithfully on a rooted tree of bounded
   degree, through the recursion of item 3. So `H_τ` is residually finite and its finite quotients have
   composition factors of bounded order.

## Proof

**1. Chart lemma.** Induction on `|q|`.
- **Base.** If `|q| = 1`, then `q = {b_σ}`, since each expansion raises the rank (Remark 4.19). And
  `b_σ = [id, R_σ]` is the empty chart word.
- **Step.** Let `q ⪈ {b_σ}`. By (E0) pick `w ∈ ℰ(b_σ)` with `{b_σ} ⪇ w ≤ q`; then `|w| ≥ 2`. Write the classes of
  `w` as `[c_j, R_(ρ_j)]` with charts `c_j`.
  - **Splitting `q` along `w`.** By Prop. 4.22(1),(2) there is, for each `j`, a unique `q_j ⊆ q` with image
    `c_j(R_(ρ_j))`, and `{[c_j, R_(ρ_j)]} ≤ q_j`. The `q_j` partition `q`, so `|q_j| ≤ |q| − 1`.
  - **Pulling back.** `c_j^(-1) ∈ Ŝ` is defined on the image of `q_j`, so by Prop. 4.24(2)
    `c_j^(-1)·q_j ≥ {[c_j^(-1) c_j, R_(ρ_j)]} = {b_(ρ_j)}`, with the same rank as `q_j`.
  - **Induction.** Every class of `c_j^(-1)·q_j` is `[ω, R_ρ]` with `|ω| ≤ |q_j| − 1`. So every class of `q_j` is
    `c_j·[ω, R_ρ] = [c_j ω, R_ρ]`, of length `≤ |q| − 1`. ∎

**2. Prefix connectors.** Let `v_0 = {[id, M_i]}_i`. Then `γ·v_0 = {[γ|_(M_i), M_i]}` has the same image `X`, so
by Cor. 4.26 there is a common upper bound `u`.
- **Relative to `v_0`.** Let `u_i ⊆ u` be the part with image `M_i` (Prop. 4.22). Then
  `κ_i^(-1)·u_i ≥ {[κ_i^(-1), M_i]} = {b_(t(M_i))}`. By item 1 its classes are `[ω, R_ρ]`, so the classes of `u`
  are `[κ_i ω, R_ρ]`.
- **Relative to `γ·v_0`.** Let `u'_k ⊆ u` be the part with image `γ(M_k)`. Then
  `(γ κ_k)^(-1)·u'_k ≥ {[κ_k^(-1), M_k]} = {b_(t(M_k))}`, so the classes of `u` are also `[γ κ_k ω', R_ρ]`.
- **Equating.** Each class of `u` has both forms. By the normal form, `γ κ_k ω' = κ_i ω h` with `h ∈ H_ρ`. So on
  `κ_k ω'(R_ρ)` we get `γ = κ_i ω h (κ_k ω')^(-1)`.
- **The pieces partition `X`.** The images `κ_i ω(R_ρ)` of the classes of `u` partition `X`, and `γ` is a
  bijection, so the sets `κ_k ω'(R_ρ)` partition `X` too. ∎

**3. Finite tables.**
- **`H_τ` permutes `ℰ(b_τ)`.** For `h ∈ H_τ` we have `h·b_τ = [h, R_τ] = [id, R_τ] = b_τ`, so Def. 6.1(3) gives
  `h·ℰ(b_τ) = ℰ(b_τ)`.
- **The table entries.** For a chart `c` of `w`, `[h c, R_ρ] = h·[c, R_ρ]` is a class of `h·w ∈ ℰ(b_τ)`. So it
  equals `[c', R_ρ]` for the chosen chart `c'` of that class, and `h c = c' k` with `k ∈ H_ρ`.
- **Transition rules.** For systems `w, w''` at `τ`, take a common upper bound `u` (Cor. 4.26). Pulling back along
  the charts of `w`, as in item 2, every class of `u` is `[c ω, R]` with `c` a chart of `w`. Likewise it is
  `[c'' ω'', R]` with `c''` a chart of `w''`. Equating the two gives `c ω = c'' ω'' h`. Finitely many pairs and
  finite `u` give finitely many rules. ∎

**4. Caps (sketch; the exponent is not optimized).**
- **Addresses.** Let `{y}` be a domain. By Def. 3.12(2) there is a partition `P ∋ {y}` of `X` into domains; apply
  the argument of item 2 to `v_0` and `{[id, E]}_(E ∈ P)`.
  - Since `{y}` has no nontrivial pattern, the part of the upper bound with image `{y}` is a single class
    `[κ_i ω, R_ρ]` with `R_ρ` a singleton. So `y` has a **finite chart address** `(i, ω)`.
  - The same argument writes every domain, and so every `U`, as a finite union of sets `κ_i ω(R_ρ)`.
  - By `finitary-permutations-force-singleton-domains`, this applies to every orbit point of a seed full group.
- **Three operations.**
  - **(A) Apply an `H`-word to an address.** Go letter by letter through the table of item 3. Section words grow by
    a factor of at most `L` per level, where `L` is the maximal table-word length. On singleton types the group is
    `𝕊({y}, {y}) = {id}`, so nothing is carried past the end of the address. No word problem is solved; words are
    only rewritten.
  - **(B) Test `α ∈ κ_i ω(R_ρ)`.** Compare letters. When the chart systems at a common node differ, apply a
    transition rule. This needs to know which of the finitely many refinement pieces, of bounded length, contains
    the tail: a recursive test one level deeper. Then rewrite the prefix and push the rule's `h` into the tail
    by (A).
  - **(C) Apply a generator.** Find its piece by (B), swap the prefix (bounded), and apply its `h` by (A).
- **Cost.** Address lengths stay `≤ ℓ_0 + O(n)`, carried words have length `≤ L^ℓ`, and (B) satisfies
  `T(ℓ) ≤ B·T(ℓ−1) + 2^(O(ℓ))`. So each step costs `2^(O(ℓ))`, and `n` steps cost `2^(O(n))`. This gives (a).
- **Word problem (b).** `γ = id` iff every piece of item 2 maps onto itself and, after bringing source and target
  to the same chart word by transition rules, its `h` is `1` in `H_ρ`.

**5. Structure groups.**
- **The tree.** The domains inside `R_τ` form a rooted tree under inclusion, whose children are the maximal
  partitions (Cor. 3.20, Prop. 3.16). S-maps carry maximal partitions to maximal partitions (Prop. 3.24), so the
  number of children depends only on the type. That bounds the degree.
- **The action.** `H_τ` acts on this tree (Lemma 3.7(2), Prop. 3.24).
- **Faithfulness.** If `h(x) = x' ≠ x`, a domain containing `x` but not `x'` is moved, so the action is faithful.
- **Consequence.** The automorphism group of a rooted tree of degree `≤ d` is residually finite, and its finite
  quotients are subgroups of iterated wreath products of `S_d`. ∎

## What this settles

- **The coherent-coordinates question of 3912bc3c96 has a yes answer**, in the form the cap needs. Chart
  coordinates give prefix connectors and bounded section words: finitely many table words.
  - The `κ_N` need not be chosen maps.
  - (S5) enters only through FH's directedness, Lemma 4.25 and Cor. 4.26.
  - The real work is done by two hypotheses that every FH finiteness theorem imposes: **finiteness of `ℰ(b)`** and
    **0-connectivity**. Finiteness makes the chart set finite. 0-connectivity (E0) forces every expansion,
    including every twisted one, to pass through a chart system.
- **Twisted connectors are the same door,** as bh-ref-t0 observed (79ad158419). That door is now closed: twists
  are absorbed into the finite chart set.
  - Röver's certificate (FH Ex. 4.35, Prop. 6.24) shows how. Its nonstandard expansion is the standard split
    twisted by `a`. So `b c_0 = c_0 a` becomes a table entry with trivial section, on the chart `c_0 a` of the
    nonstandard system.
- **Abstract certificates add nothing either.** The compact ultrametric property already makes the domains a
  bounded-degree rooted forest (item 5), and chart coordinates live on it.
- **Gate 1, hard-seed form, via Farley–Hughes is dead for every certificate** that Thm 8.2 or Prop. 8.10 can use.
  By item 4(a), seed orbit evaluation costs `2^(O(n))` **even when the structure groups have hard word problems**.
  - This subsumes `finite-type-farley-hughes-groups-are-exponentially-capped`,
    `rover-nekrashevych-engines-cap-orbit-evaluation-exponentially` and
    `generation-axiom-closes-the-rover-door-in-tree-coordinates`.

## What survives

1. **The word-problem channel,** the only one left. By item 4(b), `WP(Γ_S)` can be hard only through some
   `WP(H_τ)`. For `Γ_S` to witness HARD-(A) (`type-a-actors-with-arbitrarily-hard-word-problem`), some structure
   group `H` must satisfy all of the following:
   - type `F_n` with `n ≥ 2` (Prop. 8.10), or `F_∞` (Thm 8.2);
   - residually finite with bounded composition factors, when domains separate points (item 5);
   - acts faithfully through a **finite wreath recursion** over a finite chart graph (item 3);
   - has a word problem harder than `T`.

   For such an `H`, the word problem is decidable: it is r.e. because `H` is finitely presented, and co-r.e. by
   searching for a moved vertex. Its hardness is exactly the growth of the **depth of the shallowest vertex moved
   by a nontrivial word of length `n`**. So the precise open target is:
   > A finitely presented, finitely recursive self-similar group (finite table sections, not necessarily finite
   > state) whose nontriviality depth grows faster than any given recursive function.
   - Contracting groups have logarithmic depth, so they fail.
2. **Engines outside FH's theorems.**
   - **Infinite `ℰ(b)`.** If ℰ is only 𝕊-finite (Def. 6.12), with each `ℰ(b)` infinite but `H`-cocompact, then
     the charts come in `H`-orbits, and orbit evaluation needs `H`'s action on the infinite sets `ℰ(b)`. Hardness
     can then enter only through the membership problems of the stabilizers `Stab_H(w)`, `w ∈ ℰ(b)`. That is a
     structure-group channel again.
   - **Non-FH finiteness engines.** These are untouched.

## Literature for the surviving channel (not re-read at source except as marked)

- **Type-F groups with arbitrarily hard solvable word problem exist.**
  - Collins–Miller, "The word problem in groups of cohomological dimension 2" (Groups St Andrews 1997, Bath),
    abstract read: the Boone–Britton groups are iterated HNN extensions of free groups along finitely generated
    free subgroups, with aspherical presentations, so they have type F.
  - Run on a decidable machine or semigroup of high complexity, the Boone–Britton construction gives a word
    problem at least that hard. The degree theory is Boone's and Clapham's.
  - These groups are not expected to be residually finite with bounded composition factors, so they do **not**
    fit as FH structure groups.
- **Residually finite finitely presented groups with arbitrarily complex word problem.** These are by
  Kharlampovich–Myasnikov–Sapir, "Algorithmically complex residually finite groups" (Bull. Math. Sci. 2017).
  Their finiteness beyond `F_2`, their composition factors and any self-similar recursion are unchecked. They are
  the natural test inputs for the open target above.
- **No known group meets all four requirements** of "What survives", item 1.

## Lesson for general BH

**Finite expansion schemes are finite coordinate atlases.**
- 0-connectivity pushes every expansion through one of finitely many chart systems. Every Farley–Hughes group is
  therefore a prefix-swap-plus-structure-group group in finite chart coordinates.
- Seeds are exponentially cheap in every Farley–Hughes engine.
- Hardness can live only in the word (or coset-membership) problems of the structure groups, which must be
  finitely presented, residually finite, bounded-composition-factor, finite-recursion self-similar groups.
