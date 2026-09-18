---
rg: 2
id: bounded-propagation-operads-have-capped-word-problems
kind: claim
title: Operad groups with finite transformations, a finite spine and bounded propagation of moves have word problems in uniformly doubly exponential time, so no family of such hosts is universal; a finite-spine host with finite transformations escapes the complexity cap only through an unbounded propagation alphabet
requires:
  - complexity-bounded-host-classes-are-not-universal
  - symmetric-ore-operads-containing-their-carrier-are-full-groups
  - thumann-operad-groups-need-only-f-infinity-transformations
distinct_from:
  rational-homeomorphism-subgroups-have-exponential-wp: that bounds the word problem of groups of finite transducers on a full shift; this bounds the word problem of abstract operad groups from their finite operad data, with no coding of the boundary as a shift.
  complexity-bounded-host-classes-are-not-universal: that turns any uniform word-problem bound into non-universality; this supplies the bound for one host class, the finite-state operads.
  symmetric-ore-operads-containing-their-carrier-are-full-groups: that shows an operad host is the full group of its carrier and asks whether finite spines cap its word problem; this answers that question under bounded propagation and isolates the remaining case.
---

**ESTABLISHED** under the hypotheses below (lane bh-typeA-universal, 2026-09-18). The proof is
elementary and given below; not independently reviewed. No priority claimed. It answers, in the
bounded-propagation case, the question in
`symmetric-ore-operads-containing-their-carrier-are-full-groups`.

## Setting

`𝒪` is a planar or symmetric operad with transformations in Thumann's sense, as in
`thumann-operad-groups-need-only-f-infinity-transformations`. Assume:
- finitely many colors and finitely many generators (very elementary operations);
- **finite** transformation groupoid `ℐ`;
- the cancellative calculus of fractions (Ore).

Degree-1 operations are exactly the transformations, so every other operation has degree at least
2.

Write `x ≥ t` when `x = t∘ψ` for some `ψ`.

- **(FS), finite spine.** For each pair of generators `s, s'` with the same output, the minimal
  common multiples of `s` and `s'` lie in finitely many classes modulo leaf transformations.
- **(BP), bounded propagation.** There is a finite set `𝒫` of operations with the following
  properties:
  - it contains the generators and the transformations, and is closed under composing with
    transformations on either side;
  - for every `t ∈ 𝒫` and every generator `s` with the same output, some `p_1, …, p_k ∈ 𝒫`
    satisfy `s∘(p_1, …, p_k) ≥ t`.

  So a move passes through a split as one element of `𝒫` on each piece. Put
  `D_𝒫 = max deg 𝒫`.

## Statement

1. **Presentation.** Words are trees of generators with transformation labels on the leaves. The
   category of operations is presented on these words by finitely many relations:
   - the relations of `ℐ`;
   - the pull-through relations `α∘s = s'∘(β_1, …, β_k)`;
   - one square `s∘u = s'∘u'` for each spine class.

   Equality of two words of degree `N` is decidable in time `2^{O(N)}`.
2. **Linear refinement growth.** For every operation `b` and every operation `c` whose word has
   `r` generators, `b` and `c` have a common multiple of degree at most `D_𝒫^r · deg b`, and it
   can be computed.
3. **Word problem.** For every object `X`, every finitely generated subgroup of `π_1(𝒪, X)` has
   word problem decidable in time `2^{2^{O(n)}}`, where the constants depend on `𝒪` and on the
   generators. This covers `π_1(𝒪, X)` itself whenever it is finitely generated, for instance
   under Thumann's finite type.
4. **Cap.**
   - By `complexity-bounded-host-classes-are-not-universal` with `T(l) = 2^{2^l}`, some
     two-generated group with solvable word problem embeds in no group of any operad in this
     class.
   - By `symmetric-ore-operads-containing-their-carrier-are-full-groups`, this includes every
     full group `[[Λ]]` presented by such an operad.
   - So a universal operadic route, through transformations or through dynamics, cannot use finite
     transformations, finite spine and bounded propagation together.

## Proof

1. **Presentation.**
   - **Normal words.** Pull-through relations move every transformation to the leaves, so every
     operation has a word of the stated form.
   - **Induction on `deg μ`.** Let `w` and `w'` be words for the same operation `μ`.
     - If `deg μ = 1`, both are transformations and the relations of `ℐ` connect them.
     - Otherwise `w = s∘(w_1, …, w_k)` and `w' = s'∘(w'_1, …)` for generators `s, s'`. So `μ` is
       a common multiple of `s` and `s'`.
   - **A minimal common multiple.** Among the common multiples of `s, s'` that left-divide `μ`,
     choose `m` of least degree.
     - It is minimal among all common multiples, since a proper divisor that is a common multiple
       would also divide `μ`.
     - By (FS), `m = m_j∘α` for a listed class `m_j`, with square `m_j = s∘u = s'∘u'`, and
       `μ = m∘ν`.
   - **Closing the induction.**
     - Left cancellation gives `(w_i) = (u∘α∘ν)` componentwise. Each component has degree less
       than `deg μ`, since `k ≥ 2` and every component has degree at least 1.
     - By induction, `w ~ s∘(u∘α∘ν) ~ s'∘(u'∘α∘ν) ~ w'`, where the middle step is the square.
   - **The time bound.**
     - Relations preserve degree.
     - There are at most `c^N` normal words of degree `N`, with `c` depending on the numbers of
       generators, the arities and `|ℐ|`.
     - Equality is connectivity in this finite graph, so it takes time `2^{O(N)}`.
2. **Propagation lemma.** For `t ∈ 𝒫` and any `b` with the output of `t`, there are `p_ℓ ∈ 𝒫`,
   one for each leaf `ℓ` of `b`, with `b∘(p_ℓ)_ℓ ≥ t`. Induction on `deg b`:
   - **`deg b = 1`.** `b = α` is a transformation. Take `p = α^{-1}∘t ∈ 𝒫`.
   - **Otherwise.** `b = s∘(b_1, …, b_k)`. (BP) gives `s∘(p_1, …, p_k) ≥ t`, and induction gives
     `b_i∘(p_ℓ)_{ℓ ∈ b_i} ≥ p_i`. Composition preserves `≥`, so
     `b∘(p_ℓ) = s∘(b_i∘(p_ℓ)) ≥ s∘(p_i) ≥ t`.
   - **Degree.** `deg(b∘(p_ℓ)) ≤ D_𝒫 · deg b`.

   **Growth.** Induct on the number `r` of generators in `c`. Write `c = t∘(c_1, …, c_l)` with `t`
   a generator.
   - The lemma gives `b' = b∘(p_ℓ) = t∘(z_1, …, z_l)`, with `deg b' ≤ D_𝒫 deg b`.
   - Induction gives `y_j ≥ z_j, c_j` with `deg y_j ≤ D_𝒫^{r_j} deg z_j`, where `r_j < r` is the
     number of generators in `c_j`.
   - Then `t∘(y_j)_j ≥ b' ≥ b` and `t∘(y_j)_j ≥ c`, of degree at most `D_𝒫^r deg b`.
   - The choices in (BP) are finite data, so everything is computable.
3. **Word problem.**
   - **Generators.** Fix a finite symmetric set of fractions `a_i∘b_i^{-1}` whose words have at
     most `r` generators, and consider the subgroup it generates.
   - **Multiplication.** Multiplying the current fraction `a∘b^{-1}` by `c∘d^{-1}` uses a common
     multiple `b∘ψ = c∘ψ'` from 2. This gives `(a∘ψ)∘(d∘ψ')^{-1}`, whose degree has grown by a
     factor of at most `C = D_𝒫^r`.
   - **Size.** After `n` letters the fraction has degree `N ≤ C^n · deg X`.
   - **Triviality.** In a cancellative Ore category, `a∘b^{-1} = 1` iff `a = b`. By 1 this test
     takes time `2^{O(N)} = 2^{2^{O(n)}}`. Building the words costs less.
4. **Cap.** The bound has the form `C_S·T(C_S·l) + C_S·l + C_S` with `T(l) = 2^{2^l}` required by
   `complexity-bounded-host-classes-are-not-universal`. For finitely generated subgroups the same
   bound holds after a linear change of word length. ∎

## Instances

- **(BP) with `𝒫` the generators and identities.** This holds when two splits always refine by
  one split on each piece:
  - Higman–Thompson groups (one split per color);
  - Brin–Thompson `nV`: `s_j∘(s_i, s_i) = s_i∘(s_j, s_j)` up to a permutation;
  - the Stein interval operad with splits into 2 and 3 equal parts:
    `s_2∘(s_3, s_3) = s_3∘(s_2, s_2, s_2)`, both being sixths.

  (FS) is immediate for the first two. For the Stein operad it was not checked here.
- **The edge-split operad violates (BP) for `𝒫` = generators.**
  - Let `s` split the edge `AB` of `cone(A, B, C)` at `M = A + B`, and let `t` split `AC` at
    `N = A + C`.
  - The cut of `t` runs from `B` through `P = A + B + C`.
  - On the piece `cone(A, M, C)` of `s` it is the segment `NP`, which joins two edge midpoints.
  - None of the three edge splits of that piece has `NP` as an edge, so the cut needs at least two
    splits there.
  - In deeper pieces the propagated cut is a rational plane in the piece's frame, and its
    coefficients grow.
  - So no finite `𝒫` is expected. This is not proved.
  - The word problem of `𝒯_m` is presumably capped anyway, by integer linear algebra on
    polyhedral pieces (not proved here).
  - Where it lies, the complexity comes from the arithmetic of the carrier `GL_{m+1}(Z)`, not from
    the operad.

## What remains open

- **Finite spine without bounded propagation.** Can such an operad have a word problem outside
  every fixed recursive class? The proof of 2 fails exactly when passing a move through a split
  can require several moves on one piece. Then the propagation multiplies along depth, and the
  degree of common multiples is controlled only by Ore's existence statement.
- **A construction.** A finite-spine operad whose propagated cuts simulate a machine, as rational
  planes do Diophantine approximation in the edge-split operad, would escape this cap. Such an
  operad is the operadic form of a ¬CAP seed.

## Lesson for general BH

**Finite-state propagation caps the host.** An operad host with finite transformations and a
finite spine is capped by the size of its *propagation alphabet*: the set of shapes a move takes
after being pushed through a split. A finite alphabet makes the operad a finite-state machine on
addresses. Its groups then have uniformly doubly exponential word problems, and no family of them
is universal.

This is the operadic counterpart of CAP for rigid seeds: finite-state seeds are capped. The only
escape is an unbounded alphabet generated by the carrier's action on cuts, as for the rational
planes of the edge-split operad. There the host's complexity is the carrier's arithmetic.

So a universal operadic route needs one of two things:
- a carrier whose action on cut shapes computes the input's word problem, which is the carrier
  principle again;
- infinite transformations with unbounded refinement, which is the transformation channel of
  `bounded-refinement-operads-reduce-to-their-carriers`.
