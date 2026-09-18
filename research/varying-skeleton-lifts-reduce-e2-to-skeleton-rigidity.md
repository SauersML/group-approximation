---
rg: 2
id: varying-skeleton-lifts-reduce-e2-to-skeleton-rigidity
kind: claim
title: For lifts whose skeleton varies along Λ_0, determination by skeleton and input is allowed and makes E2 exactly skeleton rigidity plus centrality; minimality forces the skeleton to be joined to the input, the transport no-go lifts, and the natural design is a transplant along the input's tree heights whose minimality is the height-cocycle criterion
requires:
  - e2-for-plane-lifts-is-clustered-floating-freedom
  - extension-rigidity-is-base-centrality-plus-pointwise-rigidity
  - strongly-proximal-geometries-are-disjoint-from-measured-inputs
distinct_from:
  e2-for-plane-lifts-is-clustered-floating-freedom: that treats Λ_0-constant skeletons, where minimality forces free data and transports are impossible; this treats skeletons varying along Λ_0 (option (b)), where both obstructions lift.
  busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid: that reduces rigidity of transplants along a group's own Busemann function to centrality; this asks for a transplant along a cocycle read from the INPUT, so that the skeleton is joined to the input as minimality requires.
  keyed-slots-bypass-the-phase-field-on-boundary-geometry: that recorded the height-cocycle test as no longer load-bearing for E1; Part 3 here makes it the minimality condition of option (b).
---

**Status.** Parts 1, 2 and the first item of Part 3 are ESTABLISHED (the second item was corrected on 09-18) (lane proofs,
elementary, unreviewed). Part 4 is OPEN.

**Note on option (a).** bh-free-09's warning (its board, 09-18) kills freedom localized at an
input defect only when that freedom is *bounded*, i.e. a finite modification.
- The defect freedom of `e2-for-plane-lifts-is-clustered-floating-freedom`, Section 4, is
  clustered along `Λ_0` but runs along an infinite chain in `Z^2`. That warning does not reach
  it.
- Option (a) is set aside here because (b) removes its reason to exist, not because it has
  been refuted.

**Setting.**
- `X` is an SFT over `Λ_0 x Z^2`, with:
  - a *skeleton* layer `S` (a hierarchy in each plane, **not** required to be `Λ_0`-constant);
  - plane-constant letters;
  - tables and twin rules as in 695a89096, with twin carriers matched by the skeleton's
    cross-plane correspondence, at offsets of norm `≤ D`;
  - computation data.
- `Y` (the letters) is a minimal non-SFT `Λ_0`-subshift.

## Part 1. E2 when the point is determined

**Theorem D.** Suppose:
- (i) the skeleton SFT (the `S`-projection of `X`, closed under its own rules) is `D`-quantum
  rigid;
- (ii) in every `D`-quantum family of `X`, the skeleton idempotents are central (condition (C));
- (iii) copied table wires cross, as in (P2) of the required node;
- (iv) (Det): every point of `X` is determined by its skeleton and letters.

Then `X` is `D`-quantum rigid.

*Proof.*
1. **Letters are central.** Split the space along the central skeleton projections, by (ii).
   On each summand the argument of Theorem A of `e2-for-plane-lifts-is-clustered-floating-freedom`
   applies verbatim:
   - twin carriers at matched positions are within `2D`, so their projections are equal;
   - crossing makes the copied letters of all planes commute;
   - every edge lies in a commutative block algebra that contains the letters.
   So letters are central too.
2. **The base commutes.** Take base = skeleton plus letters. Its marginals commute:
   - skeleton idempotents commute with one another by (i);
   - letter and skeleton idempotents commute by step 1 and (ii).
   So condition (C_D) of `extension-rigidity-is-base-centrality-plus-pointwise-rigidity` holds.
3. **Localize.** By (iv), the fibre over each frozen base point is a single filling. So every
   relative family acts by `0/1` scalars and commutes.
4. **Conclude.** Item 3 of that node gives rigidity. ∎

## Part 2. Minimality forces the skeleton to be joined to the input

**Proposition E.** If `X` is minimal and satisfies (Det), then the skeleton system `T` (the
image of `X` in the skeleton layer) and `Y` are **not disjoint**: `T x Y` is not minimal.

*Proof.* Theorem 3 of `strongly-proximal-geometries-are-disjoint-from-measured-inputs`, in its
general form ("`(τ,φ)` injective and `T x Y` minimal ⇒ `Y` is an SFT"), with `τ` = the skeleton
map. ∎

**Consequences.**
- A `Λ_0`-constant skeleton is automatically disjoint from a plane-constant input: orbits are
  products. So (Det) is impossible there. This recovers the forced freedom of the constant case.
- In option (b), the skeleton's variation along `Λ_0` must *depend on the input*.
- The local form of such a dependence is a **transplant**: a cross-plane skeleton rule
  "skeleton at `(λs, z + c)` = skeleton at `(λ, z)`", where the offset `c = c(s, y|λF)` is a
  bounded integer vector read from the letters.
- Consistency around relators makes `c` a continuous `Z^2`-valued cocycle over `Y`.

## Part 3. The transport no-go lifts, and what minimality becomes

- **Theorem C of the constant case does not apply.**
  - Its contradiction came from the parallel sections `g_k`, which are `Λ_0`-invariant, together
    with a `Λ_0`-invariant skeleton.
  - With a transplant skeleton, `(skeleton, g)` is not `Λ_0`-invariant, so Theorem 3(iii) is
    not triggered.
- **Floating data is a plane-global section field (CORRECTED 2026-09-18).** An earlier
  version claimed that minimality forces a unique section. That argument was wrong and is
  withdrawn.
  - The windowing argument of Theorem C shows that, at each level `k` and skeleton position
    `z`, the floating identities of all planes form one parallel section `s_k(z)`. That argument
    uses slots at transplant-matched positions.
  - But `s_k(z)` depends on the position `z`. So it is not a global invariant datum, and its
    level sets are not closed invariant sets.
  - What is true instead: adjoin the section field `(s_k(z))` to the skeleton layer. It is
    read continuously and is plane-global. Relative to this *enlarged skeleton* and the
    letters, (Det) holds.
  - So Theorem D applies, with (i) and (ii) asked of the enlarged skeleton.
  - The freedom that remains is the choice of sections at degenerate chains. It is shared by
    all planes, so it creates no separable pair across planes.
    (Det) holds.
- **Minimality becomes a cocycle condition (sketch).** Write the skeleton as an almost 1-1
  extension of the Durand–Romashchenko odometer `O`.
  - The pair (skeleton phase at plane `1`, `y`) then lives in the skew product
    `Y x_c O`, with `λ·(p, y) = (p + c(λ, y), λy)`.
  - Up to the fault fibres, `X` is this skew product. So minimality of `X` comes down to
    minimality of `Y x_c O`.
  - For compact abelian `O`, that is the character criterion (PF1): for no nontrivial
    character `χ` is `χ∘c` a continuous coboundary into the circle.
  - The fault-fibre part is the usual DR bookkeeping (not re-derived).

## Part 4. The natural design for option (b) (OPEN)

Take `Λ_0 = A' = (Λ_1 x Z) * Z` and the tree-glued input `Y_1` of
`free-products-with-z-inherit-m2-from-decidable-free-subshifts`.

**The design.** Transplant a crossing-wire Durand–Romashchenko–Shen skeleton along the
**Busemann height cocycle** of `Y_1`'s Bass–Serre pointer data: `c(s, y) = (h(λs) − h(λ), 0)`.

**Why it fits.**
- It is a genuine `y`-dependent cocycle, with values in `{−1,0,1}` on generators.
- The minimally almost periodic kill does not apply: it concerns homomorphisms and factors,
  and this is neither.
- (PF1) for `c` is the test recorded in `keyed-slots-bypass-the-phase-field-on-boundary-geometry`,
  Part 2. There the Sturmian label factor alone cannot trivialize `c mod 2^k`; the full
  criterion is open.

**What is left.**
- **(1) (PF1) for the height cocycle over all of `Y_1`.** This is minimality.
- **(2) Rigidity of the transplanted skeleton.** This is hypothesis (i).
  - Busemann-transplant tools apply: `busemann-transplants-of-rigid-z2-sfts-are-quantum-rigid`
    reduces it to (C), and `tree-product-transplants-pass-the-separability-test` shows that
    skeleton modifications contain surjective slabs.
  - Here the tree is the input's, not the group's.
- **(3) Centrality (C) of the skeleton.** This is hypothesis (ii), via bh-g2-fixedpoint-b's
  downhill lemma (df763a98d): offsets read off the pointer flow, with the height as potential.
- **(4) Layout.** Crossing of copied table wires, hypothesis (iii), is a construction
  obligation.

## Lesson for general BH

Once the skeleton varies along the acting group, E2 is no longer about floating data at all.
- Minimality forces the skeleton to be *joined to the input* (Proposition E).
- The only local way to do that is a transplant along an input cocycle.
- The floating data is then a plane-global section field, which the skeleton absorbs.
- So E2 is exactly skeleton rigidity plus centrality (Theorem D).

The phase cocycle retired from E1 comes back as the minimality condition of E2. The input's
own Bass–Serre heights, which the tree gluing already supplies, are the natural candidate.
