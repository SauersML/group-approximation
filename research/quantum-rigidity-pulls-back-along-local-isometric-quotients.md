---
rg: 2
id: quantum-rigidity-pulls-back-along-local-isometric-quotients
kind: claim
title: If a quotient G' → G is injective on D-balls, a G-subshift is D-quantum rigid whenever its pullback to G' is; so rigidity is certified at finite stages of a marked-group limit, while exactness is not, and (RA′) needs a global argument
distinct_from:
  quantum-rigid-minimal-topfree-subshift-actions-are-amenable: that poses (RA′); this shows that the rigidity side of (RA′) is local, being inherited from any group with the same large balls, so a proof must use minimality or topological freeness over the group itself.
  roller-compactifications-of-cube-complexes-are-quantum-rigid: that proves rigidity over cubulated groups; this transfers such certificates to limit groups (Osajda's non-exact group is a limit of cubulated hyperbolic groups) and records why the Roller certificates themselves do not descend.
---

**ESTABLISHED** (lane proof, elementary; bh-star-b, 2026-09-18; not reviewed): the Lemma and part 1.
Parts 2 and 3 are partial, with their status stated.

## Setting

- `π : G' → G` is a surjection of finitely generated groups with corresponding generating sets, and
  `K = ker π`.
- `π` restricted to every ball `B_ρ` of `Cay(G')` is an isometry onto a ball of `Cay(G)`. Take
  `ρ >= 2D`.
- For a subshift `X ⊆ A^G`, the *pullback* `π^*X = {x ∘ π}` is a closed, `G'`-invariant subshift of
  `K`-invariant configurations.

## Lemma (pullback)

If `π^*X` is contained in a `D`-quantum rigid `G'`-subshift, then `X` is `D`-quantum rigid, over the
same field.

*Proof.* Since balls are isometric, `L_D(π^*X) = L_D(X)`. Given a `D`-family `E` for `X`, put
`E'(q) = E(π(q))`.
- (Q1) holds.
- (Q2) holds, because `d(q, q') <= 2D` implies `d(πq, πq') <= 2D`.
- (Q3) holds, because a `D`-pattern at `q` is illegal for `π^*X` iff its image is illegal for `X`.

So `E'` is a `D`-family for `π^*X`, and hence, by monotonicity, for the rigid overshift. So `E'`
commutes. Since `π` is onto, `E` commutes. ∎

## Consequences

1. **Rigidity is local; exactness is not.**
   - Let `G = lim G_i` be a marked-group limit in which balls stabilize, for example Osajda's residually
     finite non-exact group. Its stages `G_i` are cubulated hyperbolic groups, which are exact
     (`research/artifacts/exactness-boone-higman-separator-2026-09-17.md`, l.396; recalled).
   - Then every `D`-rigidity certificate for a `G`-subshift can be taken over a finite stage `G_i`,
     that is, over an **exact** group.
   - So no argument that uses only the local rigidity data (difference sets, clouds, caps at bounded
     scale) can prove (RA′). A proof must use a global property over `G` itself: minimality, topological
     freeness, or the cap coherence (CC) of `rigid-subshift-amenability-from-coherent-variation-caps`,
     which is global.
   - Conversely, a counterexample may be certified at a finite stage.
2. **Why the Roller certificates at finite stages do not descend (partial).**
   - A `G`-subshift `X` with `π_i^*X` inside the Roller subshift `R_i` of `G_i`
     (`roller-compactifications-of-cube-complexes-are-quantum-rigid`) is `D_i`-rigid once balls agree
     at scale `D_i`, and Osajda's fast-growing girth gives this.
   - But `π_i^*X` consists of `K_i`-invariant points of `R_i`. `K_i` is an infinite normal subgroup of
     the non-elementary hyperbolic group `G_i`, and such subgroups are expected to fix no Roller point.
     The reason: a fixed point would make `K_i` virtually cyclic, through the stabilizer of its image
     in the Gromov boundary. This is **not proved** here.
   - If so, only the empty `G`-subshift is certified this way. Rigid `G`-subshifts of wall type must
     then be certified by the walls of `G` itself, and those are not uniformly coarsely connected
     (part 4 of the cube node).
3. **Minimal subsets of the wall boundary of `G`.**
   - *The kill.* Let `M` be a minimal subset of the Roller boundary of `G` coded over `G`. Suppose some
     `x ∈ M` and some wall `V` whose edges are not `2D`-connected have `x ⊕ V ∈ M`. Then `M` is not
     `D`-rigid: Lemma 1′ of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere` applies to
     `x` and `x ⊕ V`. The two far flippable walls test of `45b0b68950` is the same mechanism.
   - *The escape.* If no point of `M` has a minimal chosen halfspace (true for regular points in the
     finite-dimensional theory, and for the ends of trees), no single-wall flip exists. The question is
     then higher-order: independent wall pieces.
   - **Not decided here.**

## What decides (RA′) at Osajda's input, as of this node

One of the following must happen:
- **(a)** A rigid `G_i`-subshift with a nonempty `K_i`-invariant part whose `G`-action has a minimal,
  topologically free subset. That would be a counterexample, certified at a finite stage.
- **(b)** A proof that minimality over `G` forces cap coherence (CC). That is a global argument, and it
  proves (RA′).

The cheapest test of (a): rigid `G_i`-subshifts whose points are invariant under large normal
subgroups, such as coset shifts `A^(G_i/Δ)` with `K_i ≤ Δ`. These descend to Cornulier-type coset
shifts over `G`, which are non-minimal when (IS) holds.

## Lesson for general BH

Quantum rigidity at scale `D` is a property of `D`-balls, so it is inherited from any group with the
same large balls. Exactness is not local: Osajda's group is a limit of exact groups. So (RA′) can only
be true for a global reason, namely minimality or topological freeness over the group itself.

That shifts the burden:
- **bh-ra-proof** must use minimality, for example through cap coherence;
- **bh-ra-counter** may certify rigidity at a finite stage, and must then find enough `K_i`-invariant
  rigid points.
