---
rg: 2
id: levelled-actions-make-finitary-extensions-not-fp2
kind: claim
title: If some virtual character of G vanishes on the point stabilizers of one orbit of X, then FSym(X) x| G and Alt_fin(X) x| G are not FP_2 over Q; so in every finitely presented split finitary overgroup, point stabilizers surject rationally onto the abelianization of every finite-index subgroup
distinct_from:
  lampshuffler-groups-are-not-fp2-over-q: that is the free-action case, where every character vanishes on the trivial stabilizers; this replaces freeness by a level function, so it covers every non-free action whose stabilizers of one orbit lie in the kernel of a virtual character, and it turns the theorem into a necessary condition on stabilizers.
  fp-finitary-permutation-overgroups-are-type-a-actors: that says a finitely presented overgroup of Alt_fin(X) is a type (A) actor; this says which split overgroups can be finitely presented at all.
  abels-quotient-product-form-model-with-one-singular-point: that proposes Alt_fin(Omega) x| A_p/C as a route to Boone--Higman for Hall's and Abels' quotients; this shows that candidate passes the new necessary condition, because its point stabilizers contain the torus.
artifacts:
  - research/artifacts/zp-lampshuffler-not-fp2-2026-09-13.md
---

**ESTABLISHED** (lane `bh-solvable`, lane proof: the proof of
`lampshuffler-groups-are-not-fp2-over-q` with one step changed; not independently reviewed;
no priority claimed).

## Statement

Let `G` be a group acting on a set `X`. Call a homomorphism `φ: G → Z` onto, and an orbit `O`, a
**levelled pair** if `φ(Stab_G(x)) = 0` for one (hence every) `x ∈ O`.

1. **Theorem.** Suppose some finite-index subgroup `G_1 ≤ G` has a levelled pair `(φ, O)` on `X`.
   Then `FSym(X) ⋊ G` and `Alt_fin(X) ⋊ G` are not of type `FP_2` over `Q`. In particular they are
   not finitely presented.
2. **Stabilizer law.** Let `G` be finitely generated. If `FSym(X) ⋊ G` or `Alt_fin(X) ⋊ G` is of type
   `FP_2` over `Q`, then for every finite-index `G_1 ≤ G` and every `x ∈ X`, the image of
   `Stab_(G_1)(x)` spans `H_1(G_1; Q)`.
3. **Nilpotent inputs.** If `G` is finitely generated and virtually nilpotent and `X` has an infinite
   `G`-orbit, then `FSym(X) ⋊ G` and `Alt_fin(X) ⋊ G` are not of type `FP_2` over `Q`. This holds for
   every action, free or not, so for such `G` it extends the lampshuffler theorem from free
   actions to all actions with an infinite orbit.

## Proof

1. **Reductions.** `FSym(X) ⋊ G_1` has finite index in `FSym(X) ⋊ G`, and `Alt_fin(X) ⋊ G` has
   index 2 in `FSym(X) ⋊ G`. `FP_2` over `Q` passes to and from finite-index subgroups. So assume
   `G_1 = G` and prove the claim for `E = FSym(X) ⋊ G`.
2. **Levels.** Fix `x_* ∈ O` and put `ℓ(gx_*) = φ(g)`. This is well defined because
   `φ(Stab(x_*)) = 0`, and `ℓ(hx) = φ(h) + ℓ(x)` for all `h ∈ G`, `x ∈ O`. Choose `t` with `φ(t) = 1`.
   So `t` raises levels by one, and `Δ = ker φ` preserves them.
3. **The proof of Theorem A, verbatim, except in two places.** The proof is in
   `research/artifacts/zp-lampshuffler-not-fp2-2026-09-13.md`, with `x_0 ≠ z` in `O` and `s = (x_0 z)`.
   - *Distinctness.* Freeness was used to make `x_0, z, t^(-n)x_0, t^(-n)z` pairwise distinct for
     large `n`. Levels give this: `ℓ(t^(-n)y) = ℓ(y) − n`, so for `n > |ℓ(x_0) − ℓ(z)|` the last two
     points have levels different from the first two, and they are distinct from each other because
     `t^(-n)` is a bijection.
   - *Step (c), the bad levels.* Suppose `t^i x_0 = δb` with `δ ∈ Δ_0 ≤ Δ` and `b ∈ B`.
     - Then `b ∈ O`, and `ℓ(b) = ℓ(t^i x_0) = ℓ(x_0) + i`. So `i` is determined by `b`.
     - Points of `B` outside `O` never qualify. The same holds for `t^(i-n)x_0`.
     - So (**) fails for at most `2|B|` values of `i`, which is all that Step (c) asserted.
   - *Everything else is unchanged.* No other step of the artifact's proof uses freeness: the
     Bieri–Eckmann criterion, locally finite kernels, the five-term sequence, the averaging
     idempotent killing `(t−1)y`, the separation of different levels `i` by `φ`, and the
     distinctness of the four cosets at a good level. ∎
4. **Stabilizer law.**
   - If the image `S` of `Stab_(G_1)(x)` does not span `H_1(G_1; Q)`, take a nonzero linear form
     vanishing on `S`.
   - `G_1` is finitely generated, so its image in `Q` is cyclic. After rescaling, it gives `φ` onto
     `Z` with `φ(Stab_(G_1)(x)) = 0`.
   - Then `(φ, G_1x)` is a levelled pair, and item 1 applies. ∎
5. **Nilpotent inputs.**
   - Take `G_1 ≤ G` torsion-free nilpotent of finite index. An infinite `G`-orbit contains an
     infinite `G_1`-orbit, since it splits into finitely many `G_1`-orbits. So some
     `Stab_(G_1)(x)` has infinite index in `G_1`.
   - In a finitely generated nilpotent group, a subgroup whose image spans `H_1(G_1; Q)` has finite
     index. (Standard, via Mal'cev completions: a Lie subalgebra of a nilpotent Lie algebra that
     surjects onto its abelianization is everything.)
   - So `Stab_(G_1)(x)` does not span, and item 2 gives the claim. ∎

## Examples and calibrations

- **Free actions.** Every character levels every orbit. This recovers Theorem A of
  `lampshuffler-groups-are-not-fp2-over-q`, including Houghton's `H_2 = FSym(Z) ⋊ Z`.
- **Coset actions inside a kernel.** `G` acting on `G/Λ` with `Λ ≤ ker φ` for some virtual character
  `φ` is levelled. Examples:
  - `BS(1,n)` on its cosets of `⟨a⟩`;
  - `Z^2` acting on `Z` through one coordinate;
  - any action that factors through a quotient acting freely and virtually indicably.

  None of these split extensions is finitely presented.
- **Houghton `H_n`, `n >= 3`, is finitely presented.** This is consistent: `H_n` is not a split
  extension of `FSym` by a group acting on the rays. `Z^(n-1)` acts only up to finitary corrections.
- **Kazhdan and other `H_1`-trivial inputs.** Item 2 is vacuous when every finite-index subgroup has
  finite abelianization. The theorem says nothing there.

## Application: the Abels route passes

For `P = A_p/C` and the two faithful transitive `P`-sets
- `Ω = Z[1/p]^2 × Q_p/Z_p` of `abels-quotient-product-form-model-with-one-singular-point`, with
  stabilizer `Z[1/p]^3 ⋊ T`, and
- `Ω' = P/T`, with `T ≅ Z^2` the torus, so that point stabilizers are the conjugates of `T` and
  two-point stabilizers are centralizers in `T`, subgroups of `Z^2`,

the stabilizers contain a conjugate `T^g` of `T`.
- Let `P_1 ≤ P` have finite index, and put `U_1 = P_1 ∩ U/C` and `T_1 = P_1 ∩ T^g`. Both have
  finite index in their groups, so `U_1 ⋊ T_1` has finite index in `P_1`.
- A character `φ` of `P_1` restricts to a `T_1`-invariant character of `U_1`.
  - On `U_1 ∩ {g_12 = g_23 = g_34 = 0}`, an abelian group rationally spanned by the root
    subgroups `e_13`, `e_24` (the `e_14(R)/C` part is torsion), `T_1` acts with the nonzero weights
    `(0,−1)` and `(1,0)`. So `φ` vanishes there.
  - `φ` then factors through the image of `U_1` in `R^3` (entries `12, 23, 34`). There the weights
    `(−1,0)`, `(1,−1)`, `(0,1)` are nonzero, so `φ` vanishes again.
- So `φ(U_1) = 0`, and `H_1(P_1; Q)` is spanned by the image of `T_1`, which lies in the
  stabilizer.

So neither action is levelled, and item 2 does not obstruct `Alt_fin(Ω) ⋊ P` or `Alt_fin(Ω') ⋊ P`.
The regular action `P/1` and the action on `P/(U/C)` are levelled, so they are excluded.

`Ω'` is the better candidate for the finitary gate. Its point and two-point stabilizers are
finitely generated, so the well-definedness relations of the presentation in
`finitary-mixing-of-fp-highly-transitive-groups-is-fp` are finite in number. What remains is the
presentation's relation family (R4), one relation for each `P`-orbit of pairs of transpositions,
which is infinite because `P` has infinitely many orbits on pairs. Finite presentation needs a
derivation of all but finitely many of them.

## Lesson for general BH

In a split finitary overgroup `Alt_fin(X) ⋊ G`, the abelian "motion" of the input must be realized
as rotation about points, never as translation of levels.
- Every virtual character of `G` must be nonzero on every point stabilizer.
- Otherwise the escaping-transposition class of Houghton's `H_2` reappears, and `FP_2` fails over
  `Q`.
- For soluble and amenable inputs, which have many virtual characters, this forces the torus into
  the stabilizers. The geometric models built on the Abels quotient do exactly that: the torus
  fixes the base point and dilates around it.
- This is the permutation-group form of the carrier principle: what the host must carry, the
  stabilizers must carry.
