---
rg: 2
id: v-times-minimal-free-sft-alternating-full-groups-are-fp
kind: claim
title: For a finitely presented group with a minimal free subshift of finite type, the alternating full group of V times the transformation groupoid is finitely presented
distinct_from:
  v-times-shift-alternating-group-is-of-type-fp2: that asks for type FP_2 of one group, V times the full two-sided Z-shift, whose Z-action is neither free nor minimal and which is not simple; this asks for finite presentation of the simple groups built from minimal free SFTs over arbitrary finitely presented groups.
  labbe-shift-derived-full-group-is-finitely-presented: that asks for finite presentation of the derived full group of one Z^2 SFT without the V factor; this multiplies by the groupoid of V, which kills the index map and makes the full group equal its alternating group.
  fp-alternating-full-groups-of-free-subshifts-force-sft: that is a necessary condition (finite type) for finite presentation without the V factor; this is the sufficiency assertion with the V factor, restricted to minimal free SFTs over finitely presented groups.
refuted_by:
  - v-times-golden-silver-wang-product-full-group-is-not-fp
---

**OPEN.** Premise (P2) of route
`boone-higman-via-v-times-aperiodic-sft-full-groups`.

**Statement.**
- Let `Λ` be an infinite finitely presented group, `A` a finite alphabet, and
  `X ⊆ A^Λ` a nonempty subshift of finite type on which `Λ` acts freely and
  minimally.
- Let `G_V` be the groupoid of germs of Thompson's group `V` on `C = {0,1}^N`, and
  `T = G_V × (Λ ⋉ X)`.

Then `A(T)`, which equals the topological full group `F(T)` by
`v-times-ample-full-groups-are-generated-by-transpositions`, is finitely
presented.

**Status of the hypotheses.**
- By the route, `A(T)` is simple and contains `Λ`, so a positive answer gives
  finitely presented simple hosts for every subgroup of `Λ`.
- The statement contains no computability hypothesis. Decidability enters only
  through the existence of `X` (premise `decidable-groups-embed-in-fp-groups-with-minimal-free-sft`).
- The restriction to shifts of finite type is forced in the analogous setting
  without `V` (`fp-alternating-full-groups-of-free-subshifts-force-sft`).
  Whether finite presentation of `A(T)` forces finite type of `X` was not checked.

## Attempts

**Attempt 1 (2026-09-17): look for obstructions already in the graph.** None
applies.
- *Kazhdan subgroups.* `A(T)` contains `Λ`, which may have property (T), so the
  obstruction of `input-encoded-sft-groupoid-hosts-are-not-universal` does not
  transfer.
- *Mod-2 groupoid homology* (`derived-full-group-h2-filtered-by-mod-two-groupoid-homology`).
  The groupoid homology of `G_V` vanishes in every degree, as the Thompson `V`
  case there records. A Künneth formula for products of ample groupoids would then
  make the homology of `T` vanish. This is heuristic: the Künneth import is not in
  the graph.
- *Index map.* `F(T) = A(T)`, so no abelian quotient of the full group obstructs.

**Smallest test case.** `Λ = Z^2` and `X` a minimal free SFT, for example Labbé's
Wang shift. Test the natural finiteness method there: a Stein--Farley complex of
prefix trees in the `C` coordinate with clopen partitions of `X` labelled by
translations, together with Brown's criterion. The needed input is connectivity of
descending links, which is where finite type of `X` should enter. Not attempted.

**What would kill it.** One pair `(Λ, X)` as above for which `A(T)` has a
non-finitely-generated `H_2`, or a retract or quotient visibly not of type `FP_2`.

**Attempt 2 (2026-09-17): a necessary condition by a basis-switching representation.** *Obstruction
proved; P2 not refuted.*
- *The theorem.* `fp-v-times-subshift-full-groups-force-connected-differences`. If `A(T) = F(T)` is
  finitely presented, there is `m` with every difference set `Δ(x, y)` of `X` `m`-connected. So
  the minimal SFT `X` has no finite asymptotic pairs and `|L_F(X)| <= |A|^|∂F|`, which gives zero
  entropy over amenable `Λ`.
- *The mechanism.* Split `Δ(x, y)` into two far parts. The lift of `F(T)` to `C_0 × Λ.x ⊔ C_0 × Λ.y`,
  written with a two-dimensional fibre, is conjugated by `[[1, 1], [0, 1]]` on one part. Every short
  relator reads only one part, so it still holds. But two commuting site-conditioned 3-cycles, one
  reading each part, stop commuting.
- *What P2 now needs.* Its hosts must be boundary-deterministic. Over amenable `Λ`, a minimal SFT
  with a finite asymptotic pair is one with positive entropy (route, Section 5, sketch). So a
  counterexample to P2 by this route is exactly a minimal free SFT with a finite asymptotic pair,
  over an infinite finitely presented group. Whether one exists is open here.
- *Earlier test not yet run.* Over non-amenable one-ended `Λ` the bound says nothing quantitative.
  A kill there needs a minimal free SFT whose difference sets split into two far parts, for example
  two independent defect regions separated by a wide strip on which the two points agree.

**Attempt (2026-09-18, swarm-0917-w6-w6-bh-last2): refute P2 through a finite asymptotic pair.**
*Dead over unique-product groups; the obstruction is proved.* This is the refutation left open by
the connected-difference necessary condition (worker bh-break, need 65f52e90).
- *The theorem.* `minimal-sfts-on-up-groups-have-no-finite-asymptotic-pairs`. If a minimal SFT has
  a finite asymptotic pair `(x, x')`, then some nonzero `a >= 0` supported on a syndetic window
  satisfies `a * ν_b = 0` in `R[Λ]` for every letter `b`, where
  `ν_b = [x = b] - [x' = b]`.
  - So over every unique-product group there is no such pair, and patterns are determined by
    their boundary layers.
  - This covers `Z^d`, bi-orderable groups and their direct products, and non-amenable examples
    such as `F_2 x F_2 x Z^2`.
- *The mechanism.* Flip `p' -> p` at occurrences, which stays inside `X`. The change of a site
  potential `Ψ = Σ ψ(k, y(k))` under a flip at `g` is a fixed row `(Mψ)_g`. Gordan's alternative
  gives either a `ψ` whose descent removes `p'` from a syndetic window, contradicting minimality,
  or a nonnegative zero divisor.
- *What remains for a refutation of P2.* Either an acting group with a nonnegative zero divisor
  (torsion suffices, as with `(1 + t)(1 - t) = 0`), or a minimal free SFT whose infinite
  difference sets split into two far parts. Over unique-product `Λ`, including `Z^2` and every
  Durand--Romashchenko hierarchy, only the second remains.

**Attempt (2026-09-18, swarm-0917-w7-w7-bh-last1): operator-valued fibres over the V-orbit.**
*Obstruction strengthened to every operator family; P2 not refuted.*
- *The theorem.* `fp-v-times-subshift-full-groups-force-quantum-rigidity`. If `A(T) = F(T)` is
  finitely presented and `Λ` acts freely on the subshift `X`, then:
  - `X` is of finite type, which settles the question in the status above;
  - `X` is `D`-quantum rigid over every field, for all large `D`.
- *The mechanism.* Put an arbitrary locally commuting, locally admissible idempotent family `E_a(q)`
  into the fibre of the orbit representation on `k[C_0] ⊗ k[Λ] ⊗ W_0`.
  - The window idempotents `P_α` split `W_0` into pieces on which the family is the scalar family of a
    point of `X`, so every short relator holds.
  - The one relation `[g_1, g_2] = 1`, for two translated site-conditioned 3-cycles, becomes
    `(H - 1)^2 ⊗ [E_a(p), E_b(q)] = 0`.
  - For finite type, the scalar family of a point of `X_N \ X` violates an iterated commutator of
    `V`-conjugated conditioned 3-cycles, which reads a forbidden pattern.
- *What P2 now needs.* Every minimal free SFT over every infinite finitely presented `Λ` must be
  quantum rigid over every field. Over `Z^2`, P2 at Labbé's shift implies
  `labbe-wang-shift-crossed-product-is-finitely-presented` over every field (route
  `labbe-crossed-product-fp-via-v-full-group-fp`), and hence `free-minimal-z2-sft-is-quantum-rigid`.
- *Where a refutation should now look.* One noncommuting quantum family at every scale, over any
  field, for one minimal free SFT. The walls and finite asymptotic pairs of the earlier attempts are
  the two-dimensional case. The remaining candidates are genuinely contextual families, for example a
  periodic quantum tiling of Labbé's tiles at every scale (`labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`),
  or an exactly matricial crossed product (`matricial-aperiodic-sft-rings-are-not-quantum-rigid`).
- *Not attempted.* The converse: whether quantum rigidity of `X` makes `F(T)` finitely presented. It
  would reduce P2 to rigidity plus finite type.

**Attempt (2026-09-18, swarm-0917-w7-w7-bh-follow): bypass P2 on the ring side.** *P2 not settled;
it is removed from one route to Boone--Higman.*
- *The lemma.* `quantum-rigid-sfts-over-fp-groups-have-fp-crossed-products`: over any finitely
  presented `Λ`, a quantum rigid SFT has a finitely presented crossed product `LC(X, F_2) ⋊ Λ`. The
  proof is the universal algebra with the relators of `Λ` added, acting on itself by left
  multiplication.
- *Consequence.* With the necessity theorem of the previous attempt, P1 ∧ P2 gives
  `decidable-groups-lie-in-fp-free-minimal-crossed-products` (E).
- *The bypass.* Route `boone-higman-via-leavitt-units-of-rigid-sft-overgroups` has
  `G <= Λ <= B^x <= (B ⊗ L)^x`, with `B` central simple
  (`free-minimal-cantor-crossed-products-are-central-simple`). It needs (E), the K-theory premise
  `free-action-leavitt-tensor-hosts-have-trivial-k1-k2`, and the Khanh transfer. Neither P2 nor the
  unattempted converse above is on it.
- *What this says about P2.* For Boone--Higman, P2 matters only through the quantum rigidity of one
  shift. Group-side finite presentation of `A(T)` is needed only on the V-times route.

**Attempt (2026-09-18, swarm-0917-w8-w8-z-pull): split difference sets in a product of two
metallic mean Wang shifts.** *P2 refuted, pending review.*
- *Torsion case closed.* `minimal-sfts-have-no-finite-asymptotic-pairs`: over every infinite
  finitely generated group, minimal SFTs have no finite asymptotic pairs. The proof flips a pair
  independently at a separated syndetic set of occurrences, avoids one pattern by the local lemma,
  and contradicts minimality. So the finite-pair branch of the previous attempts is dead
  everywhere, torsion included. Only split infinite difference sets were left.
- *The counterexample.* `metallic-wang-shift-product-is-minimal-with-split-differences`. Take
  `X = Ω_1 × Ω_2`, the product of Labbé's golden and silver metallic mean Wang shifts over `Z^2`.
  - `X` is a minimal free SFT. The factors are almost one-to-one extensions of the rotations by
    `β_1` and `β_2`, and `1, β_1, β_2` are independent over `Q`.
  - Each `Ω_n` has a pair differing exactly in a two-row band. Approach the horizontal partition
    line `y = 0` from both sides at an `x ∉ Q(β_n)`.
  - Shifting the second factor's band `m + 2` rows up gives a difference set with two parts at
    distance `> m`.
- *The kill.* `v-times-golden-silver-wang-product-full-group-is-not-fp`. With
  `fp-v-times-subshift-full-groups-force-connected-differences`, part 1, `A(T) = F(T)` is not
  finitely presented for `(Z^2, Ω_1 × Ω_2)`. This is the kill named in Attempt 2 ("a minimal free
  SFT whose difference sets split into two far parts"). It holds already over `Z^2`, with no need
  for non-amenable groups.
- *What survives, to be split off as a new claim.* An existential or restricted P2, for example:
  - "some minimal free SFT over `Z^2`, such as one Labbé shift, has `A(T)` finitely presented";
  - "SFTs with coarsely connected difference sets have `A(T)` finitely presented".
  Coarse connectivity is now a necessary hypothesis. Minimality, freeness, finite type, zero
  entropy and no finite asymptotic pairs do not imply it.
- *Routes affected.* `boone-higman-via-v-times-aperiodic-sft-full-groups` and every route citing
  P2 for an arbitrary SFT produced by P1 lose this premise. They need P1 to output coarsely
  connected (wall rigid) shifts and a restricted P2. The ring-side bypass of the previous attempt
  does not use P2.
- *Also shown.* By part 1 of `fp-crossed-products-force-connected-differences`, the same `X` is not
  quantum rigid, over any field. This is not a counterexample to
  `free-minimal-z2-sft-is-quantum-rigid`, which is existential.
