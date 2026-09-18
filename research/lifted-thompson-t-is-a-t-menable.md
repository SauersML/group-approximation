---
rg: 2
id: lifted-thompson-t-is-a-t-menable
kind: claim
title: "The lift T-bar of Thompson's T to the real line (the central extension of T by Z with the Euler class) has the Haagerup property"
distinct_from:
  thompson-v-has-haagerup-property: that is Farley's theorem for V, and so for T ≤ V; this asks it for the central extension T-bar of T by Z, which is not a subgroup of V in any known way
  cantor-integer-maps-by-v-have-haagerup-property: that is Brothier's Problem B for Γ = Z, for the group C(C,Z) ⋊ V; this is its one-dimensional subcase for the subgroup T-bar ≤ C(C,Z) ⋊ T, which it implies but is not known to imply it
  lifted-thompson-t-center-has-relative-t: that is the refuting statement (relative (T) for the centre); this claim implies its negation
artifacts: []
---

**Statement.** Let `T̄` be the group of lifts of Thompson's `T` to `R`, with central translation
`z(x) = x + 1`. Then `T̄` admits a proper conditionally negative definite function.

**Status.** OPEN.

## Role

This is **necessary** for `brin-thompson-groups-nv-are-a-t-menable` and for
`cantor-integer-maps-by-v-have-haagerup-property`, because
`T̄ ≤ C(C,Z) ⋊ T ≤ C(C,Z) ⋊ V ≤ 2V` (`lifted-thompson-t-embeds-in-cantor-integer-maps-by-v`).
It can fail on its own: its failure refutes both.

It is the smallest known subgroup of `2V` in which the central direction
(`cantor-integer-maps-central-direction-has-relative-t`) can be tested. The centre `⟨z⟩` goes to
`Z·1_C`.

## Equivalent form

`T` has the Haagerup property, since `T ≤ V` (`thompson-v-has-haagerup-property`). Pull a
proper cnd function of `T` back to `T̄`. The result is proper modulo `⟨z⟩`, because its sublevel
sets are finite unions of fibres of `T̄ → T`, and those fibres are cosets of `⟨z⟩`. By
`haagerup-splits-as-coset-plus-subgroup-properness` with `H = ⟨z⟩`:

> `T̄` is Haagerup **iff** some cnd function on `T̄` is proper on `⟨z⟩`.

A cnd function that is merely *unbounded* on `⟨z⟩` means exactly that `(T̄, ⟨z⟩)` is not
relatively (T). That is necessary for the claim. Whether it is sufficient for this central `Z` is
not settled here.

## Where this sits in the literature

It is an instance of an open problem. Gomez Aparicio, Julg and Valette, *The Baum–Connes
conjecture: an extended survey*, arXiv:1905.10081, p. 96, verbatim:

> "The behavior of the Haagerup property under central extensions is a widely open question.
> More precisely: if Z is a closed central subgroup in the locally compact group G, is it true that
> G has the Haagerup property if and only if G/Z has it? Both implications are open. See
> Proposition 4.2.14 and Section 7.3.3 in [CCJ+01] for partial results on lifting the Haagerup
> property from G/Z to G, in particular from SU(n,1) to ~SU(n,1)."

Two caveats:
- The contents of CCJJV Proposition 4.2.14 were **not checked verbatim**. If its hypotheses hold for
  `T̄ → T`, this claim closes, and the refutation route through
  `lifted-thompson-t-center-has-relative-t` dies. **Checking it is the cheapest next step.**
- No source stating the Haagerup property of `T̄`, or its failure, was found (searches of
  2026-09-18).

Kida, arXiv:1309.3739, links the pair property to stability: if `(G, C)` does not have (T), then
`G` is stable.

## Attempts

- **2026-09-18 (swarm-0917-w8-w8-nv-last1, host-geometry): first probes.**
  - *Witness form.* Since `z` is central, a witness for non-relative-(T) can be cut down along the
    spectral projections of `π(z)`. Each such projection commutes with `π(T̄)`, and some spectral
    band keeps the relative defect, by averaging `Σ_s ‖π(s)P_j ξ − P_j ξ‖²` over bands. So a
    witness amounts to unitary representations of `T̄` in which `z` acts with spectrum in narrow
    bands near, but away from, `1`. Disintegrated, these are projective representations of `T`
    with multiplier `e(θ·c)`, where `θ → 0` and `c` is a `{0,1}`-valued Euler cocycle, and they
    have almost invariant vectors. This is a sketch; the disintegration step is not written out.
  - *Permutation witnesses on dyadic orbits: die.* Let `O ⊂ R` be a `T̄`-orbit. Then `z` acts
    freely on `O`, so `ℓ²(O)` has no `z`-invariant vector, and almost invariant vectors would make
    it a witness. They do not exist:
    - Let `ξ` be `ε`-invariant under the generating set `X` of (TC1). Then `|ξ|²` is
      `2ε`-invariant in `ℓ^1`.
    - Summing over the `z`-orbits gives a probability `g` on `O/Z`, which is a `T`-orbit in
      `S^1`. It is still `2ε`-invariant under the image of `X`.
    - The Namioka layer-cake argument gives a finite level set `F' ⊂ S^1` with
      `Σ_s |sF' Δ F'| ≤ 2ε|X|·|F'|`.
    - For `ε < 1/(14 L |X|)` this contradicts (TC1) of `thompson-t-orbits-carry-no-invariant-means`. The same argument kills `ℓ²` of any countable
    `T̄`-set whose `Z`-quotient maps finite-to-one and equivariantly to `S^1`.
  - *Virtual splitting is unavailable.* `T` is simple and infinite, so every finite-index
    subgroup of `T̄` maps onto `T`. A virtual splitting would make the rational Euler class of `T`
    zero. It is recalled as nonzero (Ghys–Sergiescu), but that is unverified. So the braid-group
    mechanism does not apply: `B_3` is the lift of `PSL_2(Z) ≤ T`, and the class is torsion there.
  - *Cubical approaches are not excluded by the `2V` kills.* The Callard–Salo distortion and the
    cubical ellipticity of `1_C` concern `2V` and `C(C,Z) ⋊ V`. They do not pass to the subgroup
    `T̄`: a commensurating action of `T̄` need not extend to one of `G`, and `z` is undistorted in
    `T̄`, since `rot(z^N) = N`. One constraint does remain. In any `T̄`-action on a
    finite-dimensional CAT(0) cube complex with `z` hyperbolic, the minset splitting gives a
    homomorphism `T̄ → R` nonzero on `z`. So `z` is not hyperbolic there when `Hom(T̄, R) = 0`,
    which again reduces to the nonvanishing of the rational Euler class.
  - *Next falsifiable steps.*
    - (a) Read CCJJV Proposition 4.2.14 and §7.3.3 verbatim, and test their hypotheses on `T̄`.
    - (b) Try the twisted "complementary series" family: `T̄` acting on `θ`-quasi-periodic
      functions on `R` with density weight `(a^(-1))'^(1/2+s)`, where `z` acts by the scalar
      `e(−θ)`. Ask whether it has almost invariant vectors as `θ → 0`. For `θ = 0` this is the
      twisted Koopman question for `T` on `S^1`.
