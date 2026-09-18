---
rg: 2
id: cantor-integer-maps-central-direction-has-relative-t
kind: claim
title: "The pair (C(C,Z) ⋊ V, <1_C>) has relative property (T): every cnd function on C(C,Z) ⋊ V is bounded on the constant functions Z·1_C"
distinct_from:
  cantor-integer-maps-by-v-are-not-a-t-menable: that denies the Haagerup property; this is a strictly more specific statement that implies it (a proper function is unbounded on the infinite subgroup <1_C>), and it is the weakest relative-(T) statement for a subgroup of C(C,Z)
  cantor-integer-maps-central-growth-criterion: that is the established equivalence between failure of this claim and almost invariant vectors with no 1_C-invariant vector; this is the open assertion that no such representation exists
  extractable-character-spectra-carry-no-almost-invariant-vectors: that establishes this claim for the extractable spectral parts of all cnd functions (with an explicit bound); this is the full statement, whose remaining case is scale-incoherent characters
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that proves boundedness of 1_C for commensurating (wall) cnd functions only; this asks it for all cnd functions
refuted_by:
  - cantor-integer-maps-by-v-have-haagerup-property
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

**Statement.** Let `G = C(C,Z) ⋊ V` and `z = 1_C`. For every cnd function `ψ` on `G`,
`sup_M ψ(z^M) < ∞`.

**Equivalent forms.** By `cantor-integer-maps-central-growth-criterion`, the following are
equivalent to the statement:
- no unitary representation of `G` without nonzero `π(1_C)`-invariant vectors has almost
  invariant vectors;
- for every cocycle, the restriction to `ker(π(1_C) − 1)^⊥` is a coboundary.

By `extractable-character-spectra-carry-no-almost-invariant-vectors`, it holds for the part of
any cocycle carried by finitely atomic, bounded-phase-variation or `F`-regular characters.

**Why it matters.**
- It implies that `2V`, and every `nV` with `n ≥ 2`, is not Haagerup, since
  `G ≤ 2V ≤ nV`.
- Its negation is necessary for Problem B(Z) and for Haagerup of `nV`. So a positive answer
  must construct almost invariant laws on scale-incoherent characters with `χ(1_C) ≠ 1`.

**Status.** OPEN. The attempt to close it is recorded under
`cantor-integer-maps-sup-norm-is-cnd-dominated`, Attempts, 2026-09-17.

## Attempts

- **2026-09-17 (swarm-0917-w5-nv-cocycle): paradoxical push-forward along an extraction (dies
  at scale-incoherent characters).**
  - The three moves `0↦00`, `0↦01` and the first-letter swap make any probability measure on
    `C` almost invariant under them paradoxical.
  - This kills every spectral part carried by a `V`-invariant character set with an equivariant
    Borel map to `Prob(C)`
    (`extractable-character-spectra-carry-no-almost-invariant-vectors`).
  - It dies where no location can be read off equivariantly: characters with infinite phase
    variation and no convergent `F`-variation. The kill uses only three group elements, so it
    cannot see correlations across scales. An argument there must use unbounded families of
    elements of `V`, for example the relative-(T) generation of `C(C,Z)` by conjugates.
- **Linear-response designs (die).** Take vectors whose `1_C`-phase is `e(θm)` on mass at
  charge `m`, with invariance defect `o(θ)`. A charge inequality from the same push-forward,
  `⟨|arg π(1_C)| η, η⟩ ≤ 5δ + 3ε²`, blocks them. It does not constrain growth rates, so it does
  not decide the claim.
- **Quasimorphisms and congruence quotients (die).**
  - Every homogeneous quasimorphism of `G` vanishes on `A`, so `scl(1_C) = 0` gives nothing.
  - In `C(C,Z/N) ⋊ V` the image of `1_C` has finite order, so it can carry no growth witness.
- **2026-09-17 (swarm-0917-w6b-w6b-nv-break): independent or mixing witness laws (die;
  class-kill).**
  - Established `cantor-central-witnesses-have-long-range-dependence`. Suppose a witness
    `ξ` is `ε`-almost invariant with no `1_C`-invariant vector, and `(u, v)` is a pair of
    disjoint, non-complementary cones. Then the spectral law keeps the phases `χ[u]` and `χ[v]`
    at conditional TV-dependence at least `(1 − ε − 50Lε)/8`, given any `V`-invariant function.
    Here `L` is the word length of four moving elements.
  - **Invariant:** `χ[0] = χ[00] + χ[01]`. Two prefix moves turn independence into
    `ν ≈ ν * ν` in total variation.
  - **Where every member dies:** `ν̂` cannot leave `1`, since it stays near `{0, 1}` with steps
    less than `1`. So `χ[0]` and `χ[1]` have atoms near mass `1` at `0`, which forces
    `χ[C] = 0`.
  - **Class killed:** independent-subtree, finite-range or mixing random characters, wrapped
    Gaussian charges with small correlations, and random cone products with rarely included
    common ancestors.
  - **Not ruled out:** witnesses with long-range coupling that is not a `V`-invariant function
    of `χ`, for example a random scale shifted by `V`.
  - **Refutation route (not recorded as a node).** Suppose some co-amenable `H ≤ G` contains
    `1_C` with `(H, Z·1_C)` not relatively (T), for example with `ψ : H → R` and
    `ψ(1_C) ≠ 0`. Then this claim fails: induce `e^{2πitψ}`, use Fell continuity of induction,
    and note that `1_C` acts by a scalar.
    - Obstruction: take a section cocycle `c(g, x)` of `G/H`. If `ψ∘c(s, ·)` is bounded for the
      generators `s`, averaging `ψ∘c` with the invariant mean gives a homomorphism `G → R`
      that is nonzero on `1_C`. This is impossible because `G` is perfect.
    - So such `H` must have unbounded transfer.
