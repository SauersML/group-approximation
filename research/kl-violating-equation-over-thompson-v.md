---
rg: 2
id: kl-violating-equation-over-thompson-v
kind: claim
title: A Kervaire--Laudenbach-violating equation with coefficients in Thompson's group V
refuted_by: [kl-holds-over-thompson-v]
distinct_from:
  kl-violating-equation-over-leavitt-unit-group: that allows any coefficients from the binary Leavitt unit group; this restricts every coefficient to the copy of Thompson's V inside it, so a witness here is a witness there but not conversely.
  thompson-v-not-hyperlinear: that is non-hyperlinearity of V by any certificate; this asks for one algebraic certificate of it, a nonsingular equation over V with no solution in any overgroup.
  kl-holds-over-thompson-v: that is the positive statement over V; this is its negation, and exactly one of the two can end up established.
---

**OPEN.** There are `w in V * <t>` with `deg_t(w) != 0` and `1 != a in V`
such that `a` dies in `(V * <t>)/<<w>>`.

## Consequences

- **A Leavitt violation.** By `leavitt-kl-violation-from-thompson-v-violation`,
  the same word is a violation over `R^x = L_(F_2)(1,2)^x`.
- **V is not hyperlinear.** By `thompson-v-not-hyperlinear-from-kl-violation`,
  through `kervaire-laudenbach-holds-for-hyperlinear`.

## Why V is a reasonable search space for the violation lane

- **Checkable.** Coefficients are prefix replacements, so products and
  equality are decided by tree-pair normal forms. Because
  `V <= EL_D(R) <= R^x` (`leavitt-cylinder-swaps-generate-thompson-in-el`),
  every candidate is also checkable by the shared Leavitt checker.
- **A different kind of certificate.** Inside V no compression criterion of
  this graph applies (`thompson-v-has-no-rigid-compression-defect`,
  `thompson-v-has-haagerup-property`). A violation over V would certify
  non-hyperlinearity by a mechanism no rigid-defect argument can supply.

## Attempts

1. **Short and generic words.** Dead, for every coefficient group and so
   over V.
   - Variable length at most five: Evangelidou (`length-five-kl-fence-citation`).
   - `t` occurring with one sign only: Levin's positive-equation theorem,
     Bull. Amer. Math. Soc. 68 (1962), 603--604, as cited in
     `length-five-kl-fence-citation`.
   - At least four light same-sign corners: `kl-four-same-sign-corner-words-inject`.
   - Small-cancellation words: `kl-small-cancellation-words-inject-every-coefficient-group`.
2. **Structured candidates.** Deferred. No candidate family over V has been
   proposed. Any surviving word must evade every fence in item 1 with
   coefficients drawn from V.
3. **Exhaustive generator census at variable length six and seven (2026-09-13).** No violation found.
   - **Census:** every `t`-exponent is `+-1` and coefficients are in `{1, a, b, b^(-1), c}`.
     That gives `181202` classes up to rotation and `w -> sigma(w^(-1))`.
   - **Certified injective:** `85432` classes, by
     `kl-thompson-v-short-generator-words-certified-injective`:
     - finite coefficient subgroup: `63678`;
     - four light corners: `4380`;
     - proper powers: `6`;
     - three light corners with (D4) and (A2): `15204`;
     - exact retractions onto V: `2164`.
   - **Collapse test.** The `113144` words left after the first two filters were each run
     through Todd--Coxeter enumeration over `<t>`, using the nine Bleak--Quick relators
     plus `w`, at `200000` cosets. All `113144` overflowed and none collapsed (MSI job array 731591).
     - V is simple, so a violation shows up exactly as index 1.
     - An overflow certifies nothing.
   - **Frontier:** `95770` words, by class in
     `research/artifacts/kl-thompson-v-generator-census-2026-09-13.md`.
   - **What a violation needs.** A violation of variable length at most seven with generator
     coefficients lies in the frontier and needs a coset budget above `200000`. Longer words
     or coefficients beyond the generators are untouched.
4. **Internal roots after endomorphisms (2026-09-17, d-klv).** No violation found. The
   method is dead as a general mechanism.
   - **Frontier search.** The certificate is `w^phi(t0) = 1` with `phi` an injective
     endomorphism of V and `t0 in V`. The search tried the `g+1` and `delta1` endomorphisms
     on the `90550` frontier words that remain after weight certificates.
     - `43831` words were processed before the run was stopped.
     - `1495` roots were verified independently, so these words are certified injective
       (`experiments/kl-thompson-v-internal-roots-2026-09-17/root_certificates.txt`).
     - NOROOT is capped and certifies nothing.
     - Details are in `research/artifacts/kl-thompson-v-internal-roots-2026-09-17.md`,
       Section 4.
   - **Class kill.** `higman-thompson-roots-miss-a-kl-word-over-thompson-v`: no homomorphism
     `V_w -> V_{n,1}` is non-trivial on V for `w = ctataT`, although KL holds for that word.
     - It imports Matte Bon's classification of homomorphisms `V -> V_{n,1}`
       (`thompson-v-homomorphisms-into-higman-thompson-are-coded`).
     - The method dies at Step 3 of its proof. The equivariant coding map keeps
       `<a,c> ≅ S_3` of orbit type `{1,3}` on the ambient, and
       `cantor-homeomorphisms-miss-a-unimodular-root`, item 2, then forbids the root.
     - The gate `thompson-v-endomorphism-breaking-the-s3-orbit-type` is refuted.
   - **What survives.** Internal roots combined with localization to the coefficient
     subgroup, and ambients whose homomorphisms from V are not spatial. The frontier is at
     most `89055` words, and the unprocessed words still need a search.
5. **Entropy and measure transplant, then a width fence (2026-09-17, d-nhg-p2).**
   - **Transplant.** Blind. Placing V inside a measure-preserving or entropy-carrying overgroup
     yields no mechanism for producing roots.
     - `Aut(X, mu)` contains every countable group, so the embedding adds no structure specific to V,
       and a root theorem there would be the full conjecture.
     - The Maharam extension of V's nonsingular Cantor action carries an infinite measure, with no
       finite trace to transport a Gerstenhaber--Rothaus root.
     - V has torsion, so no locally indicable host applies.
     - Each version reduces to hyperlinearity of V or to the full conjecture.
   - **Necessary condition, established.** `kl-kernel-lies-in-the-compact-unitary-width-radical`,
     by `kl-kernel-compact-unitary-width-radical-proof`, shows the following. If `a` dies through
     an identity with `A` old-relator factors, then in **every** dimension `d` and for **every**
     tuple `U in U(d)^S`, `a(U)` is a product of `A` conjugates of relator images. Its part (B)
     identifies the resulting radical as the common kernel into quotients of algebraic
     ultraproducts of unitary groups.
   - **Decomposition of this claim's consequences.** A violation here forces
     `thompson-v-has-bounded-compact-unitary-relator-width`, by
     `thompson-v-bounded-unitary-width-from-kl-violation`. That in turn gives
     `thompson-v-not-hyperlinear` directly, by `thompson-v-not-hyperlinear-from-bounded-unitary-width`.
   - **What would kill this claim.** One unitary tuple family in which a relator length is
     `o(l(a(U)))` for a single invariant length `l`. The length may be unnormalized rank, HS,
     operator norm or Schatten. Such a family refutes bounded width, and then this claim, by
     `kl-holds-over-thompson-v-via-unbounded-unitary-width`.
     - Permutation ratio models reduce to soficity by tensor amplification.
     - Unitary rank and HS ratio models are the new format.
     - The existing dead Følner and compression routes do not reach them.
