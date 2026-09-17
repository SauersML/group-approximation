---
rg: 2
id: some-field-crossed-product-fails-the-rank-condition
kind: claim
title: Some crossed product of a countable group over a commutative field fails the rank condition
distinct_from:
  deligne-twisted-group-algebra-is-not-stably-finite: that asks one specific twisted group algebra of Sp4(Z) to fail stable finiteness, and it is refuted; this asks for any field crossed product, including skew group rings with transcendental coefficients, to fail the weaker rank condition.
  clifford-cover-anti-half-skew-ring-not-directly-finite: that is a skew group ring over a noncommutative Clifford lamp algebra with coset compression; this requires commutative field coefficients, the case that yields finitely entropic profiles.
  char-zero-steinberg-stably-finite-iff-invariant-measure: that gets infiniteness from idempotents cutting a paradoxical unit space; a field has no idempotents, so this needs a different mechanism.
artifacts:
  - research/artifacts/twisted-linear-entropy-profiles-2026-09-17.md
---

**OPEN.** For some countable group `G`, commutative field `K`, action `σ: G -> Aut(K)` and 2-cocycle `α`, there
are matrices `A` (size `d x r`) and `B` (size `r x d`) over `K*G` with `AB = I_d` and `r < d`.

**Payoff (criterion: kills a class).** By `twisted-linear-profile-deficits-are-rank-condition-failures`, the
twisted linear profiles over that `K*G` are invariant, finitely entropic entropy profiles over `G` with
`Phi -> 0`. So maximal Bernoulli Rokhlin entropy at `G` has **no profile-level proof**. No argument that uses
only the following can prove it:
- entropy inequalities on finite families;
- independence and uniformity of sites;
- window dependence of codewords;
- translation invariance of entropy values.

This covers Følner-type counts, Shannon or non-Shannon polymatroid LP certificates, and read-degree bounds.
Every such argument fails at `G` where it would conclude domination for the profile.

**Constraints on a witness** (`field-crossed-product-rank-condition-survival-cases`):
- `G` is nonamenable, and `σ, α` are not inflated from an amenable quotient;
- the coefficients generate a field transcendental over `K^G`;
- in characteristic 0 with `α = 1`, `Emb(K_0, C)` carries no invariant probability measure.

**Test cases.**
- **Ternary Leavitt twisted algebra.** `S_- = F_3[G]/(1+[z])` with `G = L_(F_3)(1,2)^x` and `z = -1` is the
  twisted group algebra `F_3^α[G/<z>]`. A unital two-pair Cohn family there
  (`ternary-anti-central-summand-has-cohn-family`) proves this claim
  (`some-field-crossed-product-fails-rank-from-ternary-cohn-family`).
- `Q(x) ⋊ PSL_2(Z)` by Möbius substitutions. It evades all three survival regimes.
- `F_p(x_g) ⋊ G`. The complex-measure argument is unavailable in characteristic `p`.
- Twisted group algebras `K^α[G]` in characteristic `p`.

**Negative evidence.**
- No idempotent cutting is available in a field.
- A Riemann–Roch count on pole divisors (`dim L(D) = deg D + 1`) behaves like a Følner count and fails on
  nonamenable orbits. So neither a construction nor a proof of the rank condition is visible.
- Literature status was not checked in this lane.

## Attempts

- **Idempotent cutting (a-gs-pull-10, 2026-09-17). Dies at the first step.**
  - Paradoxical point dynamics are available. `PSL_2(Z)` acts on `P^1(Q)` nonamenably, and principal parts of
    rational functions are indexed by poles.
  - Cutting `Q(x)` into pieces indexed by a paradoxical decomposition needs projections onto principal parts at
    subsets of poles. These are not in `K ⋊ G`, because `K` has no nontrivial idempotents.
  - The same mechanism works for Steinberg algebras (`char-zero-steinberg-stably-finite-iff-invariant-measure`)
    because there `C_c(X,k)` has idempotents.
- **Pole-degree counting as a proof of the rank condition (a-gs-pull-10). Dies at the Følner step.**
  - An element `f u_g` maps a Riemann–Roch space `L(D)` into `L(gD + poles(f))`.
  - A one-sided family `R^2 -> R` would force `2(deg D + 1) <= deg(union of translates of D) + O(1)`.
  - On nonamenable orbits some divisors have translate unions of degree at least `2 deg D`, so the count gives no
    contradiction.
- **Complex measures (a-gs-pull-10). Dies on the Möbius case.**
  - The affiliated-operator argument (`field-crossed-product-rank-condition-survival-cases` (c)) needs an invariant
    measure on `Emb(K_0, C)`.
  - For Möbius actions every such measure sits on algebraic fixed points of hyperbolic elements, which are not
    embeddings. In characteristic `p` there is no trace to use.
- **Ternary Leavitt summand.** See the route above. Its necessary condition (the support is not `F_3`-linear
  sofic) is recorded at `ternary-anti-central-summand-has-cohn-family`.
- **Finite-index division rings (swarm-0917-w4-gs-rokhlin-kazhdan, 2026-09-17). Kills the Möbius test case and the
  whole ordered class.** `virtually-hughes-free-field-crossed-products-are-stably-finite` (ESTABLISHED):
  - for faithful `σ`, `K*G` is simple, so a witness is exactly a faithful field crossed product that is not
    stably finite (with a cocycle allowed);
  - `K*G` is stably finite whenever every finitely generated subgroup has a finite-index subgroup that is
    residually torsion-free nilpotent, locally indicable amenable, free-by-cyclic, or a graph of these. Proof:
    right multiplication on a coset basis embeds `K*G` in `M_n(K*N)`, and `K*N` has a Hughes-free division ring
    (`fsp-graph-of-rings-and-linnell-extension-imports`, items 2 and 6);
  - so `Q(x) ⋊ PSL_2(Z)` (virtually free) has the rank condition, as does `F_p(x_g) ⋊ G` for such `G`.
  - **Where the class stops.** Infinite finitely generated Kazhdan groups have no locally indicable finite-index
    subgroup. A witness must contain a finitely generated subgroup outside the virtual Hughes-free class.
  - **Next test case:** `Q(x, y) ⋊ SL_3(Z)` (or `Γ(3)`) by projective substitutions, which evades all four
    regimes if `Emb(Q(x,y), C)` has no invariant probability measure (unchecked). Artifact
    `research/artifacts/field-crossed-product-virtual-division-embedding-2026-09-17.md`.
