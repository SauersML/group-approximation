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
- **Finite-field point models (sw-016, 2026-09-17). Three test-case regimes die; the node stays OPEN.**
  See `finite-field-point-models-give-the-rank-condition`.
  - Evaluate the coefficients at finite-field points along a finite or sofic permutation model. A one-sided
    inverse then gives `d(1-ε)|V| <= rank <= r|V|` over a finite field.
  - This kills, as witnesses:
    - every action on `k(x)` by `k`-automorphisms, including the Möbius case `Q(x) ⋊ PSL_2(Z)`;
    - projective linear actions on `k(x_1..x_n)`;
    - Bernoulli fields `k(x_g) ⋊ G` over sofic `G` in every characteristic;
    - via Malcev–Neumann, every crossed product with any twist over a bi-orderable group, such as `F_2`,
      surface groups and RAAGs.
  - Exact failing step for a witness: it must defeat (P2). No approximately equivariant assignment of
    finite-field points may make the coefficients' denominators nonzero. So either `α ≠ 1`, or the coefficient
    `G`-ring has no finite-field point models (for example a Bernoulli field over a nonsofic group). The group
    must also be neither amenable nor bi-orderable.
  - The ternary Leavitt route (`α = ±1`, `G = L_(F_3)(1,2)^x/<-1>`, which has torsion) survives, as do twisted
    group algebras `K^α[G]` over non-bi-orderable groups. These are the named test cases still alive.
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
- **Finite-field point models (swarm-0917-w4-pull-gs-3, 2026-09-17). Kills the `Q(x,y) ⋊ SL_3(Z)` test case and
  every untwisted rational case.** `rational-function-field-crossed-products-have-the-rank-condition`
  (ESTABLISHED, unreviewed):
  - for any group `G` and any action on `k(x_1..x_n)` (`k` a prime field, `α = 1`), `K ⋊ G` has the rank
    condition; for faithful actions it is stably finite;
  - proof: reduce mod `p` and let `G` act by partial substitution on `F_q^n`. The model of `AB = I_d` is exact off
    the zero set of one nonzero polynomial `D`, so `(d - r) q^n <= d deg(D) q^{n-1}` (Schwartz–Zippel);
  - so every subgroup of `Bir(P^n_Q)` or `Bir(P^n_{F_p})`, Kazhdan or not, fails as a host of an untwisted
    rational witness, including the Möbius case and `Q(x,y) ⋊ SL_3(Z)`;
  - **Where the class stops.** A witness needs at least one of the following:
    1. a cocycle that is not a coboundary on finite models (the ternary route lives here);
    2. coefficient orbits in no finitely generated rational subfield closed under finitely many `σ_g`
       (Bernoulli fields `F_p(x_g)`; for sofic `G` the same count over sofic models is expected to kill them, but
       this is not recorded);
    3. a non-rational finitely generated field. There the same proof needs Lang–Weil plus spreading out, which
       is not imported.
- **Lang–Weil point models (swarm-0917-w5-pull-tf-2, group-rings, 2026-09-17). Kills witness class 3: every untwisted
  finitely generated field.** `finitely-generated-field-crossed-products-have-rank-condition` (ESTABLISHED,
  unreviewed, via `lang-weil-point-count`):
  - for any group `G` and any action on a field finitely generated over its prime field, `K ⋊ G` has the rank
    condition, and it is stably finite when the action is faithful. The local form covers every field in which
    finite data lie in a finitely generated subfield stable under finitely many `σ_g`;
  - **invariant:** the ratio of `F_q`-points `|V(D)(F_q)| / |Hom(R, F_q)|` for a spread-out model `R` of `K`;
  - **dying step:** the model of `AB = I_d` by partial substitutions on `Hom(R, F_q)` is exact off `V(D)`. After
    reducing modulo a prime chosen away from the minimal primes of `(D)` (Krull's principal ideal theorem), `V(D)`
    has dimension below that of the model, so Lang–Weil gives `(d - r) <= d · O(q^{-1})`;
  - so number fields, K3 and Calabi–Yau function fields, and subgroups of `Bir(V)` for any variety `V` over `Q` or
    `F_p` all fail as hosts of an untwisted witness;
  - **where the class stops.** A witness needs either (1) a cocycle that is not a coboundary on finite models (the
    ternary route), or (2) coefficient orbits in no finitely generated `σ_T`-stable subfield. The basic case of (2)
    is Bernoulli fields `F_p(x_g)` over a group `G` that is not known to be sofic; for sofic `G` a count over sofic
    models is expected to kill it, but that is not recorded.
- **Root-of-unity specialization (swarm-0917-w8-w8-gs-pull, finite-models, 2026-09-17). Kills the twisted group
  algebra test case as a barrier.** `twisted-group-algebra-failures-are-finite-field-cover-failures`
  (ESTABLISHED, unreviewed):
  - for trivial action, any field and any cocycle, a rank or stable finiteness failure of `K^α[G]` specializes
    to one of `F_q[E_0]`, where `E_0` is a central extension of a subgroup of `G` by a locally cyclic `p'`-torsion
    group. So a trivial-action witness refutes Gottschalk and the root `every-group-has-positive-rokhlin-entropy-action`
    outright, and the profile barrier is never the strongest conclusion;
  - **invariant:** the cocycle composed with a character `Λ -> F̄_p^x` that extends a residue map on the finitely
    many relevant values. Divisibility of `F̄_p^x` makes the extension exist;
  - **dying step:** the central idempotent of the finite cyclic value group makes the twisted algebra a corner of
    a group algebra. The ternary (`±1`) and Deligne (`μ_3`) routes are the torsion special cases;
  - **where the class stops.** An informative witness (one that does not already refute INF) needs a
    nontrivial action. Either the orbit field is non-Bernoulli with no finitely generated stable subfield, or the
    field is Bernoulli with a cocycle. Equivariant residue maps are the (P2) point-model problem.
