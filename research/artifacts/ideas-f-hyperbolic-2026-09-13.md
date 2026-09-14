# Idea lane: Thompson's F, Gromov's question, nonsofic hyperbolic groups (2026-09-13)

Lane `ideas-f-hyperbolic`, ordered to generate new approaches first, kill them quickly, then execute the best
survivor.

**Targets:**
- `thompson-f-is-amenable` / `thompson-f-is-not-amenable`
- `thompson-f-is-sofic`
- `non-residually-finite-hyperbolic-group`
- `nonsofic-hyperbolic-group`

**Status labels:**
- **dead:** a node already on main kills the idea, or it only restates an open node;
- **alive:** no kill found and a concrete first test exists;
- **executed:** worked out in this lane.

Nothing here claims novelty against the literature beyond the repo and the sources named.

## Thompson's F

1. **Ore degrees must grow like Moore's tower.** *Dead.*
   - **Idea:** turn a uniform bound on common-multiple degrees into small Følner sets, then contradict
     Moore's tower bound.
   - **Kill:** the Tamari argument only gives the other direction: a Følner set of radius `R` for the
     supports gives `δ <= R`.
   - **Evidence:** pairwise degrees decouple from certificate size. Over `F_2` every `P_(2,1)` pair meets by
     degree 7 (`thompson-f-p21-over-f2-every-pair-meets-in-degree-seven`), while cardinality certificates
     need degree 11 (`thompson-f-p21-cardinality-certificate-in-degree-eleven`).
2. **Graded Ore sieve by the x_0-count.** *Executed; the sieve is vacuous for `P_(2,2)`.*
   - The abelianization makes `K[M]` bigraded, and extreme components of a common multiple are common
     multiples of extreme components.
   - Over the 94329 unsolved census pairs, every component pair is equal or settled by degree 7. So the
     sieve certifies nothing. See the section below.
3. **Kernel-dimension profiles.** *Alive, not executed.*
   - **Idea:** record `d_k(a, b) = dim ker A_k` on the letter window `M_(k, k+3)` for stubborn pairs and look
     for linear-recurrence structure. Normal forms are a regular language and right multiplication by a
     monomial is a letter-shifting transducer, so the solution spaces might be governed by finite-rank
     transfer data.
   - **Smallest test:** the `d_k` sequence for a sample of `P_(2,2)` pairs with `δ > 7`, through `k = 8`,
     calibrated on `P_(2,1)` profiles.
   - **Obstacle:** degree 8 has 274638 rows per pair, beyond Python bit rows
     (`research/artifacts/thompson-f-ore-over-f2-2026-09-13.md`); it needs M4RI-style dense elimination.
   - **Kill criterion:** profiles show no recurrence and jump irregularly with `k`.
4. **SAT instances of Moore's Hindman-type reformulation.** *Dead computationally.* Finite instances
   inherit Moore's tower lower bound (`thompson-f-folner-function-exceeds-every-tower`,
   `thompson-f-cardinality-certificates-need-tower-degree`).
5. **Schreier-graph Ponzi schemes on `F/H` with `H` avoiding end-rigid stabilizers.** *Dead as an easier
   route.*
   - End-rigid Schreier graphs are amenable (`thompson-f-end-rigid-schreier-graphs-are-amenable`).
   - For amenable `H`, co-amenability and amenability of `H` give: `F/H` is amenable iff `F` is (Eymard).
   - So small `H` is exactly as hard as `F`.
6. **Mean-free amenable actions of `F` force amenability.** *Alive.*
   - **Idea:**
     - following-model soficity witnesses exist iff `F` has a mean-free amenable action
       (`thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived`);
     - mean-free amenable actions exist for residually amenable groups through quotient towers, and for
       groups with a Kazhdan pair only when residually finite
       (`kazhdan-groups-mean-free-amenable-iff-residually-finite`);
     - every proper quotient of `F` is abelian, so no quotient tower exists.
   - **Conjecture:** a mean-free amenable action of `F` exists only if `F` is amenable.
   - **First test:** examine the averaging proof "invariant mean on `X` plus amenable stabilizers gives an
     invariant mean on the group" when stabilizers are only mean-null. Pin the finitely additive
     countable-union gap.
7. **Powers averaging for C*-simplicity of `T`.** *Dead.*
   - Conjugates of arc-supported elements with disjoint supports commute, so their averages keep norm 1.
   - Overlapping conjugates generate copies of `F`.
   - So this is circular with `thompson-f-not-amenable-iff-thompson-t-cstar-simple`.
8. **Entropy or Poisson-boundary certificates.** *Dead.*
   - Non-Liouville walks don't certify `ρ < 1` (`thompson-f-random-walks-are-not-liouville`).
   - Finite moment data can't either (`thompson-f-moment-data-cannot-certify-nonamenability`).
9. **Haagerup property and relator stability.** *Dead as a mechanism.* Kun–Thom-type nonsoficity needs
   relative property (T), which a Haagerup group lacks. It supplies no positive soficity mechanism either.

## Gromov's question and nonsofic hyperbolic groups

10. **Escape from subvarieties gives an explicit radius.** *Dead as novelty.*
    - Words of bounded length escape the variety `{g : g^N = 1}` in bounded-rank groups of Lie type
      (Eskin–Mozes–Oh; Breuillard–Green–Tao; not pinned). That excludes bounded-rank approximants at an
      effective radius.
    - Clause 3 of `lef-burnside-groups-iff-finite-simple-limits` already excludes every bounded linear degree
      qualitatively.
11. **Metric-ultraproduct dichotomy for simple limits.** *Dead by inheritance.*
    - **Idea:** a bounded-exponent limit `T` of `A_n` (or of classical groups of unbounded rank) has a
      quotient that embeds in the Hamming (or rank) ultraproduct. Generators of a transitive `A_n` cover
      all points, and irreducible generators have rank sums `>= n`. So the quotient is nontrivial, hence
      infinite and sofic (or linear sofic) of exponent `N`.
    - **Kill:** LEF already implies sofic, so the chain through
      `local-restricted-burnside-iff-lef-burnside-groups-are-finite` gives nothing new.
12. **Co-sofic invariant random subgroups from natural actions of simple approximants.** *Dead.* Regular
    actions always supply `δ_e`, and natural-action limits add no constraint.
13. **Transfer-operator counting of triangle homomorphisms.** *Dead.* For the `(A_7, A_7, A_8)` candidates,
    `|Hom(Δ, G)|` is a 3-cycle count in compatibility graphs. Expected counts don't exclude existence, and
    the large-quotient barrier stands (`a7a7a8-triangle-candidate-without-finite-quotients`, Attempts).
14. **Local restricted Burnside for finite solvable groups of bounded derived length.** *Dead.*
    - Schreier induction gives it elementarily.
    - Subsumed by `lef-burnside-approximants-are-nonlinear-and-nonsolvable` and
      `finite-nilpotent-groups-satisfy-local-restricted-burnside`, and approximants can be taken simple.
15. **Expander approximants.** *Dead.* The law on radius `>= C log |G_k|` would force exponent-`N` elements
    to have positive density, but nothing controls the radius against `|G_k|`.
16. **Following models for Kazhdan hyperbolic groups.** *Alive, theory.*
    - `kazhdan-groups-mean-free-amenable-iff-residually-finite` shows that a non-residually-finite hyperbolic
      Kazhdan group has only non-following sofic approximations.
    - **First test:** decide whether properly non-amenable almost-actions of such a group can have
      stabilizer data that converge to an invariant random subgroup other than `δ_e`.
17. **Pseudofinite model theory.** *Alive, weak.*
    - Simple pseudofinite groups are elementarily equivalent to Chevalley groups over pseudofinite fields
      (Wilson; not pinned), so ultraproducts of alternating or unbounded-rank approximants are not simple.
    - **First test:** find a definable-subgroup obstruction to an infinite exponent-`N` group lying inside
      the definable set `{g : g^N = 1}` of such an ultraproduct.

## Executed: the graded Ore sieve for P_(2,2)

- **Theorem** `thompson-f-ore-x0-components-meet-no-later`, route
  `thompson-f-ore-x0-components-meet-no-later-proof`:
  - the count of `x_0` letters is a monoid homomorphism `M -> N`, through the abelianization;
  - `K[F]` has no zero divisors;
  - so `δ(top(a), top(b)) <= δ(a, b)` and `δ(bot(a), bot(b)) <= δ(a, b)` for all nonzero homogeneous `a, b`.
- **Census application** `thompson-f-p22-x0-graded-sieve-certifies-no-pair`, script
  `experiments/thompson-f/ore/ore_graded_sieve.py`, run on MSI with output
  `research/artifacts/ideas-f-hyperbolic-2026-09-13-data/sieve_output.txt`:
  - no single-level pair is unsolved, and all 94329 unsolved pairs mix levels;
  - every unsolved pair's top and bottom component pairs are equal or settled by degree 7:
    - both equal: 166;
    - top equal, bottom settled: 26376;
    - top settled, bottom equal: 292;
    - both settled: 67495.
- **Consequence:** extreme `x_0`-components can't certify a non-Ore `P_(2,2)` pair over `F_2`. Any
  certificate has to see how the levels interact.

## Best three ideas for the next lanes

1. **Idea 3:** kernel-dimension profiles and transfer structure for mixed stubborn `P_(2,2)` pairs. The sieve
   now confines stubborn pairs to mixed ones.
2. **Idea 6:** does a mean-free amenable action of `F` force amenability?
3. **Idea 16:** stabilizer invariant random subgroups of non-following sofic approximations of
   non-residually-finite Kazhdan hyperbolic groups.
