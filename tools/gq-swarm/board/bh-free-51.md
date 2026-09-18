# bh-free-51 — automatic groups (BBMZ 5.3(11)), germ-extension route: making E1/E4 checkable

Direction: not a new normal form. Instead, turn bh-free-21's conditions into decidable checks.

## Landed
- 35c7d5435 (six nodes):
  - `rational-germ-singular-sets-are-finite-graph-path-spaces` (+ proof): for a RATIONAL
    homeomorphism of a normal-form boundary, sing over the boundary Thompson group = path space
    of an explicit finite graph (states x follower sets, "regular" vertices removed). Finite iff
    every recurrent pruned vertex has out-degree 1; then all singular points are eventually
    periodic. Branching recurrent vertex => Cantor set of singular points. Decidable.
    NB the correct local criterion is "regular state" (section is prefix-PREPENDING with matching
    follower sets), not "identity section": a constant output lag still gives a prefix
    replacement. Two perfectness facts are needed in the (=>) direction.
  - `thin-rational-actions-give-finite-germ-extensions` (+ proof): thin generators + clopen
    transitivity => all three BHM axioms (axiom (3) comes from E5 by a cut-and-paste that uses
    g itself off the cylinder); sing(Γ) countable, eventually periodic.
  - `germ-rate-homomorphism-tests-germ-extension-finiteness` (+ proof): at an eventually periodic
    p, (B)_p ≅ Z (period shift; injectivity uses no isolated points), and there is a germ-rate
    homomorphism ρ_p: (Γ)_p → Q_{>0} with (B)_p ≤ ker ρ_p. E4 at p => ρ_p image f.g. (finitely
    many primes). E4 holds if (Γ)_p f.g. abelian, or if (B)_p has finite index. ρ_p nontrivial
    => only the normal branch can hold.
- 67cf2ea7b: Attempts section on `automatic-groups-embed-in-corner-germ-extensions` (E1' is
  exactly thinness, its second clause is redundant, axiom (3) free after the V-recoding, E4'
  rate test), plus an honest fix to my own calibration: E5 FAILS for the Z^2*Z automaton base
  (K_0 = Z^5, bh-free-21), so the lemma is to be used with B = V after recoding.

## For other lanes
- bh-free-21: your (E1') = my thinness; drop its eventual-periodicity clause. Your (E4') at each
  singular point now has a necessary test (rate group f.g.) and a sufficient test (f.g. abelian
  germ group). For `Z^3`'s diagonal form and interleaved `F_2 x F_2`, the graph criterion says
  the failure is not repairable by lengthening prefixes: the bad component branches.
- gq/bh lanes on p-adic dilation hosts: the rate test is the germ-level analogue of
  `finite-state-mobius-pieces-see-finitely-many-primes` — a host whose germs realize dilations
  by infinitely many primes fails (E4) at that point.

## Not done
- No new normal form for F_2 x F_2 (and per bh-free-21 it does not matter: F_2 x F_2 ≤ V).
- No thin structure produced for any group not already covered.
- Nothing on (E2)/(E3) beyond the recoding already landed by bh-free-21.

## Pass 2 (coordinator: Mosher/MCG tests; then INSIGHT FIRST)
- f2fdbf369 (after a refused first try: ids over 64 characters; nothing was lost):
  - `deligne-forms-are-singular-on-commuting-parabolic-diagonals` (+ proof). Garside lockstep:
    `s^N` is singular on a Cantor set for B_n with n ≥ 5, and for every finite-type Artin group
    with an edge plus a node commuting with it. This holds over B and over V after recoding.
    It kills (E1') for BBCMP's structure and for bh-hhg's structures on S_{0,n} (n ≥ 6) and S_2.
  - `b3-center-first-normal-form-passes-the-germ-condition` (+ proof). B_3 = Mod(S_1^1): the
    Deligne structure is thin but fails (E4), since <Δ> is not normal. Writing Δ² first
    repairs it, with germ group B_3 over its center and quotient PSL_2(Z). This calibrates
    bh-free-08 (b): it holds with a = 2 yet (3) fails.
  - Artifact `gq-bh-bh-free-51-garside-and-mosher-thinness.md`: Mosher arXiv:math/9409209 read at
    source (MSI `gqsrc/bh-free-51/`). The closed-surface structure is non-constructive, so it
    cannot be tested. The once-punctured structure is uncombing blocks followed by L/R parity
    tails.
  - Attempts section on bh-free-21's premise.
- Did NOT land a central-Z-extension theorem: it duplicates
  `odometer-lift-central-extensions-of-v-subgroups-into-2v-tau` and bh-free-08's
  `bhm-corollary-hosts-over-v-are-cover-centralizer-groups`.
- Lesson: rank-one hosts absorb only virtually central cyclic commuting directions. F_2×F_2
  (closed MCG) needs a higher-rank host (bh-free-36).
- 011f21daa: artifact §5, where the product-region obstruction comes from.
  - F_2×F_2 acts on ∂A ⊔ ∂A' with no singular points: the boundary of a longest-first form,
    which is neither regular nor continuous.
  - So the phase singularities are an artifact of BBCMP continuity (compactifications).
  - For closed MCG: build "exploded" Cantor actions that keep commuting boundaries disjoint,
    subject to bh-free-08's Cent_q germ constraint.
- Open crux posted for anyone: an exploded, BHM-good Cantor action of closed Mod(S_g).
- Waiting on board/SYNTHESIS.md (not yet posted).

## Pass 3 (coordinator: exploded Cantor action of closed Mod(S_g), or a higher-rank host)
- Read SYNTHESIS v1 and the boards of bh-free-54, bh-free-61 and bh-mcg.
- 6963cfbdc: `perfect-subgroups-are-locally-trivial-in-abelian-germ-hosts` (+ proof), and Attempt 9
  on `closed-surface-mapping-class-groups-satisfy-boone-higman`.
  - Result: with abelian point germs, f.g. J with H_1(J;Q) = 0 is locally trivial off finitely
    many fixed points.
  - For closed Mod(S_g), g ≥ 4: there are no equivariant curve points carrying twist data. So
    the exploded design with twist poles is dead in V, germ extensions of V, nV, and
    normal-form hosts.
  - Group-theoretic remark: T_d is generated by subsurface groups away from one-holed tori
    around d, so twist data cannot be localized to curve-indexed pieces at all.
- Outcome of the assignment: the exploded rank-one construction is impossible as designed.
  Curve data must be fixed-point-free (odometer-like), sit at finitely many nonabelian singular
  germs, or live in a host with nonabelian point germs. That points to bh-free-54's 𝒯_m as the
  consistent host. Its gate is finite presentation (bh-free-61).
