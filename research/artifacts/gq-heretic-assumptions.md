# Heretic pass on GL_n(Q) hosts: three shared assumptions, denied

Lane `gq-heretic`, 2026-09-17. Target: `gl-n-q-embeds-in-fp-simple-group` (G). This pass read the lane boards at
~22:50 CDT (germ/VA, type (A)/twisted Brin–Thompson, piecewise projective, rings/Leavitt, unions/adelic) and the
landed nodes `lifts-add-no-unipotent-divisibility` (970b120c7) and root obstruction O4 (2688d4128).

Every popular approach makes three assumptions without stating them. For each one below: the assumption, the
denial, and what happens to the denial.

## H1. The host is of Thompson type (acts on a Cantor set, circle or line by local moves)

- **Shared by:** every family on the boards (germ extensions of V, VA-type groups, nV and twisted Brin–Thompson
  groups, Röver–Nekrashevych groups, piecewise-projective groups, Leavitt unit groups, which contain V).
- **Denial:** take a finitely presented simple group from the non-Thompson world. The survey (§4.1) names exactly
  two such families: the Burger–Mozes groups (lattices in products of trees) and the Kac–Moody groups used by
  Caprace–Rémy (twin building lattices over finite fields). Other lattice-type groups acting on CAT(0) complexes
  also qualify.
- **Verdict: DEAD.** See `proper-semisimple-cat0-groups-contain-no-gl-2-q`. A group acting properly by semisimple
  isometries on a CAT(0) space has no distorted cyclic subgroup (the axis argument). `BS(1,2) <= GL_2(Q)`
  therefore rules out, for every `n >= 2`:
  - all proper cellular actions on CAT(0) complexes with finitely many shapes (Bridson 1999);
  - all proper actions on CAT(0) cube complexes of any dimension (Haglund, arXiv:0705.3386).
  Both named families are excluded. Amenable hosts are excluded too, because `F_2 <= SL_2(Z) <= GL_2(Q)`. This rules
  out, for example, commutator subgroups of topological full groups of minimal subshifts.
- **Lesson:** H1 is not a habit. By present knowledge it is forced. The host must be a group of homeomorphisms of a
  Cantor-like space (or line/circle), not proper on any CAT(0) space, and with distorted cyclic subgroups (O4).

## H2. Divisibility comes from roots of a central element (the T̄ mechanism)

- **Shared by:** `gq-tbar-lift-n`, `gq-pp-lift`, and the Q-inside-VA lanes. The one fully explicit Q-embedding
  (Belk–Hyde–Matucci) gets `Q` as the preimage in the central extension T̄ → T of a locally finite `Q/Z <= T`.
- **Denial:** divisibility must be *non-central*. The centre of `GL_n(Q)` is `Q^x · I`, which is `{±1} × Z^(∞)` and
  contains no nontrivial divisible subgroup. So every copy of `(Q,+)` in `GL_n(Q)` meets the centre trivially.
- **Verdict:** the central mechanism is DEAD. This is landed as `lifts-add-no-unipotent-divisibility`: the base of
  any central lift must already contain the unipotent `Q`. O4 independently kills VA, T̄ and A.
- **What remains live: divisibility by conjugation.** In `GL_2(Q)`, `u = e_12(1)` is conjugate to `u^p` by
  `diag(p,1)` for every prime `p`, and the conjugators commute. So any host needs an element conjugate to its `p`-th
  power for every prime `p`, through a free abelian group of conjugators of infinite rank (up to the kernel of the
  action). That is exactly the configuration `Aff(Q) = Q ⋊ Q^x`, so `Aff(Q)` is the right minimal test group for
  every family.
- **Consistency:** this mechanism forces exponential distortion (`|u^(p^k)| <= 2k|t_p| + 1`), which matches O4's
  requirement that the host have distorted cyclic subgroups. A host like VA with only undistorted cyclic subgroups
  cannot supply it.
- **Spark:** Kojima–Sheng (arXiv:2603.18410v3) put `(Q,+)` in `nV` for `n >= 2`. Two questions follow:
  - Is their `Q` normalized there by elements acting as multiplication by every prime?
  - Failing that, can a twisted Brin–Thompson overgroup add such conjugators?
  A positive answer is the first step toward `Aff(Q)`. This belongs to `gq-bt-kojima` and `gq-affq`.

## H3. GL_n(Q) acts naturally (linearly or projectively) on the host's space

- **Shared by:** `gq-solenoid`/`gq-adelic` (A_f^n), `gq-typeA-projective` (P^{n-1}(Q)), `gq-houghton-q` (Q^n),
  `gq-pp-psl2q`/`gq-pp-higher` (RP^{n-1}).
- **Denial:** the embedding may be *wild*, meaning conjugate to the natural action only by a non-algebraic
  homeomorphism. There is precedent twice over:
  - Thurston's model of `T` as piecewise-`PSL_2(Z)` maps of `RP^1` is conjugate to the dyadic PL model by the
    Minkowski question-mark function;
  - in Belk–Hyde–Matucci, the rational rotations inside `T` are dyadic PL maps topologically conjugate to rotations,
    not rotations.
- **Verdict: LIVE, as a warning to the obstruction lanes.** Bounded-denominator results, such as `gq-pp-psl2q`'s
  "a f.g. group of piecewise `PSL_2(Q)` maps contains only `PSL_2(Z[1/S])`", kill only natural embeddings. To kill a
  family, an obstruction must hold for abstract embeddings. `gq-pp-psl2q`'s rotation-number rigidity programme,
  `N(D) = C(D)` for divisible `D`, is of that abstract kind. So is O4.
- Constructions need not respect the natural action either. The Aff(Q) configuration of H2 is the invariant
  statement of what a wild embedding must still contain.

## Summary for the swarm

1. Non-Thompson hosts are dead (H1, landed obstruction). All effort belongs on Cantor/line dynamics with distorted
   cyclic subgroups.
2. Central-root divisibility is dead (H2, `lifts-add-no-unipotent-divisibility`). The live requirement is an
   element conjugate to its p-th power for all primes p, through commuting conjugators: the Aff(Q) configuration.
3. Natural-action obstructions do not settle anything (H3). Obstructions must be abstract; constructions may be wild.
