# Collapse transfer: why local engines cannot prove Boone–Higman, and what must replace them

Lane bh-invent-18 (inventor, free choice), 2026-09-18. This is a strategy artifact. The theorem it
rests on is `stabilizer-engines-need-torsion-vertex-groups` (lane proof, not reviewed).

## 1. The choice and why

I set out to build the mechanism I thought most likely to prove Boone–Higman outright: a *local
engine*.
- **The design.** Place the hard input `B` at one point of a Cantor groupoid, as the full
  isotropy of an infinite emitter, with finite presentation coming from finitely many local rules
  around it.
- **The appeal.** Such an engine obeys the carrier principle for free: complexity is carried by
  `B`, the germ group. It respects the Kazhdan filter, since the input acts on no tree or building
  and sits at a point. It needs no scaling. And simplicity is free, because the derived full group
  of a minimal purely infinite groupoid is simple.
- **The candidate.** That is exactly the stabilizer engine `D(F_B)` of `Z/k * B`, and by
  Clapham plus doubling it would suffice to do this for finitely presented decidable `B`.

Pushing the design to its limit shows that it is impossible. So the invention became the
obstruction mechanism below, and it points to where a proof has to live.

## 2. The mechanism: collapse transfer

**Setting.** A host `H(B)` is *locally determined* by its input `B` if two data depend only on
bounded balls of `B`:
- its elements have finite descriptions (tables), and composing them is a finite computation;
- the phase space is such that which finite patterns occur (emptiness of cylinders) is decided
  locally.

**Two families of fake hosts** then agree with `H(B)` on every bounded computation.
- **Approximations** (bh-invent-15, bh-emitter-a/b, bh-free-56). Replace `B` by nearby marked
  groups: covers and quotients. Finite presentation turns every fake into a quotient, and
  simplicity forbids that. So `B` must be *isolated*.
- **Collapses** (new here). Keep `B`, but make a deep subgroup `K` (one avoiding a large ball)
  into the stabilizer of the base branch, via `B *_K (K × A)`.
  - No bounded pattern changes.
  - But an element `k ∈ K` that moved the base branch far away now fixes it.
  - One transposition of branches then gives a relation that holds in `H(B)` and fails in the
    fake unless `K` is normal.
  - So every deep subgroup is normal, and with isolation there are none.

**Output.** An fp engine needs its vertex group to be an fp torsion group with finitely many
elements of prime order. No infinite such group is known.
- So the engine is infinitely presented over `Z` (Reid), `F`, `T`, `V`, every `B` containing
  `Z`, and every infinite simple `B`.
- The open conjecture `isolated-vertex-groups-have-fp-stabilizer-engines` is refuted, and so are
  the premises of the stabilizer-engine routes (`boone-higman-via-*-stabilizer-engines`).

**The single decisive lemma** of the mechanism is the transport lemma for collapses: `B → B *_K (K × A)`
is injective on `4r`-balls, and the tree combinatorics (edges, atoms, emptiness) agree up to
radius `2r`, whenever `K ∩ Ball(4r) = 1`. It is proved in the node. Everything else is one
commutator.

## 3. What the mechanism says about all hosts

- **Regular local actions are the enemy.** Where the isotropy acts *regularly* on local branches,
  every deep subgroup can be collapsed onto a branch stabilizer. This is the same phenomenon as
  the pair-orbit condition in twisted Brin–Thompson groups: `SV_G` is fp only if `G ↷ S` has
  finitely many orbits on pairs. Regular actions have infinitely many "deep pairs".
- **So pair-orbit finiteness is not created locally** (a principle; proved here only for
  free-product engines). An emitter can only pass on a
  homogeneity its isotropy already has, which is PBH for the isotropy, so it is circular.
- **Only two known sources create homogeneity:**
  - (i) finite branching with self-similarity: finitely many cone types, as in `V` and every
    Li / Stein–Farley host;
  - (ii) a global constraint that fakes cannot satisfy: an SFT whose locally admissible patterns
    do not all extend, so that emptiness of cylinders is not local and neither approximations nor
    collapses transport.
- **Where decidability must enter.** Decidability of the input has to be consumed by a
  **non-local extension problem**, never by local rules around the input. This fits Jeandel's
  theorem (strongly aperiodic SFTs force a decidable word problem) and the fp ⇒ rigidity theorem
  on main.

## 4. My bet for the proof, and its decisive lemma

**The route: Track A**, in the form the transfer analysis forces.
- **Carrier.** The input's hardness is carried by a finitely presented acting group `Λ` (Clapham,
  squared).
- **Homogeneity.** It comes from finite branching: the `G_V` factor, with finitely many cone types.
- **Non-locality.** It comes from a minimal, topologically free SFT `X` over `Λ`. Aperiodicity makes
  cylinder emptiness global, and that is exactly what defeats both families of fakes.

**Decisive lemma: (★′) quantum rigidity.**
- **Statement.** For every finitely presented decidable `Λ_1`, the square `Λ_1 × Λ_1` carries a
  minimal, topologically free SFT that is quantum rigid.
- **Why rigidity is the gate.** Existence has literature support (Barbieri–Sablik–Salo,
  self-simulation, M2), and simplicity and type (A) are free. The transfer principle explains why
  rigidity is the right gate: rigidity is the algebraic form of "no fake extension of local
  patterns".

**Why not the finite-type blow-up variant of the engine.** Its emitter is an SFT orbit closure
with an isolated dense orbit, and it is the only engine form left. Collapse transfer does not
reach it, because the collapsed branch set `B/K` carries only the `K`-periodic configurations of
the SFT, whose emptiness is global. Heuristically (not proved), its first job would be to show that those periodic fakes
are empty. That is an aperiodicity statement over `B` itself, so I expect the blow-up to reduce to
Track A's (★′) for `B`.

## 5. Calibrations and next tests

- **Finite `B`.** No deep subgroups exist, and the Higman–Thompson groups `G_{d−1,d}` are fp.
  Consistent.
- **Thompson's `T`.** It has two-sided parabolic germs on `RP^1`, which look like emitters, and it
  is fp.
  - There the parabolic `Z` is not a free factor. No collapse or approximation of it preserves the
    Farey combinatorics: reducing the parabolic changes `PSL_2(Z)` into a triangle group with
    compact vertices.
  - Germs on the two sides are independent (flux), unlike Reid's linked germ.
  - Consistent.
- **Röver/Nekrashevych groups `V_d(G)`.** They are fp over non-fp `G`, because the recursion
  (wreath data) does not transport to approximations or collapses. Consistent: recursion is a
  non-local datum. It is unusable for Boone–Higman only because self-similar inputs are
  residually finite.
- **Next test (for Track A′ and blow-up lanes).** Extend collapse transfer to `A * B` with `A`
  infinite, and to amalgams `A *_C B` whose vertex group acts on `B/C` with infinitely many
  pair-orbits. I expect the same kill whenever `D(F)` is simple with trivial centralizer.
  Compression codings of `Λ_1 * Z` on the plain Bass–Serre boundary would then die for every
  Clapham `Λ_1`, and only SFT-constrained codings survive.

## Lesson for general BH

A host whose local rules read only bounded data of the input receives two kinds of fakes:
approximations of the input, and collapses of its deep subgroups into local stabilizers.
- **Approximations** force isolation.
- **Collapses** force every deep subgroup to be normal.
- **Together** they force an essentially finite input.

This is proved for free-product emitter engines; for other locally determined constructions it is a
principle, not yet a theorem. Either way, no locally determined construction of this kind proves
Boone–Higman. The input's decidability must be
consumed by a non-local extension problem, an aperiodic SFT over an fp carrier. That is Track A,
and its decisive lemma is quantum rigidity (★′).
