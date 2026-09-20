---
rg: 2
id: constant-point-sft-domains-admit-no-post-surjective-covers
kind: claim
title: No proper SFT containing a constant configuration strongly post-surjects onto the full shift
distinct_from:
  proper-sft-domains-admit-no-dual-failures: that assumes strong irreducibility and concludes pre-injectivity; this drops irreducibility and non-pre-injectivity, assumes a constant point, and concludes non-existence.
  every-group-is-dual-surjunctive: that is about automata on the whole full shift; this is about proper SFT domains with a constant point.
  proper-sft-covers-exclude-finite-orbits-and-sofic-constants: that proves this statement for sofic groups (and for finite-orbit points on residually finite groups); this is the statement for all groups.
artifacts:
  - research/artifacts/constant-point-domain-count-2026-09-17.md
  - research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md
  - research/artifacts/fixed-point-surjectivity-and-free-monoid-calibration-2026-09-18.md
  - research/artifacts/pointed-pre-injective-sections-2026-09-18.md
  - research/artifacts/injective-image-sft-cover-pairs-2026-09-19.md
  - research/artifacts/coset-lift-tube-shifts-2026-09-20.md
---

**OPEN.** Read group by group. Let `G` be a group and `A` a finite alphabet. No SFT `X ⊊ A^G` that contains
a constant configuration admits an automaton `F : X → A^G` that is strongly post-surjective with lifts inside
`X` (same alphabet on both sides).

**Why it matters.** It suffices for `gottschalk-surjunctivity-conjecture` through
`gottschalk-via-constant-point-domains`. The bounded-defect domain `X_R` of a strict pair contains the
constant `τ(a^G)`, since `τ(a^G)` is shift-fixed.

**Known cases.**
- Amenable `G`: a proper subshift has entropy `< log|A|`, and a strongly post-surjective map is onto, so
  entropy would increase. (Standard; sketched in the artifact, §4.)
- Sofic `G`: ESTABLISHED as part 2 of `proper-sft-covers-exclude-finite-orbits-and-sofic-constants`.

**How it can fail.**
- It needs a non-sofic `G` with a proper constant-point SFT and a strongly post-surjective cover.
- The compression and arrow-shift domains of `nonamenable-groups-carry-arrow-shift-strict-automata` cannot
  serve, since they have no finite orbit, hence no constant point.
- Linear sector: a one-sided inverse in `F_q[G]` gives a linear counterexample, whose domain contains `0`
  (bus lemma of `swarm-0917-w8-w8-gs-break`). So the claim at `G` forces `F_q[G]` to be stably finite.
- Whether Gottschalk at `G` implies this claim at `G` is unknown.

## Attempts

- **Scheduled sections (swarm-0917-w8-w8-gs-follow, 2026-09-17; symbolic-dynamics). Gives a decomposition, not a
  proof. Stays OPEN.**
  - *Landed (ESTABLISHED, unreviewed).* `post-surjective-sft-covers-admit-scheduled-sections`. Lifting one output
    site at a time inside `gΦ`, scheduled by a proper colouring of the Cayley graph of a finite `E`, gives a
    continuous equivariant `S(z, κ, x_0) ∈ X` with `F ∘ S = z`. With a Borel greedy colouring of the Bernoulli
    free part, this yields:
    - Rok-max(G) ⇒ this claim at `G`, via `strict-automaton-lowers-bernoulli-rokhlin-entropy`;
    - MCS(G) ⇒ this claim at `G`.
    Both need only a Bernoulli-factor point, respectively an invariant probability, on `X`, not a constant. New
    route `constant-point-domains-via-bernoulli-rokhlin-maximality`. So the chain is Rok-max ⇒ this claim ⇒
    Gottschalk, and this claim reduces to countably infinite finitely generated groups (artifact Lemma 5).
  - *Where the converse dies (Gottschalk ⇒ this claim).* By Proposition C of the artifact, `G` is non-surjunctive
    iff some cover pair has a continuous equivariant section `A^G → X`. So for surjunctive `G` this claim says
    that every constant-point cover pair has a section. The scheduled section needs the colouring:
    - at a constant target `a^G`, a section must return a point fixed by `G`;
    - `F` need not map any constant of `X` to `a^G`;
    - interface sites between lifted and unlifted regions lose their data, and over nonamenable `G` the interface
      is a fixed fraction of the volume;
    - iterates `F^n` gain no capacity, since the alphabet is the same on both sides.
    This is the proper-subshift table case left open in `irs-surjunctivity-iff-pmp-graphing-surjunctivity`.
  - *Dead sub-attempt.* Converting a dual failure into a section by repeatedly replacing lifted blocks with a
    canonical word dies at termination: defects can be pushed to infinity.
  - *What would move this claim.* Either a de-colouring theorem for sections of cover pairs with base-independent
    decoder over the colouring shift, or the Rokhlin hub. Artifact
    `research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md`.
- **Symmetric-locus localization (swarm-0917-w9-w9-gs-last1, 2026-09-18; reframing). Sharpens the de-colouring
  question. Stays OPEN.**
  - *Landed (ESTABLISHED, unreviewed).* `cover-pair-sections-localize-to-the-symmetric-locus`. A cover pair has
    a section iff some seed `ξ : A^G → X` (continuous, equivariant) is exact at `1` on
    `Sym_E = ∪_{e ∈ E \ {1}} Fix(e)`. Off `Sym_E` the non-exact set is compact and `E`-free, so a finite clopen
    greedy colouring schedules Lemma-2 lifts continuously. Artifact
    `research/artifacts/symmetric-locus-seeds-2026-09-18.md`.
  - *Kills the interface-buffer obstruction.* The third bullet of "Where the converse dies" is not an
    obstruction, over any `G`. Theorem S has no lifted/unlifted interface: every non-exact site is lifted.
  - *What is left.* The converse (Gottschalk ⇒ this claim) now asks only for one seed exact on the finitely many
    closed sets `Fix(e)`. On `Fix(e)` this is an `⟨e⟩`-coset lift: lift at all `e^j` at once by an `e`-invariant
    patch, where Lemma 2 fails because `e ∈ E`. At constants it is the first bullet (a constant `b^G ∈ X` with
    `F(b^G) = a^G`). A counterexample to this claim at a surjunctive `G` must be a cover pair in which this coset
    lift is impossible for some `e ∈ E \ {1}`.
- **Fixed-point deficiency and free-monoid calibration (swarm-0917-w9-w9-gs-follow, 2026-09-18; calibration).
  This is a class kill plus a calibration. Stays OPEN.**
  - *Landed (ESTABLISHED, unreviewed).* `cover-pair-sections-force-fixed-point-surjectivity`. A section forces
    `F(X ∩ Fix(H)) = Fix(H)` for every `H`, so the constant map `φ` must be a permutation of `A`.
  - *Class kill.* On a pair with constant deficiency `D = A \ φ(C_X) ≠ ∅`, every section, seed, de-colouring or
    `⟨e⟩`-coset-lift construction dies at a constant target `a^G` with `a ∈ D`.
    - Products, shears, restrictions, composites and recodings cannot repair `D`, since deficiency pulls back along
      morphisms of pairs.
    - The pairs the route feeds in, `(X_R, σ)`, have the section `τ`, so `D_H = ∅`. The fragment of this claim that
      the route uses is therefore equivalent to Gottschalk, and the deficient fragment is off-route.
  - *Calibration.* The free monoid `{a,b}*` is surjunctive and residually finite. It carries a constant-point cover
    pair `X = {x(wb) = 0}` with `F(x)(w) = x(wa)`, which is SI, not pre-injective, and has `D = {1}`.
    - So the monoid analogues of this claim, of PSD, of the finite-orbit exclusion and of `Gottschalk ⇒ this claim`
      are all false.
    - Any proof of this claim, or of needs 36774ad3 and 06d50d0e, must use invertibility of translations.
  - *What is left.* The group question: does any (non-sofic) group carry a cover pair with `D ≠ ∅`? If one does, it
    refutes this claim. If none does, this claim is equivalent to its fixed-point-surjective fragment. Artifact
    `research/artifacts/fixed-point-surjectivity-and-free-monoid-calibration-2026-09-18.md`.
- **Host change (swarm-0917-w13-w13-gs-follow, 2026-09-18; host-geometry). This is a class kill plus one
  relaxation. Stays OPEN.**
  - *Landed (ESTABLISHED, unreviewed).* `cover-pair-sections-pull-back-along-retraction-data`.
    - Sections pull back along any `G`-equivariant retraction datum `(ι, π, β)`.
    - Inducing a pair to a supergroup `G' ≥ G`, taking products with any cover pair, and recoding all have such a
      datum. So `Ind(X, F)` has a section iff `(X, F)` does.
  - *Class kill (need 06d50d0e).* Moving a CP counterexample to a larger host (`G × K`, `G * K`, extensions,
    wreath products) never creates a section, even when the new host is non-surjunctive.
    - Invariant: existence of a section.
    - Dying step: by Proposition C a counterexample over surjunctive `G` has no section, and T1 pulls any section
      back.
    - So a proof of `Gottschalk ⇒ CP`, whether at one group or over all groups, must build its non-surjunctivity
      witness from a pair with no `G`-equivariant retraction to `(X, F)`. This extends F2 of
      `cover-pair-sections-force-fixed-point-surjectivity` from deficiencies to sections, and from one group to a
      change of host.
  - *Relaxation (T3).* Proposition C holds with `H`-equivariant sections, for any finite-index `H ≤ G`. So the
    `⟨e⟩`-coset lift of need 06d50d0e is needed only for `e ∈ H \ {1}` of the recoded memory set, for some
    finite-index `H`.
    - Constants survive the relaxation, so `D = ∅` is still needed.
    - It gives nothing for groups with no proper finite-index subgroup, which include every infinite simple
      candidate.
- **Pointed pre-injectivity (swarm-0917-w14-w14-gs-last1, 2026-09-18; symbolic-dynamics). This is a class kill, an
  equivalence and a new decomposition of the converse gap. Stays OPEN.**
  - *Landed (ESTABLISHED, unreviewed).* `pointed-pre-injective-cover-pairs-admit-sections`.
    - Theorem P: if `F` is injective on `Fin_c(X) = {x ∈ X : x ~ c^G}` for one constant `c^G ∈ X`, then the unique
      pointed lifts form a cellular automaton with memory `Φ^-1`. This automaton extends by density to a section,
      so `G` is not surjunctive.
    - Locality holds because a lift at a site `g ∉ Φ^-1` writes only on `gΦ ∌ 1`, and uniqueness makes the result
      independent of the route. No colouring, seed or symmetric locus is involved.
    - Theorem P' does the same for `H`-fixed points, `H` of finite index.
  - *Class kill.*
    - Invariant: injectivity on the asymptotic class of a finite-orbit point.
    - Dying step: Theorem P, steps 2–4, followed by Proposition C.
    - Consequence: over a surjunctive `G`, every cover pair collides on `Fin_p(X)` at every finite-orbit point
      `p`. So every counterexample to this claim at a surjunctive group has two distinct finite perturbations of
      each of its constants with the same image.
    - Pre-injective, partial-conjugacy and reversible-cover candidates are dead.
    - Deficient pairs (`D ≠ ∅`) collide at every constant, over every group.
  - *Equivalence.* This claim at `G` is equivalent to "every constant-point cover pair over `G` is pre-injective".
    Restricted to strongly irreducible domains, it is equivalent to `proper-sft-domains-admit-no-dual-failures`
    restricted to constant-point domains.
    - Proof: a pre-injective pair gives a section, hence a strict pair, hence the non-pre-injective `(X_R, σ)`,
      which contains the constant `τ(a^G)`.
    - So the two Gottschalk routes coincide on constant-point SI domains.
  - *Decomposition (Theorem Q).* A pair has a section iff it has a pointed pruning. A pointed pruning is a closed,
    invariant, lift-closed `X' ⊆ X` through a constant, on whose class `F` is injective.
    - So need 36774ad3 is exactly PRUNE: remove colliding perturbations while keeping lifts.
    - PRUNE fails on deficient pairs, so a proof must first give `D = ∅`.
  - *Also.* `G` is non-surjunctive iff some proper closed subshift through a constant carries a strongly
    post-surjective map that is injective on that constant's class. Take `τ^-1` on `τ(A^G)`. That domain is only
    sofic, and the finite-type version is open.
  - Artifact: `research/artifacts/pointed-pre-injective-sections-2026-09-18.md`.
- **Injective images are SFT pairs (swarm-0917-w15-w15-gs-follow, 2026-09-19; calibration). This closes the C3
  finite-type gap and splits CP into Gottschalk plus a colliding surplus. Stays OPEN.**
  - *Landed (ESTABLISHED, unreviewed).* `injective-automaton-images-are-sft-cover-pairs`.
    - For an injective `τ` with memory `S`, `Y = τ(A^G)` is an SFT with window `ST`, where `T` is a memory of
      `τ^-1`. `Y` is strongly irreducible, contains every constant, and has `D = ∅`. `(Y, τ^-1)` is a bijective
      cover pair with `Φ = S^-1`.
    - The w14 remark "that domain is only sofic, and the finite-type version is open" is closed.
  - *Theorem II.* `G` is non-surjunctive iff some proper constant-point SFT cover pair is injective on one
    constant's class, iff some proper SI SFT cover pair through every constant is bijective.
  - *Theorem III (sharpens Theorem Q).* A pair has a section iff `F` maps some subshift `X' ⊆ X` bijectively onto
    `A^G`. Such an `X'` is automatically a strongly irreducible SFT through every constant. So PRUNE (need
    36774ad3) asks for an SFT conjugacy subsystem.
  - *Split.* `CP(G) ⟺ Gottschalk(G) ∧ CP_col(G)`.
    - `CP_col` says no proper constant-point SFT pair collides at every constant.
    - The bijective fragment `CP_bij` of this claim is exactly Gottschalk.
    - `CP ⇒ Gottschalk` needs one line, with no decoder and no bounded-defect domain.
    - Either conjunct fails on its own. The pair `(τ(A^G), τ^-1)` refutes `CP_bij` only, and the free monoid
      refutes the analogue of `CP_col` only.
  - *Class kill.*
    - Invariant: pointed injectivity (bijective, pre-injective or pointed-injective pairs).
    - Dying step: Theorem II.
    - Consequence: any "proof of CP" that handles only such pairs is a restatement of Gottschalk, not a
      reduction. The only content CP adds beyond Gottschalk is `CP_col`, which the route never uses.
  - *What is left.* `CP_col` at surjunctive nonsofic groups, i.e. colliding pairs, deficient or not. Spark:
    iterates `(X ∩ F^-1X, F^2)` are cover pairs, and `X_∞ = ∩ F^-n X` is a lift-closed self-cover. Artifact
    `research/artifacts/injective-image-sft-cover-pairs-2026-09-19.md`.
- **Locality and hyperbolic transplant (swarm-0917-w17-w17-gs-pull, 2026-09-19; host-geometry). This is a
  reduction plus a class kill. Stays OPEN.**
  - *Landed (ESTABLISHED, unreviewed).* `cover-pair-failures-have-finite-partial-table-witnesses` (Theorem L).
    - A failure of this claim, of `CP_col` or of NPE at `G` has a finite `K ⊆ G`. The failure recurs at every
      group into which `K` embeds partially, i.e. injectively and multiplicatively on `K`.
    - Strong post-surjectivity reduces to one single-site lift on the finite window `Φ ∪ ΦW^-1W ∪ ΦM^-1M`.
    - The only global ingredient, admissibility in `X`, is replaced by admissibility on one compactness set `L`.
    - Consequences:
      - all three properties are local, hereditary, marked-closed and colimit-closed;
      - failures occur at finitely presented groups;
      - LEF and residually finite groups satisfy all three by counting, with no soficity used;
      - over all groups, this claim is equivalent to `Gottschalk(U) ∧ CP_col(U)` for the one fixed tester `U` of
        `universal-all-group-subgroup-colimit-class-tester`.
  - *Landed (ESTABLISHED, unreviewed).* `cp-failures-transfer-between-hyperbolic-and-leh-groups`. This claim fails
    at some hyperbolic group iff it fails at some LEH group, e.g. `B(m, N)` or a lacunary hyperbolic group. That
    holds iff one fixed torsion-free Kazhdan hyperbolic `T` has a Kazhdan, finite-quotient-free hyperbolic quotient
    where it fails. The same holds for `CP_col` and NPE.
  - *Class kill (model transfer).*
    - The approach: prove CP on a model class `C` and move it by locality, i.e. partial embeddings, marked limits
      or colimits.
    - Invariant: local embeddability into `C`.
    - Dying step: it reaches all groups iff `U` is locally embeddable into `C`. `U ⊇` Thompson's `F`, which is not
      LEH. So `C` equal to finite, residually finite, LEF, hyperbolic or LEH groups all die at `U`.
    - Even "CP at every hyperbolic group" would leave this claim open over all groups, as far as locality can tell.
  - *What is left.* Exactly one group: `CP_col(U)` for surjunctive `U`, or a counterexample there. A proof needs a
    model class into which `U` embeds locally (it contains all finitely presented groups), or a non-local
    argument. Needs 36774ad3 and 06d50d0e are unchanged, but they may now be attacked at `U` alone.
- **2026-09-20, swarm-0917-w21-w21-gs-last1 [symbolic-dynamics]: the coset lift on one tube; tube-internal
  lifts are dead. This claim stays OPEN.** Artifact: `research/artifacts/coset-lift-tube-shifts-2026-09-20.md`.
  - *Target.* Need 06d50d0e: the `⟨e⟩`-coset lift of Corollary S4 (`cover-pair-sections-localize-to-the-symmetric-locus`).
  - *Landed (ESTABLISHED, unreviewed).* `coset-lifts-are-tube-sft-fixed-points`. Fix `e ∈ E \ {1}` of infinite
    order, `z ∈ Fix(e)` with `a = z(1)`, `x ∈ X ∩ Fix(e)` and a finite `K ⊇ Φ`.
    - The repairs of `x` supported on `⟨e⟩K` that are exact along `⟨e⟩` form a nonempty `Z`-SFT `Y_K`. It is
      nonempty by sequential single-site lifts and compactness, and `e` acts on it as the shift.
    - `e^p`-invariant repairs always exist, with `p ≤ |A|^{D|K|}` uniformly in `z`.
    - `e`-invariant repairs are exactly the shift-fixed points of `Y_K`. Whether one exists is a clopen, local test.
  - *Class kill (tube-internal coset lifts).*
    - The class: arguments for the coset lift that repair inside one tube and use only the one-dimensional axioms
      of the tube system. The axioms are:
      - a `Z`-SFT;
      - a strongly post-surjective code with lifts;
      - a fixed point, namely `x` itself;
      - a nonempty fibre with bounded-period points.
    - This covers entropy, Garden-of-Eden and period arguments along `⟨e⟩`.
    - Invariant: the number of shift-fixed points of the fibre `π^-1(a^Z)`, i.e. the trace of the fibre transition
      matrix.
    - Dying step: extraction of period `1`.
    - Witness: a phase-alternation tube (2-block SFT, 1-block code, single-site lifts) with fibre traces
      `tr M_a = 0` and `tr M_a^2 = 6`. It is checked by machine in `experiments/coset-lift-tubes-2026-09-17/`. The
      same example on `Z/n` kills the finite-order case.
  - *New decomposition of the tube-repair route to need 06d50d0e.* The route has two prerequisites, each of which
    can fail on its own. They are sufficient for the route, not necessary for a section, since a section need not
    arise from tube repairs of a given seed.
    - (a) The pointwise fixed-point test of T5 passes at every `(z, ξ(z))` for some finite `K`. The phase tube shows
      that tube axioms cannot give this.
    - (b) The local repairs at the cosets `h⟨e⟩`, `h ∈ C(e)`, can be scheduled together. Exactness on `Fix(e)`
      forces exactness on the whole centralizer `C(e)`, by (∗) of Theorem S, and not only on `⟨e⟩`.

    Part (b) is only sketched, not proved. For central `e`, (a) and (b) together are a `G/⟨e⟩`-equivariant
    section of the fold `X ∩ Fix(e) → A^{G/⟨e⟩}`. The fold is not a cover pair, because a one-site change
    downstairs is a coset change upstairs.
  - *Where it dies.* At period `1`. Any proof of need 06d50d0e must use `G` across the tube, through unbounded `K`
    or the `C(e)`-coupling. For a given seed, prerequisite (a) fails exactly when the fibre over `a^Z` has no
    shift-fixed point for every `K`, i.e. a phase-type tube at every width at one point of `Fix(e)`.
