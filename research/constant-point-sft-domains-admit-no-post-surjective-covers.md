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
