---
rg: 2
id: proper-sft-domains-admit-no-dual-failures
kind: claim
title: No proper strongly irreducible subshift of finite type maps onto the full shift by a strongly post-surjective automaton that is not pre-injective
distinct_from:
  every-group-is-dual-surjunctive: that is about automata from the full shift to itself; this is about automata from a proper strongly irreducible SFT inside the full shift onto the full shift. Neither statement is recorded as implying the other.
  strict-pairs-admit-post-surjective-decoders: that asks for a decoder that is post-surjective on the whole full shift; this asks that no automaton on a proper strongly irreducible SFT is strongly post-surjective without being pre-injective.
  dual-surjunctive-groups-are-surjunctive: that transfers the full-shift dual statement to surjunctivity group by group; this proper-domain statement implies surjunctivity of the same group directly, through strict-pairs-give-dual-failures-on-bounded-defect-domains.
artifacts:
  - research/artifacts/bounded-defect-domain-duality-2026-09-17.md
---

**OPEN.**

**Statement.** Let `G` be a group and `A` a finite alphabet. Let `X ⊊ A^G` be a strongly irreducible subshift of
finite type, and let `F : X → A^G` be an automaton (continuous and equivariant). Suppose `F` is strongly
post-surjective with lifts inside `X`, as defined in `strict-pairs-give-dual-failures-on-bounded-defect-domains`.
Then `F` is pre-injective on `X`.

The claim is read group by group: "`G` satisfies the claim" means it holds for every `A`, `X` and `F` over `G`.

**Why it matters.** By `strict-pairs-give-dual-failures-on-bounded-defect-domains`, every group that satisfies
the claim is surjunctive. That result needs no choice of decoder. The route `gottschalk-via-proper-domain-duality`
records this.

**Amenable groups (sketch, not imported verbatim).** For amenable `G` the claim holds vacuously: no such `F`
exists, whether or not it is pre-injective.
- By Doucha–Gismatullin (the line-176 quotation in `research/artifacts/gk3-post-surjective-decoders-2026-09-14.md`),
  a strongly post-surjective automaton onto the strongly irreducible target `A^G` is surjective.
- Factor maps do not raise topological entropy. So `log|A| ≤ h(X)`.
- On an amenable group, a proper subshift of `A^G` has entropy strictly below `log|A|`. That is the standard
  input to the Garden of Eden theorem (Ceccherini-Silberstein–Coornaert).
- These together give a contradiction.

**Caution: strong irreducibility is essential.** On nonamenable groups, SFTs built from arrows (each site
points to `k + 1` disjoint targets through bounded injections) carry post-surjective, non-pre-injective maps
onto full shifts. These SFTs appear not to be strongly irreducible. A strongly irreducible example of this
kind would refute the claim on that group.
- This is the main kill-test. It is recorded in the artifact.
- Refuting the claim on one group does not refute Gottschalk.

## Attempts

- **2026-09-17, swarm-0917-w7-w7-gs-last1 [entropy]: sofic calibration, sketch only. OPEN.** On sofic groups
  surjunctivity is already known, so this is a test of the claim, not progress on Gottschalk.
  - **Plan.** Show that no strongly post-surjective automaton maps a proper strongly irreducible SFT
    `X ⊊ A^G` onto `A^G` at all.
  - **Step (i), entropy deficit.** `X` has sofic topological entropy `< log|A|` along every sofic
    approximation, and `−∞` is allowed. The reason is that a forbidden pattern must be avoided on a positive
    proportion of the sites of good models.
  - **Step (ii), no entropy gain.** Take the arbitrary words that serve as microstates of `A^G`, and pull them
    back one site at a time using the lift constant `Φ`. This should give about `|A|^{(1−δ)n}` microstates of
    `X`.
  - **Where it dies.** Step (ii) edits microstates, not genuine points. The lift lemma holds only for genuine
    points, and transferring it to microstates needs the strong irreducibility of `X` in a quantitative form
    that is not proved.
  - **A strongly irreducible SFT with no microstates would break step (ii).** Such an SFT, on a sofic group,
    with a strongly post-surjective map onto a full shift, is the kill-test.
- **2026-09-17, swarm-0917-w7-w7-gs-last1 [arrow-shifts]: nonamenable test domains. Deferred.** Arrow SFTs give
  post-surjective, non-pre-injective maps onto full shifts, but they are not strongly irreducible. The open
  question is whether a strongly irreducible SFT, for instance a strongly irreducible factor or cover of an
  arrow SFT, can keep the post-surjective map. That question was not attacked.
