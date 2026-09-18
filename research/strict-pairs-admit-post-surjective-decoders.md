---
rg: 2
id: strict-pairs-admit-post-surjective-decoders
kind: claim
title: A group carrying a strict automaton pair carries one whose decoder is post-surjective
distinct_from:
  post-surjective-decoders-convert-strict-pairs-to-dual-failures: that proves what a post-surjective decoder gives and when decoders are post-surjective; this asks for the missing existence step for arbitrary nonlinear strict pairs.
artifacts:
  - research/artifacts/gk3-dual-surjunctivity-2026-09-14.md
---

**OPEN.** Suppose `G` carries an injective, non-surjective automaton over some
finite alphabet. Then `G` carries a strict pair `(τ, σ)`, over some possibly
different finite alphabet, whose decoder `σ` is post-surjective.

**What is proved** (`post-surjective-decoders-convert-strict-pairs-to-dual-failures`):
- **(b)** every decoder is post-surjective at configurations asymptotic to the image `Y` of the encoder;
- **(c)** affine decoders over abelian alphabets are post-surjective;
- **(e)** configurations carrying a Garden-of-Eden pattern of the encoder infinitely often are never asymptotic to `Y`.

So the whole difficulty sits at configurations with infinitely many
Garden-of-Eden occurrences. There the decoder's local rule off the language
of `Y` is free, and a proof must choose it so that finite output changes lift
to finite input changes.

**Consequence.** With the conversion claim this gives
`dual-surjunctive-groups-are-surjunctive`. Over any dual surjunctive group,
including every sofic group, no strict pair has a post-surjective decoder.

**Reduction (2026-09-14, gk3-post-surjective-decoders).**
- **Where the difficulty really is.** `decoders-lift-changes-away-from-infinite-defect-chains` narrows
  it further. Every decoder is a retraction onto `Y` read through the encoder, and every retraction
  lifts a finite change by overwriting the finite defect components touching it. So only changes
  adjacent to an infinite adjacency component of the defect set need the free rule. The sparse
  configurations of (e) are not an obstruction by themselves.
- **Two routes are dead.**
  - Conjugate full shifts of unequal size would give a post-surjective decoder, but they never exist
    (`full-shifts-with-different-alphabets-are-not-conjugate`).
  - Affine decoders exist exactly when direct finiteness fails
    (`disjoint-footprint-decoders-force-kaplansky-failure`).
- **Artifact.** `research/artifacts/gk3-post-surjective-decoders-2026-09-14.md`.

## Attempts

- **2026-09-17, swarm-0917-w7-w7-gs-last1 [reframing]: the domain restriction bypasses this hole.** This claim
  stays OPEN.
  - `strict-pairs-give-dual-failures-on-bounded-defect-domains` (ESTABLISHED) shows that every decoder, with
    no choice made, is strongly post-surjective and not pre-injective on
    `X_R = {x : every defect component has at most R sites}`.
  - `X_R` is a proper, strongly irreducible SFT.
  - So this claim is exactly the problem of extending some `σ|_{X_R}` from `X_R` to all of `A^G` while keeping
    post-surjectivity. The only configurations involved are those with an infinite (or large) defect
    component.
  - The new route `gottschalk-via-proper-domain-duality` does not need this claim. It replaces it, together
    with the full-shift dual statement, by one open step: `proper-sft-domains-admit-no-dual-failures`.
  - Artifact: `research/artifacts/bounded-defect-domain-duality-2026-09-17.md`.
- **2026-09-18, swarm-0917-w12-w12-gs-last1 [calibration]: free output tracks give no gain unless the decoder
  rewrites the track. DEAD as an approach; this claim stays OPEN.**
  - *Idea tested.* Extend `σ|_{X_R}` by adding a free track `C`. Use the encoder `τ' = τ × κ` on `(A × C)^G`, with
    `κ` a bijective automaton of `C^G`. At sites near a large defect component, let the decoder read its
    `A`-output off the track, and elsewhere use `σ`.
  - *(a) The cross-alphabet version is trivial, so it proves nothing.* Take `|C| ≥ 2`. The projection
    `(A × C)^G → A^G` is post-surjective and not pre-injective over every group. So a free-track map into `A^G`
    carries no information. Dual failures must be self-maps of one full shift, and PSD must stay inside one
    alphabet, as its statement does.
  - *(b) Slice lemma (proved here, elementary).* Suppose `σ'` is a post-surjective decoder of `τ × κ` whose
    track output is `κ^{-1}(c)` at every input `(y, c)`. Fix `c_0 ∈ C` and let `c_1^G = κ(c_0^G)`, which is
    constant because `κ` is equivariant. Define `ρ(y) = σ'_A(y, c_1^G)`.
    - `ρ` is an automaton on `A^G`, because `c_1^G` is shift-invariant.
    - `ρ(τx) = x`, from `σ'(τx, κc) = (x, c)` with `c = c_0^G`.
    - `ρ` is post-surjective. Let `z ~ ρ(y)`. Then `(z, c_0^G) ~ σ'(y, c_1^G)`, so post-surjectivity gives some
      `(y', c') ~ (y, c_1^G)` with `σ'(y', c') = (z, c_0^G)`. The track output forces `κ^{-1}(c') = c_0^G`, so
      `c' = c_1^G`, and therefore `ρ(y') = z` with `y' ~ y`. The strong form (lift constant `Φ`) carries over
      unchanged.
    - So any such `σ'` already hands over a same-alphabet post-surjective decoder of `τ` itself.
  - *Where every member dies (named invariant: the constant-track slice).* Every construction in which the
    track is only read, never rewritten, is exactly as hard as this claim for `τ`. This covers track doubling,
    ignored tracks, and "use `w(g)` at bad sites, `σ` at good sites". A free track can help only if the decoder
    changes the track output at defect sites, as the absorption decoders of
    `absorptions-give-post-surjective-strict-pairs` do with their absorbed coordinate.
    - Then a site-wise symbol count reappears. At a site whose window meets an infinite defect component, the
      output ranges over `|A||C|` symbols. The only input that can be changed without moving the defect set is
      the track, which has `|C|` symbols.
    - Over a nonamenable `G` this count is not a contradiction, because lifts may use `gΦ`. It only says the
      missing factor `|A|` must be moved between sites, which is the Hilbert-hotel content of an absorption.
  - *Net effect.* The free-track route to this claim collapses to `strict-automata-yield-topological-bernoulli-absorptions`
    (the track must absorb) or to the same-alphabet problem (the track is only read). It opens no new route.
