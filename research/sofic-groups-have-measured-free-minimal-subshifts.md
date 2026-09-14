---
rg: 2
id: sofic-groups-have-measured-free-minimal-subshifts
kind: claim
title: Every finitely generated sofic group has a free minimal subshift carrying an invariant measure
distinct_from:
  free-minimal-subshifts-all-rf-iff-virtually-cyclic: that asks which groups have only residually finite free minimal subshifts; this asks for one free minimal subshift with an invariant measure, which is automatic for amenable groups and unclear otherwise.
---

**OPEN.** Every finitely generated sofic group `Δ` admits a free minimal subshift `X ⊆ A^Δ` with a
`Δ`-invariant Borel probability measure.

Free minimal subshifts exist over every countably infinite group (Gao--Jackson--Seward), and for
amenable `Δ` every action on a compact space has an invariant measure, so the statement is automatic
there. For non-amenable `Δ` a minimal action need not have one, as boundary actions show, and the
question is whether some free minimal subshift does.

**Why it is wanted.** With such an `X` and a sofic `Δ`, the orbit relation of `Δ ↷ (X, μ)` is the
natural source of labellings of sofic approximation graphs that are equivariant off a vanishing set.
Those labellings give the rank models that the Folner truncation gives in the amenable case, so they
would extend `amenable-groups-embed-in-simple-kazhdan-linear-sofic` to all sofic inputs. Full support
is free: an invariant measure for a minimal action has full support, so every nonempty clopen set is
hit with positive density, which is what the rank lower bound needs.

**Not needed for rank envelopes (sk-measured-subshift, 2026-09-13, unreviewed).**
- The lamplighter action of `Z/2 ≀ Δ` on `2^Δ` is only topologically free, but it carries the Bernoulli measure.
- Its crossed product has faithful rank models, obtained by counting over colourings of sofic approximation sets
  (`sofic-lamplighter-bernoulli-crossed-products-have-rank-models`).
- That gives `sofic-groups-embed-in-simple-kazhdan-linear-sofic-groups` without this claim.
- This claim stays open as a dynamics question.

## Attempts

- **Bernoulli measures.** A Bernoulli measure on `A^Δ` is invariant and fully supported, but `A^Δ` is
  not minimal, and a minimal subsystem can be null.
- **Topological models of measured actions.** For amenable groups Jewett--Krieger, in Weiss's form,
  turns a free ergodic action into a uniquely ergodic minimal model. No general form for sofic or
  non-amenable groups was located by this lane; the check was one grep of this graph and no
  literature search.
- **Restricting to the free part.** The free part of `A^Δ` is invariant and conull for Bernoulli
  measures, but it is not compact, so it does not by itself provide a subshift.
- **Kerr–Li reduction (sk-measured-subshift).**
  - By the variational principle (Kerr–Li, arXiv:1005.0399, Theorem `T-variational`, quoted in
    `research/artifacts/sk-measured-subshift-lamplighter-rank-envelopes-2026-09-13.md` §1), a subshift `Y` with sofic
    topological entropy `h_Σ(Y) ≠ −∞` carries an invariant measure with nonempty measure microstate spaces along a
    subsequence of `Σ`.
  - Those microstates are the labellings of Theorem SR.
  - So it is enough to find a free minimal subshift with `h_Σ(Y) ≠ −∞`.
- **Bernshteyn 2019 (read at source, arXiv:1802.07123).**
  - For sofic `Γ` there are free subshifts `X ⊆ k^Γ` with sofic entropy at least `h`, for any `h < log_2 k`.
  - There are also free subshifts carrying an invariant measure that is a factor of a Bernoulli shift.
  - Minimality is given only for amenable `Γ`. A minimal subsystem is free and minimal, but it can be null for every
    invariant measure.
- **Elek 2021 (read at source, arXiv:1805.11149).**
  - Free minimal actions with invariant measures exist for every countably infinite group
    (`elek-free-minimal-cantor-actions-with-invariant-measures`).
  - But the construction is a subshift over the infinite alphabet `𝒞 × ∏ F_m`.
  - A finite-alphabet factor keeps minimality and can lose freeness, and a crossed product over an infinite-alphabet
    system is not finitely generated.
