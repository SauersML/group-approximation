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

## Attempts

- **Bernoulli measures.** A Bernoulli measure on `A^Δ` is invariant and fully supported, but `A^Δ` is
  not minimal, and a minimal subsystem can be null.
- **Topological models of measured actions.** For amenable groups Jewett--Krieger, in Weiss's form,
  turns a free ergodic action into a uniquely ergodic minimal model. No general form for sofic or
  non-amenable groups was located by this lane; the check was one grep of this graph and no
  literature search.
- **Restricting to the free part.** The free part of `A^Δ` is invariant and conull for Bernoulli
  measures, but it is not compact, so it does not by itself provide a subshift.
