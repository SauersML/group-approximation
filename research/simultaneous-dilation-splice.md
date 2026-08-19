---
rg: 2
id: simultaneous-dilation-splice
kind: claim
title: Simultaneous dilation of the positive compressors preserves Connes embeddability (RESTATEMENT of the target, not a reduction)
distinct_from:
  positive-core-bernoulli-ce: that is the established foothold — microstates for the core N₀ exist; this is the missing step that extends them over the compressors
  fiber-masa-free-cocycle: that is a structural demand on a from-scratch model of the whole algebra; this starts from an existing honest model of a subalgebra and asks to extend it
  invariant-cartan-completion: that is a rigidity-side target about arbitrary abstract embeddings; this is a construction-side permanence question about one specific extension
artifacts:
  - notes/FALSE_FULL_COMPRESSION_SEMIGROUP_DILATION.md
  - notes/FALSE_POSITIVE_CORE_IS_SOFIC.md
---

Starting from the sofic microstates of `W₀ = (⊕_{X₀} C₂) ⋊ Γ`
(`positive-core-bernoulli-ce`), implement the endomorphisms induced by
`L₊ = SL_d(ℤ) ∩ M_d(ℕ)` by unitary dilators satisfying the finite relations of
`SL_d(ℤ)`, without destroying Connes embeddability. Equivalently: the minimal
simultaneous automorphic dilation `M = W*(N₊, u_s : s ∈ S)` of the positive
core by all the compressors at once is Connes embeddable.

If it holds, `W = (⊕_{G/Γ} C₂) ⋊ G` is hyperlinear, and with
`wreath-not-sofic` that answers Pestov's Question 3.4 negatively. The corpus
states this consequence explicitly as `(FSD20)`.

## RESTATEMENT AUDIT (2026-08-14) — this claim renames the target

Flagged by the team-wide "restatement dressed as reduction" warning and
confirmed by re-derivation. This is the worst of the three cases: the
equivalence needs no established claim at all, because `M` **is** the target
algebra. `notes/FALSE_FULL_COMPRESSION_SEMIGROUP_DILATION.md` `(FSD5)` reads
verbatim

    M = L^∞({±1}^{G/Γ}) ⋊ G = L((⊕_{G/Γ} C₂) ⋊ G),

so "`M` is Connes embeddable" is "`W` is hyperlinear" is
`hyperlinear-wreath-model`. The same document says so in its own outline —
"the remaining obstruction is simultaneous dilation subject to the relations
among different compressors, **equivalently Connes embeddability of (FSD5)**" —
and the node was written anyway. The corpus stated the equivalence and it was
read as a decomposition.

**The route `positive-core-dilation-splice` is therefore not a reduction.**
Its implication is true, the graph is not lying, but the open hole it displays
is the target wearing different notation, and it should not be counted as a
second front.

**No repair is available, and that is worth knowing.** The obvious fix is to
replace this claim by the general permanence principle it instantiates — "the
minimal simultaneous automorphic dilation of a Connes-embeddable algebra along
a family of trace-preserving endomorphisms with prescribed relations is Connes
embeddable". That principle is too strong to be useful: taking `N = ℂ` with
trivial endomorphisms makes the dilation `L(G)` for an arbitrary group, so the
principle implies every group is hyperlinear. Splitting it into the two steps
the corpus names — amalgamated free product over `N₊`, then quotient by the
relations — does not help either, since the second step's target is `M` itself,
so the pair is again equivalent to the target.

## What survives, and it is not nothing

The genuine content is `positive-core-bernoulli-ce`, which is established and
is not a restatement: it exhibits real matrix microstates for a real
subalgebra. What it buys is a **localization of the difficulty**, not a
reduction of it — the core is discharged unconditionally, so nothing is left
but the dilation. That is worth recording and is why these nodes are kept
rather than deleted. It is not progress toward the target in the sense the
kernel means by a route.

## Why it is not routine, stated exactly

For a **single** compressor the dilation is an inductive limit followed by a
crossed product by `ℤ`, and both operations preserve Connes embeddability. The
construction does not iterate. Adjoining several free dilators produces
amalgamated free products **over the nonamenable core `N₊`**, and then imposing
the actual `SL_d(ℤ)` relations among the dilators is a quotient. Neither
operation is known to preserve Connes embeddability in this generality. The
corpus calls this the simultaneous-coherence gate.

## What the gate is, in the literature's own terms

The first half of the gate is a named open problem, and the identification does
not appear to have been made in this corpus before. Brown–Dykema–Jung
Corollary 4.5 gives `ℳ₁ *_B ℳ₂ ↪ R^ω` when the `ℳᵢ` are and `B` is
**hyperfinite**. Gao–Junge, arXiv:2012.07940, record the general case as open,
verbatim: *"the problem of given M and N embeddable, whether ∗_N M is
embeddable as well remains open"*, and as their Problem 1 in the QWEP form,
noting also that *"the 'position' of N inside M is important."* Here `B = N₊`
is nonamenable by construction, so the gate's free-product half **is** that
open problem, at a specific and unusually structured base.

That reframing cuts both ways and both are worth recording. It means the gate
will not fall to a routine permanence lemma — if it did, it would settle a
standing question in operator algebras. It also means the wreath candidate is
now attached to a problem that has independent attention, with a concrete base
algebra on which the general question can be tested, rather than sitting alone.

## Routes that are already closed off

The Ore shortcut is dead: the full compressor semigroup is neither left nor
right Ore and admits no cofinal Ore subsemigroup
(`notes/FALSE_COMPRESSION_SEMIGROUP_ORE_NO_GO.md`, `notes/AGENDA.md`). So the
several-compressor case cannot be reduced to the one-compressor case by
directing the semigroup. `notes/FALSE_FULL_COMPRESSION_SEMIGROUP_DILATION.md`
also records that the principal-bundle constructions solve the relation-imposing
step only after forgetting the common nonamenable core, and that the
one-compressor construction solves the first two steps only conditionally on
embeddability of that core — which `positive-core-bernoulli-ce` now supplies
unconditionally. **The missing theorem is precisely their compatible splice**,
and with the core discharged it is the only thing missing.
