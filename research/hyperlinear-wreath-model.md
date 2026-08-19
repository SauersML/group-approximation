---
rg: 2
id: hyperlinear-wreath-model
kind: claim
title: Construct a hyperlinear model of the wreath candidate
distinct_from:
  wreath-not-sofic: same candidate group, opposite directions — this asks to CONSTRUCT microstates; that asks to REFUTE soficity
  fiber-masa-free-cocycle: that is one ingredient of one architecture (a fiber cocycle with no invariant MASA); this is the whole goal, by any means
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

Construct microstates for the wreath candidate in which the `Γ`-pieces
genuinely have no consistent size — a model witnessing the compression
inside `R^𝒰` (notes/OBSTRUCTIONS.md §5, "Flexibility").

All *represented* constructive approaches are ruled out (see the approach
list), but **no exhaustiveness finding exists**: the no-gos kill
constructive methods and none kills abstract existence. This goal is OPEN,
not refuted.

The candidate is pinned in `wreath-not-sofic`:
`W = (⊕_{G/Γ} ℤ/2ℤ) ⋊ G` for Kun–Thom's Theorem E pair
`Γ = EL_r(𝔽_q[x₁,…,x_d]) ≤ G = EL_r(𝔽_q[x₁^{±1},…,x_d^{±1}]) ⋊ SL_d(ℤ)`,
`q` a prime power, `r, d ≥ 3`.

## The goal in operator-algebra form

Because the lamp group is abelian, Fourier transform identifies
`L(⊕_{G/Γ} ℤ/2ℤ) = L^∞({±1}^{G/Γ})`, so

    L(W) = M_KT = L^∞({±1}^{G/Γ}) ⋊ G,

the generalized Bernoulli crossed product. `IsHyperlinear` as defined in this
repository uses unitary models with Hilbert–Schmidt separation `2 − ε`, and for
unitaries `‖u − v‖₂² = 2 − 2 Re τ(v^*u)`, so the separation clause forces the
limit trace to be the canonical one. The claim is therefore equivalent to
Connes embeddability of `M_KT`, and that is how the toolkit below is scored.

## Ideas

The tools for proving `R^𝒰`-embeddability abstractly are thin; a genuinely
new idea is needed here, not a variation on the eight dead architectures.

Verdicts on the abstract-embeddability toolkit follow, from a 2026-08-14 pass
in which every statement was read verbatim in its authors' own source
(transcriptions and provenance in the artifact). The summary is that the
toolkit is now closed, not thin: every general tool fails at the same single
point, and that point is identified.

**Permanence theorems for wreath products — BLOCKED, definitively.**
Hayes–Sale (arXiv:1608.02610) covers only the standard wreath product
`⊕_H G ⋊ H` and says nothing here. Gao–Kunnawalkam Elayavalli–Patchell
Theorem 3.8 and Alekseev–Bradford Corollary 5.2/5.5 are the right shape and
generality — GKP 3.8 with `M = ℂ ⊕ ℂ` and `H = G` concludes exactly Connes
embeddability of `M_KT` — but all require the coordinate action `G ↷ G/Γ` to be
sofic, and `coordinate-action-not-sofic` refutes that. The only known
sufficient condition for the hypothesis, amenable point stabilizers, fails
because the stabilizers are conjugates of the Kazhdan group `Γ`. Recorded as
the invalidated route `sofic-action-permanence`.

**Sofic equivalence relations and sofic actions — BLOCKED, and two repo
citations were wrong.** Elek–Lippner (arXiv:0906.3619) prove `𝒩(ℛ) ↪ R^ω` for
sofic `ℛ`, but their only positive existence statement is Proposition 7.1,
*"The Bernoulli shift of a sofic group is sofic"* — the ordinary Bernoulli
shift over the group itself. There is **no** theorem there that an arbitrary
p.m.p. action of a sofic group has sofic orbit relation, and any argument
routed through one is void. Elek–Szabó (arXiv:math/0408400) contains no crossed
product at all; its R^ω result is *"All countable sofic groups are
hyperlinear"*, and its "essentially free" is a Tarski-type condition on a
finitely additive measure on a set, not a p.m.p. hypothesis — so citing it for
`L^∞(X) ⋊ G ↪ R^ω` is a misattribution, and the correct pin is Păunescu. With
those corrected, the relation route lands back on Păunescu's Definition 1.4,
which is precisely the diagonal-plus-permutation shape Kun–Thom Corollary D
refutes.

**Amalgamated free products over amenable faces — BLOCKED for `M_KT`, but it
relocates the problem usefully.** Brown–Dykema–Jung Corollary 4.5 gives
`ℳ₁ *_B ℳ₂ ↪ R^ω` when the `ℳᵢ` are and `B` is **hyperfinite**; the general
case is explicitly open (Gao–Junge, arXiv:2012.07940, verbatim: *"the problem
of given M and N embeddable, whether ∗_N M is embeddable as well remains
open"*). `M_KT` is a crossed product with no natural amalgam decomposition, and
where the corpus does produce one it is over `L(Γ)`, a property (T) factor —
about as far from hyperfinite as a base can be. This is the same
(T)-compatibility toll as `haagerup-t-exclusion`, collected on the other side.
It is worth recording that the neighbouring free-lamp group
`H_K = G *_Γ (Γ × K)` has `L(H_K) = L(G) *_{L(Γ)} (L(Γ) ⊗̄ L(ℤ))`, so *its*
hyperlinearity is literally an instance of the open amalgamated-free-product
problem over a (T) base. That is a cleaner-stated target than `M_KT`, and it is
a different group — it belongs to a different node, not this one.

**Trace-blindness — this is the right diagnosis, and it is a non-obstruction,
not a construction.** The defect that kills soficity is a size defect, and
`notes/OBSTRUCTIONS.md` §1 shows the failure of the invariant-size argument in
`II₁` factors is sharp: `R ⋊_θ ℤ` for the Bernoulli shift carries a unitary
strictly compressing a subalgebra, so no invariant — index, entropy, or
undiscovered — can settle the branch. The trace is additive under refinement,
hence blind to substituting a block for a point. So the tracial theory really
cannot see the sizes. What that buys is the *absence* of an obstruction; it
does not hand over microstates, and the precise statement of what it does buy
is `fiber-masa-free-cocycle` clause 3.

**Where all of it fails is one point.** Both halves of the construction are
free. The lamp algebra `ℂ ⊕ ℂ` is hyperfinite; the acting group `G` is
residually finite, hence sofic, hence hyperlinear, so `L(G)` is already Connes
embeddable and (T)-compatibility costs nothing here. Every failure above is a
failure to embed the *action*, and after `coordinate-action-not-sofic` the
residual requirement is exactly one thing: the lamp algebra must be embedded
**non-Cartanly** — no maximal abelian subalgebra containing it may be
normalized by all the group unitaries. Kun–Thom Corollary D forbids the
Cartan case and says nothing about the rest.

**The asymmetry, in its cleanest published form.** Holt–Rees (arXiv:1601.01836)
prove wreath closure for **weakly sofic** and explicitly not for hyperlinear,
and the candidate now sits in exactly that gap: `W` is weakly sofic — Glebsky's
residually-finite-by-weakly-sofic permanence has no hypothesis on the coset
action at all, and `W` is a restricted sum of finite groups extended by a
residually finite group (`weakly-sofic-not-sofic`) — and not sofic. So the
metric class that tolerates arbitrary bi-invariant metrics on finite groups
already contains `W`, and the one that fixes normalized Hilbert–Schmidt is the
open case. The sharp question this suggests is whether Glebsky's permanence
theorem has a normalized-HS analogue; the expected crux is that weak soficity
permits metric surgery on the finite groups and HS on `U(n)` does not.
Relatedly, since all actions of a LERF group on sets are sofic
(arXiv:2402.17150), `G` is not LERF and `Γ` is not separable in `G` — which is
a genuine constraint and not merely a restatement, as the next paragraph shows.

**There is a positive foothold, and it was in the corpus rather than the graph.**
`positive-core-bernoulli-ce` (now established, imported from
`notes/FALSE_POSITIVE_CORE_IS_SOFIC.md`) exhibits honest matrix microstates for
a genuine piece of the target: for `L₊ = SL_d(ℤ) ∩ M_d(ℕ)`, `T = ΓL₊` and
`X₀ = TΓ/Γ`, the action `Γ ↷ X₀` is sofic, so `W₀ = (⊕_{X₀} C₂) ⋊ Γ` is sofic
and `N₀ = L^∞({±1}^{X₀}) ⋊ Γ` is Connes embeddable. The separating property is
stabilizer separability: the positive stabilizers `ℓΓℓ⁻¹` are separable in `Γ`
by degree-truncation congruences, even though `Γ` is not separable in `G`. So
LERF is far more than the situation needs, and the same GKP theorem that kills
the full action in contrapositive builds the model for the positive part. The
route that uses this is `positive-core-dilation-splice`, whose single gap
`simultaneous-dilation-splice` turns out to *be* the open amalgamated-free-product
problem over a nonamenable base (Gao–Junge, arXiv:2012.07940) plus a quotient
step for the `SL_d(ℤ)` relations. That identification is new and cuts both
ways: the gate will not fall to a routine permanence lemma, but the candidate
is now attached to a problem with independent attention.

**A witness that is not a carrier.** `amenable-charge-route` applies
Kahl–Schneider's equivalence (`hyperlinear-near-representation-criterion`):
hyperlinear iff there is an essentially free amenable near representation, the
Hilbert-space analogue of Elek–Szabó's set-level criterion for soficity. Since
the witness is a finitely additive charge on an orthonormal basis rather than a
finite carrier, the locally-sofic collapse of `notes/FALSE_HALO_ACTION_AUDIT.md`
has nothing to grip, and the basis — the coordinate system — is explicitly not
required to be equivariant. Same non-Cartan requirement, different toolbox
(Hahn–Banach rather than finite construction). Risk recorded there: if Bekka's
(T) theorem forces an amenable representation of a Kazhdan group to contain a
finite-dimensional subrepresentation, the lane collapses into the rigidity fork.
I could not read that statement and did not use it.

**The live architecture.** `growing-fiber-models` puts the lamps on a
coordinate set and the group's Hilbert–Schmidt separation in a growing unitary
fiber the lamps cannot see. The route also carries the reason the naive version
of that idea fails — block-monomial fibers have an invariant MASA and collapse
back to a permutation model of the coordinate action that is still faithful on
the lamps — which is what forces clause 3 and turns the architecture into
`fiber-masa-free-cocycle`. The Fourier-block calculation in `notes/NOTEPAD.md`,
written there as an obstruction to lifting an abstract embedding to a Cartan
one, is the design principle for clause 3 read forwards.

**Read the live routes as descriptions, not fronts (audit, 2026-08-14).** All
three routes currently open into this claim fail the "restatement dressed as a
reduction" test, and each node carries the derivation. `simultaneous-dilation-splice`
asks for Connes embeddability of `M`, and `(FSD5)` says `M = L(W)` — the target
verbatim, needing no established claim to see it. `wreath-amenable-near-representation`
is equivalent to the target modulo the established Kahl–Schneider **iff**.
`fiber-masa-free-cocycle`'s exact half is implied by the target modulo the
established `block-monomial-coordinate-collapse`, and its quantitative half is
strictly *stronger* than the target rather than weaker — the opposite defect,
and no better.

Their implications are all true, so the graph is not lying; but the frontier
here is **one hole described three ways**, not three fronts, and counting them
otherwise overstates progress. What the three do supply is real and worth
keeping: a localization of the difficulty (the core is discharged, only the
dilation remains), a specification of the surviving model shape, and a change
of scale from trace to operator norm. Descriptions of a hole, not reductions of
one.

**The dual target.** The same pass identifies the rigidity-side twin, which
this graph should also carry: *invariant Cartan completion* — that every
abstract embedding of `M_KT` can be conjugated so that some diagonal
ultraproduct containing the lamp algebra is normalized by all `Θ(u_g)`. If
that is true, `M_KT` is not Connes embeddable and this claim is refuted. It is
the exact negation of `fiber-masa-free-cocycle` clause 3, and neither
direction is known.
