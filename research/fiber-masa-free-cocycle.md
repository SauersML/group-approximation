---
rg: 2
id: fiber-masa-free-cocycle
kind: claim
title: A lamp embedding with no invariant coarse block decomposition
distinct_from:
  hyperlinear-wreath-model: that asks for any hyperlinear model of W; this asks for one specific structural property of one — that no coarse block decomposition carrying the lamps is preserved
  block-monomial-coordinate-collapse: that is the established no-go saying an exactly preserved coarse decomposition is fatal; this is the positive requirement it forces, that the preservation defect stay bounded away from zero
  wreath-flexible-hs-stability: that is a stability property of the acting group G; this is a structural property of a putative microstate sequence
  torsion-free-higman-embedding: that is a group-embedding statement about finitely presented torsion-free groups; this is an analytic statement about matrix microstates and has no embedding of groups in it
artifacts:
  - notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md
---

Construct a hyperlinear model of `W` — finite data `Θ_n` on `ℂ^{d_n}` that is
`(F,ε)`-multiplicative and `(F,ε)`-separated in the normalized Hilbert–Schmidt
metric, in the sense of `Sofic/Hyperlinear.HyperlinearModel` — in which the
image of the lamp algebra admits **no invariant coarse block decomposition**:
there is no tensor splitting

    ℂ^{d_n} ≅ ℂ^{Y_n} ⊗ ℂ^{m_n}

with `Θ(a_x) ∈ D_{Y_n} ⊗ 1` for the lamps and every `Θ(u_g)` block-monomial
over `Y_n`, and more: the defect of every such candidate splitting must stay
bounded away from zero, uniformly over windows.

## RESTATEMENT AUDIT (2026-08-14)

Re-derived after the team-wide "restatement dressed as reduction" warning, and
it does not come out clean.

Clause 3's *exact* half is implied by the target. `block-monomial-coordinate-collapse`
is established: no block-monomial fiber model of `M_KT` exists. So if `W` is
hyperlinear at all, any hyperlinear model of it automatically fails to be
block-monomial with the lamps in a coarse diagonal — the exact non-existence is
free, not something a construction has to arrange. Modulo that established
claim, "hyperlinear model with no exact invariant coarse block structure" is
equivalent to "hyperlinear model", and `growing-fiber-models` is to that extent
a renaming of `hyperlinear-wreath-model`.

The *quantitative* half — that the defect of every candidate splitting stay
bounded away from zero, uniformly over windows — is genuinely stronger than the
target rather than equivalent to it. But that is the opposite defect and no
better: a model could exist whose defects tend to zero without ever vanishing,
so this claim can fail while `W` is hyperlinear. The strengthening was not
forced by anything; it came from trying to describe what a model must look
like, and it makes the prerequisite potentially harder than the goal.

So the honest reading is: **this is a specification of the surviving model
shape, not a reduction.** It is kept because the specification is informative —
it is what the two collapse theorems leave standing, and it tells a builder
where the defect has to come from — but it should not be counted as an
independent hole in the frontier. All three live routes into
`hyperlinear-wreath-model` fail this audit; see `simultaneous-dilation-splice`
and `wreath-amenable-near-representation` for the other two.

## On the slug, and on masas

The slug says "masa" and the requirement does not, deliberately. cairn-bernoulli
is right that demanding no invariant *maximal abelian subalgebra* is stronger
than necessary: their Lemma 3 runs on the doubly stochastic matrix `|u_ij|²` in
a fixed matrix-unit system, so a masa that is not a diagonal ultraproduct — a
singular masa, say — supplies no such matrix, yields no permutations, and is
harmless if invariant. The coarse-block phrasing above avoids the issue
entirely: it never mentions masas.

It also subsumes their weakening rather than sitting beside it. At `m_n = 1`
the splitting is trivial, `Y_n` is the whole index set, and block-monomial
means monomial; by their rigidity theorem a unitary approximately normalizing
the full diagonal ultraproduct is close to a monomial. So the `m_n = 1` case of
the clause *is* "no invariant diagonal ultraproduct", i.e. exactly the negation
of `invariant-cartan-completion`, and the `m_n > 1` cases are the additional
content that `block-monomial-coordinate-collapse` forces. The clause is
therefore the weakest form that is still sufficient. The slug is kept because
slugs are addresses, not descriptions, and `growing-fiber-models` points here.

## Why the requirement is stated this strongly

Three successive weakenings were tried and each is refuted, which is what fixes
the final form.

*Permutation normalizers.* Refuted by Kun–Thom Corollary D
(`coordinate-action-not-sofic`).

*Full-masa normalizers.* Refuted by `diagonal-normalizer-rigidity`: an
approximate normalizer of the full diagonal masa is close to a monomial, and
the diagonal phases untwist, so this reduces to the permutation case.

*Coarse block structure.* Refuted by `block-monomial-coordinate-collapse`. This
is the one that looked like a door and is not. `diagonal-normalizer-rigidity`
is sharp in needing the *full* masa — the Fourier-block unitary `⊕_j F_m`
centralizes a coarse block-constant subalgebra at distance `√2` from every
monomial — but distance from monomials was never the relevant measurement. A
Fourier-block unitary still *has* a permutation part over the coarse index set,
that part is still multiplicative by a rigidity estimate uniform in the fiber
dimension, and the lamps still ride on the coarse coordinates. Growing the
fiber dilutes traces; it does not dilute a displaced block.

## What is left, and why it is not vacuous

The lamp algebra is diffuse abelian, so it can always be conjugated into the
diagonal, and a window `{a_x : x ∈ E}` has exactly `2^{|E|}` atoms of equal
trace `2^{-|E|}`. So a coarse decomposition with equal blocks is *always*
present approximately, and `Θ(u_g)` for `g` in a window always permutes those
atoms approximately. The content of the claim is entirely quantitative: the
defect must not vanish.

That is not vacuous, and the reason is already in the corpus. The defect for
the atom decomposition of a window `E ⊆ G/Γ` is governed by the boundary of `E`
under the group action, and `G ↷ G/Γ` has no Følner sets — property (T) with
infinite index — so the boundary carries a constant fraction of `E`. One
mismatched coordinate costs a configuration-space defect of order one
(`notes/OBSTRUCTIONS.md` §3, amplification). The amplification obstruction,
which has always been read as an argument against models, is on this reading
the only known *source* of the non-vanishing defect the claim requires. Whether
that is enough, or whether amplification kills the model before it supplies the
defect, is the open question — and it is now a single quantitative question
about one number rather than a search for an architecture.

## A second acceptance test, which clause 3 does not supply

Any candidate cocycle has to pass a test that has nothing to do with block
structure. Kun–Thom derive Theorem A from their **Theorem 4.1** — the
centralizer of `σ(Γ)` is normalized by `σ(G)` — not from Corollary D, and
nothing downstream of Theorem 4.1 uses permutations: only that `Γ` fixes the
base coset, that distinct cosets give distinct lamps, and that a strict
compressor exists. So a Hilbert–Schmidt analogue of Theorem 4.1 alone would
refute hyperlinearity of `W`, with no masa and no coarse decomposition anywhere
in the argument. That is `kt-centralizer-normalization-hs`, which invalidates
`growing-fiber-models` if established.

Concretely, a cocycle can satisfy clause 3 in full and still fail by putting
`ρ(a_{tΓ})` in the relative commutant of `σ(Γ)`. Check that separately;
clause 3 does not imply it and was never designed to. (Flagged by
cairn-bernoulli.)

## Design input available

The Fourier-block calculation in `notes/NOTEPAD.md` is the finite-dimensional
mechanism for breaking a masa at maximal angle, and Weyl (clock-and-shift)
fibers are its natural group-theoretic packaging. It is not sufficient on its
own — that is exactly what `block-monomial-coordinate-collapse` establishes —
but any construction that succeeds will contain something like it, applied so
that no coarse index set survives rather than so that no masa survives.

**Check before building.** The corpus has extensive Weyl/Clifford/Pauli
machinery developed for the operator-norm (non-MF) programme, much of it
recorded as FALSE. That is a different property and those refutations do not
transfer, but the constructions might, and the `notes/FALSE_DUAL_HEISENBERG_*`
family should be read before any fiber cocycle is written down.
