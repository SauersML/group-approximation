---
rg: 2
id: diagonal-coset-commuting-counterexample-proof
kind: route
title: Split the bad coset space into two free coordinate actions on (G × G)/ΔH
target: nonsofic-orbit-forces-commuting-counterexample
requires:
  - gkp-sofic-action-toolkit
artifacts:
  - research/artifacts/gkp-2401-04945-verified.md
  - research/artifacts/commuting-sofic-actions-note-2026-08-17.md
  - GroupApproximation/Algebra/DiagonalCosetAction.lean
---

# Split the bad coset space into two free coordinate actions

Complete proof. The only external input is `gkp-sofic-action-toolkit`
(Theorem 2.14, Proposition 2.15(2), Proposition 2.15(3), Proposition 2.16 of
arXiv:2401.04945v3); everything else is coset bookkeeping in `G × G`.

## Setup

Let `G` be a countable group and `H ≤ G`. Put

```text
ΔH = {(h,h) : h ∈ H} ≤ G × G,     X = (G × G)/ΔH,
```

and let `G × G` act on `X` by left multiplication. `X` is countable because
`G` is. Restrict along the two coordinate embeddings
`G_1 = G × {1}` and `G_2 = {1} × G`:

```text
α_1(g)·(a,b)ΔH = (ga, b)ΔH,       α_2(g)·(a,b)ΔH = (a, gb)ΔH.
```

`G_1` and `G_2` commute inside `G × G`, so `α_1` and `α_2` commute, and the
action they combine to — `α_1(g_1)α_2(g_2) = ` left multiplication by
`(g_1,g_2)` — is exactly the left `G × G`-action on `X`. This is the shape
Question 4.2 asks about, with two groups, which by Proposition 2.15(4) is the
only case that matters.

## Step 1 — both coordinate actions are free

Suppose `α_1(g)·(a,b)ΔH = (a,b)ΔH`. Then `(a,b)^{-1}(g,1)(a,b) ∈ ΔH`.
Conjugation in a direct product is coordinatewise, so

```text
(a,b)^{-1}(g,1)(a,b) = (a^{-1}ga, 1),
```

and `(a^{-1}ga, 1) = (h,h)` for some `h ∈ H` forces `h = 1` from the second
coordinate, hence `a^{-1}ga = 1`, hence `g = 1`. The same computation with the
coordinates swapped — the second coordinate of `(1,g)` conjugated is `b^{-1}gb`
and the *first* is `1`, so `h = 1` again — gives freeness of `α_2`.

Note where `H` went: it did not go anywhere. Freeness holds for **every**
subgroup `H ≤ G`, because a diagonal element with a trivial coordinate is
trivial. That is the whole trick.

## Step 2 — both coordinate actions are sofic

`G` is sofic by hypothesis. A free action of a sofic group on a countable set
is sofic: each orbit is `G`-isomorphic to the regular `G`-set `G/{1}`, which
is sofic by Theorem 2.14 applied to the locally finite subgroup `N = {1}`, and
an action all of whose orbits are sofic is sofic by Proposition 2.16. Both
steps are spelled out in `gkp-sofic-action-toolkit`.

So `α_1` and `α_2` are sofic. Nothing about `H` is used here either.

## Step 3 — the diagonal orbit is `G/H`

Let `ΔG = {(g,g) : g ∈ G} ≤ G × G` and let `x_0 = ΔH ∈ X` be the base point.
Define

```text
Φ : G/H → X,     Φ(gH) = (g,g)ΔH.
```

*Well defined:* if `g' = gh` with `h ∈ H` then
`(g',g')ΔH = (g,g)(h,h)ΔH = (g,g)ΔH`.

*Injective:* `(g,g)ΔH = (g',g')ΔH` gives
`(g^{-1}g', g^{-1}g') ∈ ΔH`, hence `g^{-1}g' ∈ H`, hence `gH = g'H`.

*Equivariant for `ΔG ≅ G`:*
`Φ(kgH) = (kg,kg)ΔH = (k,k)·(g,g)ΔH = (k,k)·Φ(gH)`.

So `Φ` is a `G`-equivariant bijection from `G/H` onto the `ΔG`-orbit of `x_0`,
which is `𝒪 = {(g,g)ΔH : g ∈ G}`. Equivalently: the stabilizer of `x_0` in
`ΔG` is `{(g,g) : (g,g) ∈ ΔH} = ΔH`, i.e. `H` under the identification
`ΔG ≅ G`.

## Step 4 — contradiction

Suppose the combined action `α : G × G ↷ X` were sofic.

- `ΔG` is a subgroup of `G × G`, so `α|_{ΔG}` is sofic by Proposition
  2.15(3).
- `𝒪` is one orbit of `α|_{ΔG}`, so the restriction of `α|_{ΔG}` to `𝒪` is
  sofic by Proposition 2.15(2).
- By Step 3 that restriction is isomorphic, as a `G`-set with `G`-action, to
  `G ↷ G/H`. Soficity is an isomorphism invariant of `G`-sets (Proposition
  2.9(2) transports the map `π` along an equivariant bijection and does not
  touch `φ`).

Hence `G ↷ G/H` is sofic, contradicting the hypothesis. Therefore `α` is not
sofic, while `α_1` and `α_2` are. `□`

## The bookkeeping is kernel-checked

Every group-theoretic step of this route is formalized in
`GroupApproximation/Algebra/DiagonalCosetAction.lean` (2026-08-18, in the
root import closure, axiom-clean): Step 1 is `eq_one_of_fst_smul_fixed` /
`eq_one_of_snd_smul_fixed` — freeness for **every** subgroup `H`, the
trivial-coordinate trick included; the commutation and combination identities
of the Setup are `fst_smul_snd_smul_comm` / `fst_smul_snd_smul` /
`snd_smul_fst_smul`; Step 3 is `diagOrbitMap` with `diagOrbitMap_injective`,
`diagOrbitMap_smul`, `mem_range_diagOrbitMap` and
`diag_smul_base_eq_base_iff` (stabilizer of the base coset is exactly `H`).
What is *not* formalized is every appeal to soficity: Theorem 2.14,
Propositions 2.15(2)(3), 2.16 and the isomorphism-invariance of sofic
actions remain cited from `gkp-sofic-action-toolkit`. So the machine checks
the construction, and the two papers carry the transfer.

## Where the strength sits

Every step except the hypothesis on `G ↷ G/H` is soft. The construction is
not sensitive to `H` at all: it is the *same* two free actions for every
subgroup, and the subgroup shows up only in which orbit the diagonal cuts out.
`H = {1}` gives `X = G × G` with the product action, `H = G` gives `X ≅ G` with
left and right multiplication and the diagonal restriction is conjugation —
which is exactly the argument the source paper runs on p. 15 to show that a
positive answer to Question 4.2 would make every sofic group's conjugation
action sofic. Reading that paragraph with `ΔG` replaced by `ΔH` is this proof.

So the content of the result is entirely in the input, and the input did not
exist when the question was asked.

## Two failure modes checked

- **Is `α` really the action Question 4.2 forms?** The question builds
  `α : ⊕_i G_i ↷ X` out of commuting `α_i`. For two groups
  `⊕ = ×`, and `α(g_1,g_2) = α_1(g_1)α_2(g_2)` is left multiplication by
  `(g_1,g_2)` — a genuine action precisely because the coordinate actions
  commute. No mismatch.
- **Does the "iff" direction that is a theorem get contradicted?** No. The
  forward direction of Question 4.2 (`α` sofic ⟹ each `α_i` sofic) is
  Proposition 2.15(3) and is used *here*, in Step 4, in exactly that
  direction. What fails is the converse.
