---
rg: 2
id: hyperlinear-action-distills-to-stabilizer-coset-bernoulli
kind: claim
title: A hyperlinear p.m.p. action makes the generalized Bernoulli shift over G/Δ hyperlinear whenever Δ is the stabilizer of a countable family of sets
distinct_from:
  abert-weiss-free-actions-weakly-contain-bernoulli: that is weak containment of the ordinary Bernoulli shift in free actions; this passes hyperlinearity (not weak containment) from an arbitrary action to the generalized Bernoulli shift over the coset space of any set stabilizer, including infinite non-normal stabilizers, through products and a Gaussian central limit
  weak-containment-is-blind-to-kazhdan-fixed-algebras: that is ergodicity rigidity of Kazhdan subgroups under weak containment; this is a closure property of the hyperlinear action class under products, factors and weak-star limits, applied to a quasi-regular Gaussian
  kt-free-action-hyperlinear-iff-wreath-hyperlinear: that computes hyperlinearity of one specific action; this shows every action with a set of stabilizer Δ forces hyperlinearity of the binary wreath over G/Δ
  binary-free-and-ordinary-coset-wreaths-share-hyperlinearity: that identifies hyperlinearity of several groups attached to one pair C ≤ A, all already carrying the exact coset coefficient; this starts from an arbitrary hyperlinear action whose sets only have stabilizer Δ, with no lamp or coefficient equal to 1_Δ, and manufactures the Gaussian over G/Δ
  binary-coset-lamp-coefficient-forces-relative-embedding: that needs an involution whose coefficient is exactly 1_C; this needs only a set of stabilizer Δ, whose coefficient is 1 on Δ but arbitrary off it, and powers it to 1_Δ
  fd-fell-coset-observable-gaussianizes-wreath: that Gaussianizes finite-image finite-dimensional coefficients converging to 1_N; this uses Koopman coefficients of a hyperlinear action, which are neither finite-dimensional nor finite-image
---


**ESTABLISHED (proposed; proof in `hyperlinear-action-distills-to-stabilizer-coset-bernoulli-proof`).**
Let `G` be a countable group and `G ↷ (X,μ)` a p.m.p. action that is hyperlinear
(Păunescu Definition 1.3: `L^∞(X) ⋊ G` embeds trace-preservingly in `R^ω`; no
freeness assumed). Let `(A_i)_(i∈I)` be a countable family of measurable sets with
`0 < μ(A_i) < 1`, and put

```text
Δ = ∩_i Stab(A_i),     Stab(A) = { h ∈ G : μ(hA △ A) = 0 }.
```

Then the generalized Bernoulli action `G ↷ (K,κ)^(G/Δ)` is hyperlinear for every
standard base `(K,κ)`. Equivalently the binary permutational wreath
`W_Δ = (⊕_(G/Δ) Z/2) ⋊ G` is hyperlinear.

## Consequences

1. **Faithful hyperlinear actions give hyperlinear Bernoulli shifts.** Taking the
   `A_i` dense in the measure algebra, `Δ` is the kernel of `G → Aut(X,μ)`. So if `G`
   has a faithful (e.g. free) hyperlinear p.m.p. action, then `Z/2 ≀ G` is hyperlinear
   and the Bernoulli shift of `G` is hyperlinear. This closes the gap recorded in the
   third Attempt of `hyperlinear-nonsofic-free-action` for groups with a faithful
   hyperlinear action. This case is subsumed: at the trivial pair,
   `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` and free-product
   permanence already make `Z/2 ≀ G` hyperlinear for every hyperlinear `G`
   (`hyperlinear-nonsofic-free-action-from-hyperlinear-nonsofic-group`). The new
   content of the theorem is the case of a nontrivial, non-normal stabilizer `Δ`,
   where the input is an action rather than a coset coefficient and no permanence
   theorem applies: see `sofic-action-permanence`.
2. **Pointwise stabilizers of invariant subalgebras.** For any sub-σ-algebra
   `B ⊆ L^∞(X)` (not necessarily invariant), the pointwise stabilizer
   `Δ_B = {h : h·b = b for all b ∈ B}` qualifies (take a countable generating family of
   `B`), so `W_(Δ_B)` is hyperlinear. This is the input of
   `theorem-c-separation-iff-infranormal-coset-wreath`.

## Method (why it is not the standard one)

No embedding is constructed. The class of hyperlinear actions is closed under
factors, countable products and weak-star limits of invariant measures on
`[-1,1]^G` (the embeddable traces are closed). A set `A` with stabilizer `Δ` gives a
real vector `ζ = 1_(A×A^c) − μ(A)(1−μ(A))` in `L²_0(X×X)` whose normalized
positive-definite function `ψ` equals `1` exactly on `Δ` and never equals `−1`.
Tensor powers realize `ψ^n`; the central limit theorem over independent copies turns
`ψ^n` into a hyperlinear Gaussian action; `ψ^n → 1_Δ` pointwise, and the Gaussian
action with covariance `1_Δ` is the i.i.d. Gaussian Bernoulli shift over `G/Δ`.

The same argument should work for sofic actions (Păunescu Definition 1.4), since
sofic actions are also closed under products, factors and weak-star limits; that
variant is a remark, not part of the established statement, and nothing downstream uses it.

**Trust surface.** Standard facts only: tensor products and increasing unions of
Connes-embeddable algebras are embeddable; the set of embeddable traces on a
countably generated `*`-algebra is closed in the pointwise topology; the multivariate
central limit theorem.

DERIVATION
hyperlinear-action-distills-to-stabilizer-coset-bernoulli-proof
