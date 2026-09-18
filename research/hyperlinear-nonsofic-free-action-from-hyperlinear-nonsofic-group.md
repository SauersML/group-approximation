---
rg: 2
id: hyperlinear-nonsofic-free-action-from-hyperlinear-nonsofic-group
kind: route
title: The Bernoulli shift of a hyperlinear nonsofic group is a free hyperlinear nonsofic action
target: hyperlinear-nonsofic-free-action
requires:
  - hyperlinear-nonsofic-group
  - hyperlinear-groups-closed-under-free-products
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
---

**Reduction (one direction): `hyperlinear-nonsofic-group` ⇒ `hyperlinear-nonsofic-free-action`.**

Let `H` be a countable hyperlinear group that is not sofic. `H` is infinite, since finite
groups are sofic. Let `X = ({±1},fair)^H` with the shift action.

1. **Free.** The Bernoulli shift of an infinite group is essentially free.
2. **Hyperlinear.** `H * Z/2` is hyperlinear by `hyperlinear-groups-closed-under-free-products`.
   Apply `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` to the pair
   `C = {e} ≤ A = H`: the free binary coset wreath is `A *_C (C × Z/2) = H * Z/2`
   (condition 2), so the ordinary binary coset wreath
   `Z/2 ≀ H = (⊕_H Z/2) ⋊ H` is hyperlinear (condition 1). Fourier transform identifies
   `L(⊕_H Z/2)` with `L^∞({±1}^H)` equivariantly, so `L^∞(X) ⋊ H = L(Z/2 ≀ H)` embeds in
   `R^ω`: `X` is a hyperlinear action (Păunescu Definition 1.3).
3. **Not sofic.** If `X` were sofic (Definition 1.4), the embedding `Θ` would send each
   `u_h` to a permutation with `τ(Θ(u_h)) = τ(u_h) = δ_(h,e)`, so `h ↦ Θ(u_h)` would be a
   sofic representation of `H` (Kun--Thom p. 4; see `kun-thom-free-nonsofic-action`). `H` is
   not sofic.

So `X` witnesses `hyperlinear-nonsofic-free-action`, and its orbit equivalence relation is a
nonsofic relation with Connes-embeddable von Neumann algebra (Păunescu Proposition 1.15).

**What this changes.** The third Attempt of `hyperlinear-nonsofic-free-action` stopped at
the lack of a wreath permanence theorem for a nonsofic acting group (Hayes--Sale assume the
acting group sofic). For the trivial coset space no such theorem is needed: free-product
permanence plus the established tensor-Gaussian equivalence already make `Z/2 ≀ H`
hyperlinear for every hyperlinear `H`. So the root's action separation is **implied by**
Pestov's Question 3.4 in its separating form. The converse is open: a free hyperlinear
nonsofic action of a sofic group (the Theorem C route) gives a hyperlinear nonsofic group only
through `theorem-c-separation-iff-infranormal-coset-wreath`'s corollary for the Theorem E pair.

**Trust surface.** `binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` (graph
established, tensor-Gaussian construction from free lamps) at the degenerate pair `C = {e}`,
where its free binary wreath is the plain free product; Brown--Dykema--Jung free-product
permanence.
