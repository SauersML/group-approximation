---
rg: 2
id: commensurating-loxodromics-split-their-centralizers
kind: claim
title: "If z has unbounded wall count in a commensurating action, a finite-index subgroup of its centralizer maps onto Z sending z to 1; so central elements of perfect groups without finite quotients are elliptic"
distinct_from:
  cubical-coset-proper-actions-capture-distorted-elements: that makes distorted elements elliptic (growth invariant, via Cornulier's bounded-or-linear dichotomy); this makes elements that are rationally trivial in the abelianization of a finite-quotient-free subgroup of their centralizer elliptic (character invariant), which applies to undistorted elements such as the central element 1_C of C(C,Z) ⋊ V
---

**ESTABLISHED** by `commensurating-loxodromics-split-their-centralizers-proof`.

**Setting.** A group `G` acts on a set `X`, and `A ⊆ X` is commensurated: `gA Δ A` is finite
for every `g`. Put `ℓ(g) = |gA Δ A|`. Call `z ∈ G` *elliptic* if `ℓ(z^N)` is bounded in `N`.
(For a CAT(0) cube complex or a discrete wall space take `X` the half-spaces and `A` those
containing a vertex; then `ℓ(g)` is the displacement of that vertex.)

**Statement.**

1. Let `z ∈ G` with `ℓ(z^N)` unbounded. Then there are a subgroup `C' ≤ C_G(z)` of finite index
   with `z ∈ C'`, and a homomorphism `φ : C' → Z` with `φ(z) = 1`.
2. *(Corollary.)* Let `z ∈ S ≤ C_G(z)`, where `S` has no proper finite-index subgroup and the
   image of `z` in `S/[S,S]` has finite order. Then `z` is elliptic in every commensurating
   action of every group `G ⊇ S`. This holds in particular when `z` is central in a perfect group
   `S` with no proper finite-index subgroup.

**Remark (not load-bearing).** The statement is special to wall counts. It uses the
decomposition of `X` into `⟨z⟩`-orbits and the finiteness of the set of one-ended orbits. No
Hilbert-space analogue is claimed. The locally compact group `\widetilde{SL_2(R)}` is a heuristic
reason to expect none: it is connected and perfect, has an infinite discrete centre, and is
a-T-menable, so a proper cnd function on it is unbounded on the centre.

**Novelty.** Not established. The argument is short and plausibly folklore (compare Haglund's
combinatorial axes). No source stating it was found in the repository.
