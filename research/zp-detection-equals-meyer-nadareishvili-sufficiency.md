---
rg: 2
id: zp-detection-equals-meyer-nadareishvili-sufficiency
kind: claim
title: For G = Z/p, restriction and crossed product detect KK^G-contractibility iff they detect membership in the equivariant bootstrap class
distinct_from:
  zp-restriction-and-crossed-product-detect-kk-g-contractibility: that is the open detection question itself; this proves it is equivalent to the bootstrap-membership criterion that Meyer and Nadareishvili state they cannot decide, and splits the equivariant UCT into the ordinary UCT plus detection.
  bootstrap-zp-actions-realize-every-cyclotomic-k-module: that realizes Köhler invariants with contractible restriction; this is a formal equivalence between two detection statements for arbitrary separable G-algebras.
  zp-detection-iff-bootstrap-sufficiency-and-kk-g-generation: that independent node (lane ex-uct-detection-prove, landed later) proves the same detection-sufficiency equivalence for nuclear objects, with the generation and dynamical-uniqueness forms; this adds the all-separable case, verbatim Köhler, Meyer and Arano-Kubota citation nodes, and the splitting UCT_G = UCT plus detection.
---

**ESTABLISHED (derivation from cited theorems, no new analytic input).**
Let `p` be prime, `G = Z/p`, `B ⊆ KK` the bootstrap class and `B^G ⊆ KK^G` the
equivariant bootstrap class. `B^G` is the class of objects that are
KK^G-equivalent to an action on a type I algebra. Consider these statements
about a class `𝒞` of separable `G`-C\*-algebras.

* `Det(𝒞)`: every `D ∈ 𝒞` with `Res D ≃_KK 0` and `D ⋊ G ≃_KK 0` has
  `D ≃_(KK^G) 0`.
* `MN(𝒞)`: every `A ∈ 𝒞` with `Res A ∈ B` and `A ⋊ G ∈ B` lies in `B^G`.

The converse of `MN` always holds: `A ∈ B^G` forces `Res A, A ⋊ G ∈ B`. This
is Meyer–Nadareishvili (arXiv:2406.11787v2), introduction and Corollary 3.5.

1. `Det(all separable) ⟺ MN(all separable)`.
2. `Det(nuclear) ⟺ MN(nuclear)`.
3. **The equivariant UCT splits.** Let `UCT_G` say that every separable nuclear
   `G`-algebra is in `B^G`, and `UCT` that every separable nuclear algebra is in
   `B`. Then `UCT_G ⟺ UCT ∧ Det(nuclear)`.

**Status of `MN` in the literature.** For an arbitrary finite group, with all
cyclic subgroups `H` in place of `{1, G}`, `MN` is the converse that
Meyer–Nadareishvili leave undecided. Their words, in the introduction of
arXiv:2406.11787v2 (5 Dec 2025): "This implies that A and A⋊H for cyclic
subgroups H ⊆ G are in the bootstrap class in KK. We do not know whether this
necessary condition is sufficient as well." They say it again before
Corollary 3.5. For `G = Z/p` the cyclic subgroups are `1` and `G`, so the
detection question
`zp-restriction-and-crossed-product-detect-kk-g-contractibility` is exactly
the prime-order case of their question.

**Consequences.**
* A counterexample to detection, an *equivariant phantom*, is the same thing
  as a `G`-algebra outside `B^G` whose restriction and crossed product lie
  in `B`.
* Item 3 isolates detection as the part of the equivariant UCT for `Z/p` that
  the ordinary UCT does not already contain. Nothing here settles whether `UCT`
  implies `Det(nuclear)`, or the reverse. So a phantom is not known to be a UCT
  counterexample, and a UCT counterexample is not known to give a phantom.

Proof: `zp-detection-equals-meyer-nadareishvili-sufficiency-proof`.
