---
rg: 2
id: osin-isolated-components-relative-area-citation
kind: route
title: Import Osin's Lemma 2.27 on isolated components, with his definitions of relative hyperbolicity, reduced presentations and Omega
target: osin-isolated-components-bounded-by-relative-area
requires: []
artifacts:
  - research/artifacts/fpbs/docs/twisted-level-percolation-low-density-disconnection.md
---

Literature import. D. V. Osin, *Relatively hyperbolic groups: intrinsic geometry, algebraic properties, and algorithmic problems*, arXiv:math/0404040, published as Mem. Amer. Math. Soc. 179 (2006), no. 843. The arXiv PDF was fetched on MSI on 2026-09-12 and its text extracted with pypdf. Verbatim, up to extraction spacing:

> **Definition 1.6.** We say that a group G is hyperbolic relative to a collection of subgroups {Hλ}λ∈Λ if G is finitely presented with respect to {Hλ}λ∈Λ and the relative Dehn function of G with respect to {Hλ}λ∈Λ is linear.

> (p. 7) Analogously to the case of ordinary Dehn functions, if the relative Dehn function of G with respect to {Hλ}λ∈Λ is finite for each value of the argument, it is independent of the choice of a finite relative presentation up to some equivalence relation (Theorem 2.34).

> **Definition 2.20 (Connected components).** Two Hλ–components p1, p2 of a path q (cyclic or not) in Γ(G, X ∪ H) are called connected if there exists a path c in Γ(G, X ∪ H) that connects some vertex of p1 to some vertex of p2 and φ(c) is a word consisting of letters from H̃λ. [...] (In algebraic terms this means that these two vertices belong to the same coset gHλ.)

> **Definition 2.21 (Isolated components).** An Hλ–component p of a path q (cyclic or not) is called isolated if no (distinct) Hλ–component is connected to p.

> **Definition 2.24.** A relative representation (2.3) of a group G with respect to a collection of subgroups {Hλ}λ∈Λ is called reduced if each relator R ∈ R has minimal length among all words from (X ∪ H)∗ representing the same element of the group F. [...] Without loss of generality we may assume all relative presentations under consideration to be reduced. The next lemma shows that, without loss of generality, we can assume finite relative presentations to be reduced.

> **Definition 2.25.** For every λ ∈ Λ, we denote by Ωλ the subset of all elements g ∈ Hλ such that there exists a relator R ∈ R, and an Hλ–syllable V of R such that V represents g in G. We also put Ω = ∪λ∈Λ Ωλ. It is important that the set Ω is finite, whenever the set R is finite.

> **Lemma 2.27.** Suppose that a group G is given by the reduced finite relative presentation (2.3) with respect to a collection of subgroups {Hλ}λ∈Λ. Let q be a cycle in Γ(G, X ∪ H), p1, ..., pk a certain set of isolated Hλ–components of q. Then φ(pi) ∈ ⟨Ωλ⟩ for any i = 1, ..., k. Moreover, the lengths of the elements φ(p1), ..., φ(pk) with respect to the generating set Ωλ of the subgroup ⟨Ωλ⟩ satisfy the inequality Σ_{i=1}^k |φ(pi)|_{Ωλ} ≤ M · Area^rel(q), where M = max_{R∈R} ||R||.

**What the claim adds.**
- `Area^rel(q) <= C l(q) + C'` is what "linear relative Dehn function" in Definition 1.6 means, applied to the label of `q`.
- Reducedness is available by the sentence after Definition 2.24. Finiteness of `Omega_λ` is the last sentence of Definition 2.25.

**Not re-read.** The proof of Lemma 2.27, and the statement of the lemma that follows Definition 2.24, which the extraction did not reach. The import is at the level of the numbered statements quoted above.
