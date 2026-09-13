---
rg: 2
id: bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one-citation
kind: route
title: Literature import of Barlak–Enders–Matui–Szabó–Winter, arXiv:1312.6289, Definition 1.2 and Theorem 2.3
target: bemsw-outer-z2-kirchberg-rokhlin-dimension-at-most-one
requires: []
---

**Source.**  S. Barlak, D. Enders, H. Matui, G. Szabó, W. Winter, *The Rokhlin
property vs. Rokhlin dimension 1 on unital Kirchberg algebras*,
arXiv:1312.6289.  The PDF was fetched on MSI on 2026-09-13 and extracted with
ghostscript `txtwrite`.  The quotations below follow the extracted text, with
the extraction's line breaks and sub/superscripts repaired.

**Abstract (extract).**  "It turns out that in fact every outer Z2-action on a
unital Kirchberg algebra has Rokhlin dimension at most one.  This relies
heavily on Goldstein's and Izumi's remarkable main result of [4], which asserts
that every such outer action absorbs a faithful quasi-free action on O∞."

**Definition 1.2.**  "Let G be a finite group, A a unital C∗-algebra and
α : G ↷ A an action via automorphisms.  α is said to have Rokhlin dimension d,
written dimRok(α) = d, if d is the smallest natural number with the following
property: For all ε > 0 and F ⊂⊂ A, there exist positive contractions
(f_g^(l))_{g∈G, l=0,…,d} satisfying
(1) 1_A =_ε Σ_{l=0}^d Σ_{g∈G} f_g^(l).
(2) α_g(f_h^(l)) =_ε f_{gh}^(l) for all l = 0,…,d and g, h ∈ G.
(3) ‖f_g^(l) f_h^(l)‖ ≤ ε for all l = 0,…,d and g ≠ h in G.
(4) ‖[f_g^(l), a]‖ ≤ ε for all l = 0,…,d, g ∈ G and a ∈ F."

**Corollary 2.2.**  "A faithful, quasi-free action Z2 ↷ O∞ in the sense of [4]
has Rokhlin dimension 1."  The proof takes a non-trivial projection
`p ∈ O_∞` with `[p]_0 = 0` and `u = 1 − 2p`, and uses [4, Section 6] to identify
`⊗_N Ad(u)` on `⊗_N O_∞ ≅ O_∞` with the faithful quasi-free action.  It ends:
"On the other hand, it is known that no finite group action on O∞ can have the
Rokhlin property."

**Theorem 2.3.**  "Let A be a unital Kirchberg algebra and α : Z2 ↷ A an action.
If α is outer, then α has Rokhlin dimension at most 1.
Proof. Let γ be a faithful, quasi-free action of Z2 on O∞. By [4, 5.1], α is
conjugate to α ⊗ γ. Hence the statement follows immediately from 2.2."

**Remark 2.5.**  "In [6, 4.7], it was shown that there exists an action
β : Z2 ↷ O2 such that O2 ⋊β Z2 ≅ O∞^st ⊗ M2∞.  It follows from 2.3 that this
action has Rokhlin dimension 1."  Here `O_∞^st = pO_∞p` for a projection with
trivial `K_0`-class (their Definition 2.4).

**References inside the source.**  [4] is Goldstein–Izumi, *Quasi-free actions
of finite groups on the Cuntz algebra O∞*.  [5] is Hirshberg–Winter–Zacharias,
*Rokhlin dimension and C\*-dynamics*.  [6] is Izumi, *Finite group actions on
C\*-algebras with the Rohlin property I*.  None of these was re-read here.

**Reading paragraph of the claim.**  "Exactly `1`" uses only that a
counterexample is not Rokhlin.  "Infinite commuting-tower dimension" is item 5
of `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, as stated there.  Both
are readings, not part of the import.
