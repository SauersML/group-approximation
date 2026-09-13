---
rg: 2
id: artin-k-pi-1-reduces-to-free-of-infinity-parabolics-citation
kind: route
title: Import the Godelle–Paris cube complex theorems that reduce the K(π,1) conjecture to free-of-infinity parabolic subgroups
target: artin-k-pi-1-reduces-to-free-of-infinity-parabolics
requires: []
---

Citation import, not a reproof. Read on 2026-09-13 from the arXiv LaTeX source of
E. Godelle and L. Paris, *K(π,1) and word problems for infinite type Artin–Tits groups,
and applications to virtual braid groups*, arXiv:1007.1365, Math. Z. 272 (2012)
1339–1364. Parts read: the introduction. Not read: the proofs of Theorems 3.1 and 4.2.

Verbatim from the introduction:

- "We say that a family 𝒮 of subsets of S is complete and K(π,1) if (1) 𝒮 is closed under
  inclusion (that is, if X ∈ 𝒮 and Y ⊂ X, then Y ∈ 𝒮), (2) Γ_X is of type K(π,1) for all
  X ∈ 𝒮, (3) 𝒮^f ⊂ 𝒮."
- "To such a family 𝒮 we associate a cube complex Φ = Φ(Γ, 𝒮), we prove that Φ has always
  the same homotopy type as the universal cover of E_Γ, and we show that Φ is CAT(0) if
  and only if 𝒮, viewed as an abstract simplicial complex over S, is a flag complex."
- "If Γ_X is of type K(π,1) for all X ∈ 𝒮_{<∞}, then 𝒮_{<∞} is complete and K(π,1) and is
  a flag complex."
- The outline places the homotopy equivalence in Theorem 3.1 and the CAT(0) criterion in
  Theorem 4.2.

Here `𝒮^f` is the set of `X ⊆ S` with `W_X` finite and `𝒮_{<∞}` the set of free-of-infinity
subsets.

**Assembly.** Suppose every free-of-infinity `Γ_X` is of type K(π,1). By the third quote,
`𝒮_{<∞}` is complete and K(π,1) and flag. By Theorem 4.2, `Φ(Γ, 𝒮_{<∞})` is CAT(0), hence
contractible. By Theorem 3.1 the universal cover of `E_Γ` is contractible, so `E_Γ` is
aspherical.

The same reduction is recorded independently in the introduction of J. Huang,
arXiv:2405.12068: "The K(π,1)-conjecture for an arbitrary Artin group reduces to the
K(π,1)-conjecture for free-of-infinity Artin groups (i.e. there are no ∞-labeled edges in
the Coxeter diagram) by work of Charney-Davis, Ellis-Sköldberg and Godelle-Paris".
