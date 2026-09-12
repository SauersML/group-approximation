---
rg: 2
id: principal-ideal-affine-groups-are-self-similar-citation
kind: route
title: Import Zaremsky's Corollary 4.5 and Example 4.7 and check stability for subgroups of GL_n(R)
target: principal-ideal-affine-groups-are-self-similar
requires: []
artifacts:
  - research/artifacts/bh-metabelian-products-2026-09-12.md
---

Citation import. M. C. B. Zaremsky, *Embedding finitely presented self-similar
groups into finitely presented simple groups*, arXiv:2405.09722, Bull. London
Math. Soc. 2025.

Read from the PDF text extracted on MSI
(`/scratch.global/sauer354/bh-reviewer/2405.09722.txt`) on 2026-09-12:

- **Definition 4.2**, verbatim: "Let A be a group and Γ ≤ Aut(A). Let φ be a
  virtual endomorphism of A. We say that φ is Γ-stable if γ(φ^−n(A)) = φ^−n(A)
  for all γ ∈ Γ and all n ∈ N. Now assume φ is bijective. Call φ and Γ mutually
  stable if φ is Γ-stable and φΓφ^−1 ≤ Γ."
- **Properness**, verbatim: "Let us call a virtual endomorphism φ of A proper if
  the intersection of the iterated preimages φ^−n(A) for all n ∈ N is trivial."
- **Corollary 4.5**, verbatim: "Let A be a group with a surjective, proper virtual
  endomorphism φ. Let Γ≤Aut(A) such that φ and Γ are mutually stable. Then A⋊Γ is
  a self-similar group. If it is finitely presented, then it, and hence all of its
  subgroups, satisfy the Boone–Higman conjecture."
- **Example 4.7:**
  - *Hypotheses:* "Let R be a ring, viewed as an additive abelian group, and
    suppose R has a principal left ideal J = Rx of finite index. Assume x is not
    a zero-divisor, so we have a group homomorphism ϕ: J → R given by rx ↦ r."
  - *The endomorphism:* φ = ϕ^⊕n is "a surjective virtual endomorphism of
    A = R^⊕n".
  - *Properness:* "Assume that ∩_k Rx^k = {0}; for example this holds if R is a
    noetherian integral domain and J is proper, thanks to the Krull intersection
    theorem. Since φ^−k(A) = (Rx^k)^⊕n, this means that the virtual endomorphism
    φ is proper."
  - *Conclusion:* "Finally, let Γ = GL_n(R). Since J is a left ideal, and since
    scaling by x on the right commutes with multiplying by a matrix on the left,
    φ and GL_n(R) are mutually stable. Now we conclude from Corollary 4.5 that
    R^⊕n ⋊ GL_n(R) is self-similar".

**Subgroups of GL_n(R).** Let `Γ <= GL_n(R)`.
- *φ is bijective.* It is injective because `x` is not a zero divisor, and
  surjective by construction.
- *Γ-stable.* `φ^-k(A) = (Rx^k)^n`, and `Rx^k` is a left ideal. So every `γ in Γ`
  maps `(Rx^k)^n` into itself, and so does `γ^-1 in Γ`. Hence
  `γ(φ^-k(A)) = φ^-k(A)`.
- *φΓφ^-1 <= Γ.* `φ^-1` is right scaling by `x`, which commutes with left
  multiplication by `γ`. So `φ ∘ γ ∘ φ^-1 = γ`.
- *Conclusion.* `φ` and `Γ` are mutually stable in the sense of Definition 4.2.
  Surjectivity and properness do not involve `Γ`, so Corollary 4.5 gives that
  `R^n x| Γ` is self-similar.

Not reproved beyond this check; no Lean counterpart.
