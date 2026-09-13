---
rg: 2
id: steinberg-gl-max-mf-quotient-is-low-degree-homology
kind: claim
title: Open — for a locally compressible minimal ample groupoid, is the maximal MF quotient K_1(A_k(𝒢)) of GL_n equal to (H_0(𝒢) ⊗ k^x) ⊕ H_1(𝒢)
distinct_from:
  irreducible-sft-leavitt-gl-max-mf-quotient-formula: that proves the formula for Leavitt path algebras of finite graphs from the Ara–Brustenga–Cortiñas sequence; this asks it for every locally compressible minimal groupoid, where no such sequence is available
  li-derived-full-group-homology-is-k-theory-cover: that is Li's theorem on the homology of derived full groups through the groupoid K-theory spectrum; this is about algebraic K_1 of the Steinberg algebra, a different spectrum
---

**OPEN.** Let `𝒢` be second countable, Hausdorff, ample, minimal and effective, with compact infinite unit space,
and satisfying (PI) of `purely-infinite-steinberg-gl-max-mf-quotient-is-k1`. Let `k` be a countable field.
Is there a natural isomorphism

`K_1(A_k(𝒢)) ≅ (H_0(𝒢) ⊗ k^×) ⊕ H_1(𝒢)`?

By `purely-infinite-steinberg-gl-max-mf-quotient-is-k1` this would make the maximal MF quotient of every
`GL_n(A_k(𝒢))` a groupoid-homology group in degrees 0 and 1.

**Evidence.** It holds for finite graphs satisfying the hypotheses of
`irreducible-sft-leavitt-gl-max-mf-quotient-formula`, given Cuntz's `K_*(O_A)` (recalled) and Matui's
`matui-sft-groupoid-homology-is-k-theory`.

## Attempts

- **Low-degree spectral sequence.** A first-quadrant spectral sequence `E^2_(p,q) = H_p(𝒢; K_q(k)) ⇒ K_(p+q)(A_k(𝒢))`
  would give an exact sequence `H_2(𝒢;ℤ) → H_0(𝒢; k^×) → K_1 → H_1(𝒢;ℤ) → 0`. With `H_1` free, it splits.
  - **Where it dies.** No such spectral sequence for algebraic K-theory of Steinberg algebras is known to this
    lane. Li's arXiv:2209.08087 gives one for the spectrum `K(B_𝒢)` of compact open bisections, whose homotopy
    groups are not algebraic `K_*(A_k(𝒢))`.
  - **Firewall.** Even in the C*-world the HK conjecture fails in general (Scarparo; Deeley, recalled), so any
    proof must use (PI), minimality or torsion-freeness.
- **Via the full group.** `[[𝒢]] → A_k(𝒢)^× → K_1` should land the index part in `H_1(𝒢)` (Matui's index map),
  and the diagonal units `LC(X, k^×)` should give `H_0(𝒢) ⊗ k^×`.
  - **Missing steps.** Surjectivity onto `K_1` from these two pieces, and injectivity of the combined map. The
    first needs that every unit of a purely infinite simple Steinberg algebra is, modulo commutators, a product of a
    full-group unit and a diagonal unit. That is a normal-form statement not yet proved.
- **Degree 0 first.** Is `ι : H_0(𝒢) → K_0(A_k(𝒢))` an isomorphism under (PI)? This is the `K_0` analogue, and
  it overlaps `type-semigroup-reflects-paradox-of-steinberg-algebra` (surjectivity of `S(𝒢) → V(R)`).
