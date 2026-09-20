---
rg: 2
id: sp4-forms-have-central-congruence-kernel-citation
kind: route
title: Import Rapinchuk's centrality theorem for classical groups of types B_n and C_n with n at least two and S-rank at least two, and match its congruence kernel with Stover's
target: sp4-forms-have-central-congruence-kernel
requires: []
---

## Sources, verbatim

**[R] A. S. Rapinchuk, *Congruence subgroup problem for algebraic groups: old and new*, Astérisque 209 (1992)
73-84.** The scan was fetched from https://www.numdam.org/item/AST_1992__209__73_0.pdf on 2026-09-20.

- p. 73, setting: "Let G C GL n be an algebraic group defined over an algebraic number field K. Let S be a
  finite subset of the set VK of all valuations of K, containing the set V∞K of archimedean valuations. Denote by
  O(S) the ring of S-integers in K and by GO(S) the group of S-units in G."
- p. 74, definition: "The complete system of neighbourhoods of unity for τa (resp., τc) consists of all normal
  subgroups of finite index (resp., all congruence subgroups) in GO(S). ... Therefore it can be extended to a
  continuous homomorphism π: Ĝ → Ḡ of the completions. By definition, CS(G) = Ker π is the congruence kernel".
- p. 78, **Theorem 1**. The wording below was read from the page image, because the text layer turns `≥` into
  `>`: "Let G be a simple, simply connected K-group of one of the following types Bn (n ≥ 2), Cn (n ≥ 2),
  Dn (n ≥ 5), G2 or the special unitary groups, SUm(f) (m ≥ 4), of a nondegenerate hermitian form f over some
  quadratic extension L/K belonging to the type 2Am−1. Assume that rangS G ≥ 2 and, moreover, if G is of type
  C3 then either S contains a nonarchimedean valuation or such an archimedean valuation v that rangKv G ≥ 2.
  Then CS(G) is central."
- p. 77, context showing that this covers anisotropic groups: "The argument in all these papers was based on
  some manipulations with unipotent elements in GK, and so no version of it can be applied to anisotropic
  groups. Until recently, the only result which allowed also anisotropic groups was Kneser's theorem [6] for
  spinor groups of quadratic forms. But then Rapinchuk [21], [22] and Tomanov [29] extended this theorem to all
  groups having a nice geometric realization."

**[PR] G. Prasad and A. S. Rapinchuk, *Developments on the congruence subgroup problem after the work of Bass,
Milnor and Serre*, arXiv:0809.1622.** This source is consistency context and is not used in any step.

- §3.1: "define the S-rank rkSG of G as the sum of relative ranks rkkvG, of G over the completions kv, for
  v ∈ S."
- §5.1: "At the time of this writing, the centrality of CS(G) in the higher rank case of Serre's conjecture is
  not known for any anisotropic inner form, and for most of the anisotropic outer forms, of type An, for the
  anisotropic triality forms of type D4, and for most of the anisotropic groups of type E6." Type C_2 is not
  on this list of open cases.

**[St] M. Stover, arXiv:2407.07680v2, pp. 10-11, as already quoted in
`deligne-homogeneous-bundle-models-die-at-lattice-residual-proof`.**

- "The topology induced by the proﬁnite topology on G(Ok), where the basic open neighborhoods of Id ∈ G(k) are
  the ﬁnite index subgroups of G(Ok)."
- "The topology induced by the congruence topology on G(Ok), where now the basic open neighborhoods of
  Id ∈ G(k) are the ﬁnite index subgroups of G(Ok) that contain the kernel of the reduction homomorphism
  G(Ok) → G(Ok/I) modulo a nonzero ideal I ⊆ Ok."
- "Then G is said to have the congruence subgroup property if C(k) is central in ˆG(k)."

In the [R] quotes from pp. 73-74, OCR misreadings of the text layer were corrected against the scan:
`5 -> S`, `V*£ -> V∞K`, `7r -> π`, `Kenr -> Ker π`, and the hats and bars on the completions.

## Matching the hypotheses

Let `H` be as in the target and put `S = V_inf`. `S` is finite and consists of the archimedean places, as [R]
requires.

1. *Type.* `H` is absolutely almost simple, which is what [R] calls "simple" ([R] p. 74: "the main case of an
   (absolutely) simple, simply connected algebraic group G"). It is simply connected of absolute type `C_2`, so
   Theorem 1 applies through the entry `Cn (n ≥ 2)`, or through `Bn (n ≥ 2)` since `B_2 = C_2`.
   - The absolute type does not change under extension of scalars.
   - For this reason no identification with a spinor group, or with a hermitian form over a quaternion algebra,
     is needed.
   - The extra condition in Theorem 1 concerns only type `C_3`, so it does not apply.
2. *Rank.* `rang_S H = sum over v in V_inf of rank_(k_v) H >= rank_(k_v0) H = 2`, so the hypothesis
   `rang_S G ≥ 2` holds.
   - When `H` comes from a lattice of `Sp_4(R)`, `v0` is the place where `H(k_v0)` maps onto the noncompact
     factor.
   - The other real places are compact, so in fact `rang_S H = 2`.
3. *Conclusion.* By [R] Theorem 1, `C^S(H)` is central.

## Matching the definition with Stover's

- With `S = V_inf`, `O(S) = O_k` and `H_(O(S)) = H(O_k)`.
- The two arithmetic topologies are the same. [R]'s neighbourhoods are the normal subgroups of finite index in
  `H(O_k)`. Stover's are all subgroups of finite index. Every finite-index subgroup contains its normal core,
  which again has finite index.
- The congruence topologies coincide by definition.
- So [R]'s completions `Ĥ` and `H̄` are Stover's `ˆH(k)` and `H'(k)`, and `C^(V_inf)(H) = C(k)`. Centrality of
  `C^S(H)` in `Ĥ` is exactly Stover's congruence subgroup property for `H`.

This completes the route. Its only imported input is [R] Theorem 1.
