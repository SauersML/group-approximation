---
rg: 2
id: popa-vanishing-cohomology-amplification-and-ce-imports-citation
kind: route
title: Import Popa's amplification non-vanishing theorem, the normalizer reformulation of CAE and the wreath-product remark verbatim
target: popa-vanishing-cohomology-amplification-and-ce-imports
requires: []
---

**Source.** S. Popa, *On the vanishing cohomology problem for cocycle actions of groups on II_1 factors*,
arXiv:1802.09964. The PDF was fetched from arxiv.org and its text extracted and read on 2026-09-18. The quotes
below are verbatim. Ligatures, line breaks and sub/superscript placement are normalized; `R^omega` and `R_omega`
are written as in the text ("Rω" is `R^omega`, "Rω := R′ ∩Rω" is `R_omega`).

- **Cocycle actions (Section 1.1, (1.1.1), (1.1.2)).** "a cocycle action σ of Γ on N is a map σ : Γ → Aut(N) with
  the property that there exists v : Γ × Γ → U(N) such that: σe = id and σgσh = Ad vg,hσgh, ∀g,h ∈ G (1.1.1)
  vg,hvgh,k = σg(vh,k)vg,hk, ∀g,h,k ∈ Γ. (1.1.2) The cocycle action σ is free if σg cannot be implemented by unitary
  elements in N, ∀g ≠ e". And: "All 2-cocycles considered from now on will be normalized."
- **Crossed product.** "Then we let Ug · ∑hUhξh = ∑hvg,hUghξh" and "x(∑hUhξh)y = ∑hUh(σh^{-1}(x)ξhy)". "The
  ∗-algebra H0 has a trace given by τ(∑hUhxh) = τN(xe)". "The crossed product von Neumann algebra N ⋊(σ,v) Γ is by
  definition the weak operator closure of M0 in B(H)."
- **Freeness.** "The cocycle action (σ,v) is free if σg is an outer automorphism, ∀g ≠ e. It is well known (and
  immediate to check) that (σ,v) is free if and only if N′∩N ⋊(σ,v)Γ = C1."
- **Proposition (Section 1.2).** "Let (σi,vi) be a cocycle action of the discrete group Γi on the II1 factor Ni,
  i = 1, 2. If there exists a ∗-isomorphism Φ : N1⋊(σ1,v1)Γ1 ≃ N2⋊(σ2,v2)Γ2 such that Φ(N1) = N2, then σ1 and σ2
  are cocycle conjugate. More precisely, there exists a group isomorphism γ : Γ1 → Γ2, and unitaries wg ∈ U(N2),
  for all g ∈ Γ1, such that: (i) Φσ1(g)Φ^{-1} = Adwg σ2(γ(g)), for all g ∈ Γ1, (ii) Φ(v1(g,h)) =
  wgσ2(γ(g))(wh)v2(γ(g),γ(h))w∗gh, for all g,h ∈ Γ1. Conversely, if Φ : N1 ≃ N2 is a ∗-isomorphism, γ : Γ1 ≃ Γ2 is
  a group isomorphism, and there exist unitaries wg ∈ U(N2) for all g ∈ G1 such that (i), (ii) are satisfied, then
  Φ can be extended to an isomorphism N1 ⋊(σ1,v1) Γ1 ≃ N2 ⋊(σ2,v2) Γ2 (hence, to an isomorphism of the associated
  inclusions)."
- **Vanishing (Section 1.4).** "The 2-cocycle v for the cocycle action σ vanishes (or it is a coboundary) if there
  exists a map w : Γ → U(N) such that we = 1 and v = ∂w, i.e.: (1.4.1) vg,h = (∂w)g,h := σg(w∗h)w∗gwgh". "The
  2-cocycle v weakly-vanishes (or it is a weak coboundary) if there exists w : Γ → U(N) such that we = 1 and v = ∂w
  modulo scalars". "In turn, the vanishing of v is equivalent to the existence of unitary elements {wg}g ⊂ N such
  that U′g = wgUg ∈ M = N ⋊(σ,v) Γ give a representation of Γ". "by VCw(N) the class of groups Γ for which any
  free cocycle action (σ,v) of Γ on N has the property that v is a weak-coboundary."
- **Definition 3.1 ([P01a]).** "Let Γ ↷σ N be a free action of a group Γ on a type II1 factor N. Let p ∈ N be a
  projection and for each g ∈ Γ choose a partial isometry wg ∈ N such that wgw∗g = p, w∗gwg = σg(p) and we = p.
  Define σ^p_g ∈ Aut(pNp) by σ^p_g(x) = wgσg(x)w∗g, x ∈ pNp. Then σ^p is a free cocycle action of Γ on pNp, with
  2-cocycle v^p_g,h = wgσg(wh)w∗gh, g,h ∈ Γ. Moreover, up to cocycle conjugacy (σ^p,v^p,pNp) only depends on
  τ(p) = t, thus defining a free cocycle action (σ^t,v^t) of Γ on N^t, called the amplification of σ by t."
- **Theorem 3.2.** "Let Γ be a countable group and Γ ↷σ R = R0^{⊗Γ} the non-commutative Bernoulli Γ-action with
  base R0 ≃ R. Let 0 < t < 1 and denote by σt the free cocycle action obtained by amplifying σ by t, with its
  2-cocycle denoted vt. Assume one of the following properties holds true: (a) Γ contains an infinite subgroup with
  the relative property (T); (b) Γ contains an infinite subgroup with non-amenable centralizer. Then the cocycle vt
  is not weak-vanishing."
- **Corollary 3.3.** "If Γ is a group that contains an infinite subgroup which either has relative property (T), or
  has non-amenable centralizer in Γ, then Γ ∉ VCw(R)."
- **Proposition 6.1 1°, 2°.** "Rω := R′ ∩ Rω is a II1 factor whose centralizer in Rω is equal to R, i.e.,
  R′ω ∩ Rω = R." "Given any θ ∈ Aut(R) there exists a unitary element Uθ ∈ N_Rω(R) such that Ad(Uθ)|R = θ. If
  U′θ ∈ N_Rω(R) is another unitary satisfying Ad(U′θ)|R = θ, then U′θ = vUθ = Uθv′ for some v,v′ ∈ U(Rω)."
- **Definition 6.2.** "A II1 factor M (respectively a group Γ) has the CAE property if it can be embedded into Rω
  (respectively into the unitary group of Rω). Note that by a result in [R06], Γ has a faithful representation into
  U(Rω) iff Rω contains a copy of the left regular representation of Γ, equivalently L(Γ) ↪ Rω. Thus, Γ has the CAE
  property iff L(Γ) has the CAE property."
- **Theorem 6.3.** "Let Γ ↷σ R be a free action of a countable group Γ on the hyperfinite II1 factor R. The II1
  factor R ⋊σ Γ has the CAE property if and only if the U(Rω)-valued 2-cocycle vσω vanishes, i.e., iff there exist
  unitary elements {Ug | g ∈ Γ} ⊂ N_Rω(R) that implement σ on R and satisfy UgUh = Ugh, ∀g,h ∈ Γ." Its proof: "If
  M is embeddable into Rω, then by using the fact that any two copies of the hyperfinite II1 factor in Rω are
  conjugated by a unitary element in Rω, it follows that we may assume the hyperfinite subfactor R in M = R ⋊ Γ
  coincides with the algebra of constant sequences in Rω".
- **Remark 6.5.1°.** "It has been shown in [HaS16] that if two groups H, Γ are sofic, then their wreath product
  H ≀ Γ is sofic as well, so in particular it is CAE. Taking H to be an (arbitrary) amenable ICC group H, for which
  by Connes Theorem one has L(H) ≃ R, it follows that the crossed product II1 factor R ⋊σ Γ = L(H ≀ Γ) is CAE,
  where Γ ↷σ R^{⊗Γ} ≃ R is the non-commutative Bernoulli Γ-action with base ≃ R as in 6.4."
- **Remark 6.5.3° (context, not used as a hypothesis).** "But the only exemples of cocycle actions (θ,vθ) on R
  that we know to be “untwistable” are the ones provided by Theorem 3.2, which are amplifications (σt,vt) of the
  Bernoulli Γ-actions" and "As noted in [P01a], if a genuine action has II1 fixed point algebra, then all its
  amplifications can be untwisted."

Items (P1)--(P5) of the target restate these quotes. The target's "equivalently" clause for vanishing is the quoted
sentence on `U'_g = w_g U_g`, and its weak form is (1.4.2′) of the same section. Nothing is re-proved here. ∎
