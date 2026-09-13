---
rg: 2
id: km-246-completions-kazhdan-howe-moore-citation
kind: route
title: Import the completion properties from Caprace-Thom Section 5 and the lattice lemmas of Creutz-Peterson
target: km-246-completions-are-kazhdan-howe-moore-simple
requires: []
---

All three sources were fetched as arXiv e-prints on MSI on 2026-09-13 and read in TeX.

**Caprace--Thom, arXiv:2606.27993v2, `howemoore.tex`.**
- *Theorem A* (l.99–110): "Let `X` be a thick locally finite building of finite rank and
  type `(W,S)`, and let `G<Aut(X)` be a closed type-preserving subgroup acting
  Weyl-transitively. Let `π: G→U(H)` be a unitary representation. Then at least one of the
  following assertions holds. (i) `π` is mixing. (ii) There is a minimal non-spherical subset
  `J⊂S` such that `π|_{P_J}` is amenable in the sense of Bekka."
- *Proposition 4.1(1)* (`prop:Kazhdan`, l.473–477): "... (1) `D ∈ {(2,4,6), (3,3,4),
  (3,3,3,4), (3,3,3,3,4)}` and `q_min ≥ 3`. [...] Then `G` has Kazhdan's property (T)."
- *Proof of Corollary B*: "Suppose that `π` is not mixing. By Theorem A, there is a minimal
  non-spherical subset `J⊂S` such that `π|_{P_J}` is amenable, i.e.
  `1_{P_J} ≺ (π|_{P_J})⊗conj(π|_{P_J})`. Since `P_J` has property (T) by Corollary
  [`cor:minimal-non-sph:Kazhdan`], this weak containment is actual containment. Thus
  `(π|_{P_J})⊗conj(π|_{P_J})` has a non-zero invariant vector and hence `π|_{P_J}` has a
  finite-dimensional subrepresentation, see [BHV, Proposition A.1.12]."
- *Proof of Corollary BB* (l.582–586): "Let `π` be a unitary representation of `G`. Suppose
  first that `π` contains a finite-dimensional subrepresentation `ρ`. Since `G` is totally
  disconnected and `ρ` takes its values in a finite-dimensional Lie group, the kernel of `ρ`
  is open. Thus `ρ` is trivial on the subgroup `G^+` from Proposition
  [`prop:simple-by-compact`]. It follows that `ρ` factors through a compact quotient of `G`.
  By hypothesis, this implies that `ρ` is the trivial representation. Hence `π` has non-zero
  invariant vectors. Now the Howe--Moore property for `G` follows directly from the dichotomy
  asserted by Corollary B."
- *Proof of Corollary 5.3* (`cor:KM-sharp`, l.711–738): "Let `Δ=Δ_+×Δ_-` be the twin building
  associated with `Λ`, and let `L_±` be the closures of the images of `Λ` in `Aut(Δ_±)`."
  [...] "The minimal Kac--Moody group `Λ/Z` is an irreducible lattice in the automorphism
  group of its twin buildings if and only if `W(1/q)` converges [...] this is indeed the case
  for all `q ≥ 2` by Lemma [`lem:convergence-radius`]." [...] "Moreover the groups `L_+` and
  `L_-` are second countable, non-discrete, non-compact, topologically simple, totally
  disconnected locally compact groups acting strongly transitively on `Δ_+` and `Δ_-`,
  respectively. Each building `Δ_±` has compact-hyperbolic crystallographic type and all
  panels have thickness `q+1`. It follows from Proposition [`prop:Kazhdan`] that `L_+` and
  `L_-` have Kazhdan's property (T), and from Corollary [`corollary_HM_KM`] that they have the
  Howe--Moore property."

**Assembly of Howe--Moore at type `(2,4,6)`, `q ≥ 3`.** The triangle group `(2,4,6)` is
minimal non-spherical, so the only minimal non-spherical subset is `J = S`, and `P_J = L_±`.
Proposition 4.1(1) gives (T) for `L_±`, since every panel has `q+1` chambers and `q ≥ 3`. The
proof of Corollary B runs verbatim with Proposition 4.1(1) in place of
[`cor:minimal-non-sph:Kazhdan`]: every unitary representation of `L_±` is mixing or has a
finite-dimensional subrepresentation. The proof of Corollary BB then runs verbatim. `L_±` is
topologically simple, so `G^+ = L_±`, every finite-dimensional subrepresentation is trivial,
and a representation without invariant vectors is mixing. That is the Howe--Moore property.

**Creutz--Peterson, arXiv:1311.4513v3, `creutzpeterson_revised2.tex`, Lemma 5.2
(`lem:dlattice`).** "Suppose `G` is a locally compact group that is a product of simple
groups, and `Γ<G` an irreducible lattice. Then the intersection of `Γ` with any proper
subproduct of `G` consisting solely of nondiscrete simple groups is trivial." Applied to
`S_q < L_+ x L_-`, the intersections with `L_+ x {e}` and `{e} x L_-` are trivial, so both
projections are injective. Their images are dense because `L_±` is defined as a closure.

**Creutz--Peterson, arXiv:1303.3949,
`Stabilizers_of_Ergodic_Actions_of_Lattices_and_Commensurators.tex`, proof of Theorem 9.1
(`T:BSbetter`, l.3149–3160).** "Write `G=G_0×H` and let `K` be a compact open subgroup of `H`.
Let `L=Γ∩(G_0×K)`. Then `proj_K L` is dense in `K` since `Γ` is irreducible. `L` is a lattice
in `G_0×K` since `K` is open. Set `Γ_0=proj_{G_0} L`. Since `K` is compact, `Γ_0` has finite
covolume in `G_0` since `L` does in `G×K`. Moreover, `Γ_0` is discrete since `L` is discrete.
Therefore `Γ_0` is a lattice in `G_0`. Set `Λ_0=proj_{G_0} Γ`. Then `Λ_0` is dense in `G_0`
since `Γ` is irreducible and `Γ_0 <_c Λ_0` since `K <_c H`." With `G_0 = L_+`, `H = L_-`,
`K = K_-` and `Γ = S_q`, this is (KHM4) apart from (T). Property (T) of the lattice `Λ_+` in
the Kazhdan group `L_+` is Bekka--de la Harpe--Valette, Theorem 1.7.1.
