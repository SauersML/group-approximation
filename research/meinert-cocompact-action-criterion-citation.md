---
rg: 2
id: meinert-cocompact-action-criterion-citation
kind: route
title: Import the Meier–Meinert–VanWyk cocompact-action criterion and the definition of Sigma^m as quoted by Zaremsky, and derive finite-index invariance
target: meinert-cocompact-action-criterion
requires: []
---

Citation import plus a short derivation, read 2026-09-18.

**Source.** M. C. B. Zaremsky, *Geometric structures related to the braided Thompson groups*, arXiv:1803.02717. Read from
the arXiv LaTeX source (`BNSR_BF_.tex`, SHA-256
`f50b6de180a10e13ab399a3b7bc0cfb6962adde1b2ec3960dc6d9de1fdf41b09`), Subsection `sec:bnsr`. The same quotations
appear in `research/artifacts/pure-braid-twist-nonvanishing-sigma-2026-09-16.md`, Section 1, item (T1).

- **(MMV)** Citation `cit:stab_restrict`, credited "[MMV01, Theorem 2.4]" (J. Meier, H. Meinert and L. VanWyk, *On
  the Σ-invariants of Artin groups*, Topology Appl. 110 (2001), 71–81), verbatim up to typesetting: "Let G be a group
  acting cocompactly on an (m−1)-connected complex X. Let χ∈Hom(G,ℝ) be a character such that for any cell σ in X
  with dimension dim(σ)≤m, the restriction χ|Stab_G(σ) is non-trivial. If for all σ with dim(σ)<m, we have that
  Stab_G(σ) is of type F_{m−dim(σ)} and [χ|Stab_G(σ)]∈Σ^{m−dim(σ)}(G_σ), then [χ]∈Σ^m(G)."
- **(Def)** Definition `def:bnsr`: "Suppose a group G acts cellularly and cocompactly on an (m−1)-connected
  CW-complex X such that the stabilizer of each p-cell is of type F_{m−p} … For 0≠χ∈Hom(G,ℝ) such that every
  stabilizer lies in ker(χ), we can choose a map h_χ: X→ℝ satisfying h_χ(g.x)=χ(g)+h_χ(x) … Σ^m(G) := {[χ] |
  (X_{χ≥t})_{t∈ℝ} is essentially (m−1)-connected}". Also: "It turns out Σ^m(G) is well defined up to the choice of X
  and h_χ (see for example [bux04, Definition 8.1])."
- **(Mon)** "The BNSR-invariants are certain subsets Σ^1(G)⊇Σ^2(G)⊇⋯ of Σ(G)".

The MMV paper itself was not re-read; only the quoted statement is imported.

## Derivation of (FI) and (Conj)

**(FI).** Let `H` have type `F_m`, `H' <= H` of finite index, and `χ in Hom(H,R)` nonzero. Then `χ|_{H'} != 0`,
since `R` is torsion free. `H'` has type `F_m`: a `K(H,1)` with finite `m`-skeleton has a finite-sheeted cover that is a
`K(H',1)` with finite `m`-skeleton.

- Let `X` be the `m`-skeleton of the universal cover of such a `K(H,1)`. It is `(m−1)`-connected.
- `H` acts on `X` freely and cocompactly. So does `H'`, because `X/H'` is a `[H:H']`-sheeted cover of the finite
  complex `X/H`.
- All stabilizers are trivial, so they lie in `ker χ` and have every finiteness type. Choose `h_χ` for `H`. It also
  satisfies `h_χ(g x) = χ|_{H'}(g) + h_χ(x)` for `g in H'`.
- The two filtrations `(X_{χ≥t})_t` are the same. By (Def), `[χ] in Σ^m(H)` iff `[χ|_{H'}] in Σ^m(H')`.

**(Conj).** If `c: H -> gHg^{-1}` is conjugation by `g in G` and `χ in Hom(G,R)`, then `χ ∘ c = χ|_H`. An isomorphism
carries `Σ^m` to `Σ^m`. So `[χ|_H] in Σ^m(H)` iff `[χ|_{gHg^{-1}}] in Σ^m(gHg^{-1})`. ∎
