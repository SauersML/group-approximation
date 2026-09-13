---
rg: 2
id: leavitt-steinberg-map-iso-from-rank-three
kind: claim
title: Over the binary Leavitt algebra the Steinberg map is an isomorphism from rank three and every GL_r is acyclic
distinct_from:
  leavitt-gl-equals-el-and-perfect-unit-group: that proves GL = EL at every rank and perfectness of the unit group, i.e. vanishing first homology; this is the Steinberg comparison isomorphism and vanishing of all higher integral homology of every GL_r.
  finite-root-algebra-forces-steinberg-triviality: that forces one class of Steinberg representations to be trivial; this identifies the Steinberg group with GL_r itself, a statement about groups with no representation in it.
  leavitt-unit-group-finitely-presented: that is finite presentability of the unit group, which the source derives from this comparison; this is the comparison and the homology computation themselves.
artifacts:
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
---

**ESTABLISHED (literature import).** Let `R = L_(F_2)(1,2)`. Then

```text
H_n(GL_r(R); Z) = 0         for every n > 0 and r >= 1,        (KH1)
St_r(R) -> GL_r(R) is an isomorphism   for every r >= 3.        (KH2)
```

Source: H. V. Khanh, arXiv:2609.08428v1 (8 September 2026), **Theorem 4.4**
for `(KH1)` and **Theorem 5.4** for `(KH2)`. Lemma 5.3 there gives
`GL_m(R) = E_m(R)` for `m >= 2`, matching
`leavitt-gl-equals-el-and-perfect-unit-group`. Statements were checked against
the PDF text; proofs have not been reviewed here. The paper makes no assertion
about the Steinberg kernel at rank two.

## Consequences recorded in prose, for the lanes that own them

- **Leavitt–Steinberg fork.** For `U = St_5(L)` and `Q = EL_4(L)`, `(KH2)` and
  the prefix-code ring isomorphisms `M_n(L) ≅ L` give `U ≅ GL_5(L) ≅ L^x ≅ Q`.
  The kernel called central in the unstable branch of
  `leavitt-steinberg-hs-stability-fork` is trivial, and `U` is simple
  (`binary-leavitt-unit-group-is-simple`). The fork therefore says that `L^x` is
  normalized-HS stable exactly when it is nonhyperlinear.
- **Schur multiplier.** `(KH1)` with `r = 1` gives `H_2(L^x; Z) = 0`, so `L^x`
  is superperfect and is its own universal central extension.
