---
rg: 2
id: stably-finite-algebras-need-not-be-linear-sofic
kind: claim
title: Some finitely generated stably finite algebra over every field is not linear sofic
artifacts:
  - research/artifacts/un-prior-art-2026-09-13-part2.md
---

**ESTABLISHED by citation** (`stably-finite-algebras-need-not-be-linear-sofic-citation`). B. Greenfeld, *Stable finiteness
does not imply linear soficity*, arXiv:2210.11650, read from the TeX source on MSI on 2026-09-13.

- **Definition used** (Greenfeld, after Arzhantseva–Păunescu): "A countably generated algebra $A$ over a field $F$ is linear
  sofic if there exists an injective homomorphism $\Phi\colon A\rightarrow \prod_{k\rightarrow \mathcal{U}} M_{n_k}(F) /
  \Ker(\rho_\mathcal{U})$."
- **Necessity of stable finiteness** (Greenfeld, just before the theorems): "It is straightforward to check that any metric
  ultraproduct $\prod_{k\rightarrow \mathcal{U}} M_{n_k}(F) / \Ker(\rho_\mathcal{U})$ is stably finite, hence every linear sofic
  algebra is."
- **Thm `main`.** "Over an arbitrary field, there exists a finitely generated non linear sofic algebra which satisfies a
  polynomial identity and is thus stably finite."
- A second theorem (`main_jac`) gives a finitely generated non linear sofic algebra that is Jacobson radical, built from the
  Cohn–Sasiada construction. Its statement about the unital hull is not quoted here.

**Scope for the UN program.** At ring level, stable finiteness is necessary for a rank-metric matricial model but not
sufficient. The examples are not simple: a finitely generated simple PI algebra is finite-dimensional over its centre. So the
converse question (U3) for SIMPLE rings is not settled by this theorem.
