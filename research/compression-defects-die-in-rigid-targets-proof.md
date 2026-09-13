---
rg: 2
id: compression-defects-die-in-rigid-targets-proof
kind: route
title: Conjugate the centralizer through a rigid support; rigidity by counting or by Zariski dimension
target: compression-defects-die-in-rigid-targets
requires: []
artifacts:
  - research/artifacts/un-open-8-target-agnostic-compression-2026-09-13.md
---

**Lemma C.**
- `ψ(c)` commutes with `ψ(L)`, hence with `S`.
- So `ψ(ucu^-1) = ψ(u)ψ(c)ψ(u)^-1` commutes with `ψ(u)Sψ(u)^-1 = S`, which contains `ψ(l)`.
- Hence `ψ([ucu^-1,l]) = 1`.
- `ker ψ` is normal, so it contains `D_G(L)` once every generator dies.

**Finite `H`.** Put `S = ψ(L)`. Then `ψ(u)Sψ(u)^-1 = ψ(uLu^-1) ⊆ S`, both of cardinality `|S|`, so equality holds.

**`H = GL_d(K)`.** Work in `GL_d(K̄)` and let `S` be the Zariski closure of `ψ(L)`.
- Centralizers of single elements are closed, so anything commuting with `ψ(L)` commutes with `S`.
- Conjugation by `ψ(u)` is a variety automorphism, so `ψ(u)Sψ(u)^-1` is the closure of `ψ(uLu^-1) ⊆ ψ(L)`, hence
  contained in `S`, and isomorphic to `S` as a variety.
- Each irreducible component of it is closed irreducible of dimension `dim S` inside `S`, hence a component of `S`.
- It has as many components as `S`, so it equals `S`.

**`ψ = id`.** This is the statement that finite and linear groups have trivial defects.

Full text: artifact §1–§2.
