---
rg: 2
id: dyadic-affine-bs12-model-lies-in-no-finite-nucleus-rsg
kind: claim
title: The dyadic coding of the affine action of BS(1,2) on the extended real line is a rational action with a in Thompson's group F and a not equicontinuous, but no rational similarity group with finite nucleus contains it
distinct_from:
  bs12-embeds-in-brin-thompson-2v: that embeds BS(1,2) in the Brin--Thompson group 2V; this is a one-dimensional rational model with a non-equicontinuous generator and an obstruction to finite-nucleus hosts for it.
  rsg-proper-power-conjugate-germs-torsion-at-finite-orbits: that is the general germ statement; this applies it to one explicit model at a common fixed point.
artifacts:
  - research/artifacts/bh-bg-rsg-nonisometric-hosts-2026-09-13.md
---

**ESTABLISHED** (elementary; no novelty claimed).

**The model.** On `{0,1}^N`, define `a` and `b` as follows, for `n ≥ 0`,
`y ∈ {0,1}` and any infinite word `v`. Both fix `0^∞` and `1^∞`.
- `a(00v) = 0v`, `a(01v) = 10v`, `a(1v) = 11v`.
- `b(1^(n+1) 0 y v) = 1^(2n+1+y) 0 v` and `b(0^(n+1) 1 y v) = 0^(2n+2-y) 1 v`.

This is `x ↦ x+1` and `x ↦ 2x` on `R ∪ {±∞}`, in the coding where
`1^(n+1) 0 y_1 y_2 …` is `n + 0.y_1y_2…` and `0^(n+1) 1 y_1 y_2 …` is
`-(n+1) + 0.y_1y_2…`.

**Statement.**
1. `b a b^-1 = a^2`, and `<a, b> ≅ BS(1,2)`.
2. `a` lies in Thompson's group `F`. `b` is a rational homeomorphism. `<a>` is not
   equicontinuous.
3. No subgroup of the rational group of the full binary shift that is an RSG with
   finite nucleus contains both `a` and `b`.

**Why it matters for Boone--Higman hosts.** A Cantor-space host for the
Baumslag--Gersten group needs a non-equicontinuous `a`
(`baumslag-gersten-equicontinuous-generator-acts-trivially`). This is the natural
rational model with that property. Its local actions are not isometries, so it is
not in any almost-automorphism group of a graph path space. It is excluded from
finite-nucleus RSGs at the common fixed point `1^∞`. There `b` scales the
canonical shift germ of `a` to its square.

The proof is `dyadic-affine-bs12-germ-at-infinity-proof`.
