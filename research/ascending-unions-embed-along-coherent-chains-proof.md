---
rg: 2
id: ascending-unions-embed-along-coherent-chains-proof
kind: route
title: Restrict an embedding to the chain, and glue coherent embeddings of the terms
target: ascending-unions-embed-along-coherent-chains
requires: []
---

Direct proof. Not independently reviewed.

- **1 ⇒ 2.** Restrict an embedding `iota : H -> Gamma` to each `H_m`.
- **2 ⇒ 1.** Every element of `H` lies in some `H_m`, so the `iota_m` fit together
  into a well-defined homomorphism `H -> Gamma`. It is injective, because a
  nontrivial element of `H` lies in some `H_m`, where `iota_m` is injective.
- **2 ⇒ 3.** Take every `g_m = 1`.
- **3 ⇒ 2.** Put `h_1 = 1` and `h_(m+1) = h_m g_m^-1`, and set
  `iota'_m = c(h_m) o iota_m`. Then
  `iota'_(m+1)|H_m = c(h_m g_m^-1) o c(g_m) o iota_m = c(h_m) o iota_m = iota'_m`,
  and each `iota'_m` is injective.

**Class form.**
- Choose `iota_1` in `C_1`.
- Given `iota_m` in `C_m`, choose `iota_(m+1)` in `C_(m+1)` whose restriction to
  `H_m` lies in `C_m`. That restriction is conjugate to `iota_m`, because `C_m` is
  a single conjugacy class.

This gives the data of 3. ∎

**Instances.** For `GL_n(Q)`: a rational matrix `g` with rational inverse has
entries of `g` and `g^-1` with denominators dividing some `m!`. So `g` lies in
`GL_n(Z[1/m!])`, and `GL_n(Q) = union_m GL_n(Z[1/m!])`.
