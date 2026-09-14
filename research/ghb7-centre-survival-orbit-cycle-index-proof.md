---
rg: 2
id: ghb7-centre-survival-orbit-cycle-index-proof
kind: route
title: The equivariant homology spectral sequence has only a d_2 of exponent 7 between orbit cycles and group homology, since vertex groups have exponent 7
target: ghb7-centre-survival-iff-unbounded-orbit-cycle-indices
requires:
  - cckw-ghb2-kms-group-structure
  - z-extension-centre-orders-are-restricted-evaluation-indices
---

## Proof

1. **Exponent of stabilizers.** `ψ` is injective on each `X_i` (`cckw-ghb2-kms-group-structure`,
   item 5). A finite 7-group in `GL_4(F_7)` consists of unipotent matrices, so every `g ∈ X_i`
   satisfies `(g − 1)^4 = 0` and `g^7 = (1 + (g−1))^7 = 1 + (g − 1)^7 = 1` in characteristic 7.
   So every vertex stabilizer, and every subgroup of one, has exponent dividing 7.
2. **Spectral sequence (standard; Brown, *Cohomology of Groups*, VII.7).** `N` acts cellularly on
   the contractible 2-complex `Y` with finite stabilizers and no orientation reversal (edges are
   fixed pointwise by their stabilizers). So there is a spectral sequence
   `E^2_{p,q} = H_p(N\Y; ℋ_q) ⇒ H_{p+q}(N;Z)` with `ℋ_q(σ) = H_q(N_σ;Z)`, and `E^2_{p,0} = H_p(N\Y;Z)`.
   - The only differential leaving `E_{2,0}` is `d^2 : E^2_{2,0} → E^2_{0,1}`, because `p <= 2`.
   - `E^2_{0,1}` is a quotient of `⊕_v H_1(N_v;Z)`, which has exponent dividing 7 by item 1.
   - So `7·H_2(N\Y;Z) <= E^∞_{2,0} = Ker d^2 <= H_2(N\Y;Z)`, and the edge map
     `H_2(N;Z) → H_2(N\Y;Z)` has image `E^∞_{2,0}`.
3. **Pairing.** Naturality of the edge map under `N <= K` gives `⟨e^*ω, i_*x⟩ = ⟨ω, p_* e_N(x)⟩`
   for `x ∈ H_2(N;Z)`. By item 2,
   `7·ω(p_* Z_2(N\Y)) <= c(i_*H_2(N;Z)) <= ω(p_* Z_2(N\Y))` inside `Z`, which is item 1.
4. **Item 2.** `H_1(K~)` is finite iff `c(H_2(K;Z)) != 0` (the five-term sequence, as in
   `z-extension-centre-orders-evaluation-index-proof`, with `N = K`). By item 3 at `N = K`,
   `c(H_2(K)) != 0` iff `ω(Z_2(K\Y)) != 0`.
5. **Item 3, (⇐).** Given `K, ω`, put `c = e^*(ω)`. It has finite abelianization by item 2. By
   `z-extension-centre-orders-are-restricted-evaluation-indices`, the centre orders in finite
   quotients of `K~` have supremum `sup e(N) >= sup m_ω(N) = ∞`.
6. **Item 3, (⇒).** Let `K~` have class `c` with `c(H_2(K)) != 0` and unbounded centre orders.
   - Rationally `H^2(K\Y;Q) ≅ H^2(K;Q)`, as in `ghb7-normal-subgroup-b2-orbit-euler-proof`, and the
     relevant groups are finitely generated. So some integer `m != 0` and integer cochain `ω` give
     `m·c = e^*(ω) + t` with `t` torsion.
   - Torsion classes pair to zero with `H_2`, so `e_{mc}(N) = e_{e^*ω}(N)`. By scaling,
     `sup e_{e^*ω}(N) = |m|·sup e_c(N) = ∞`.
   - Then `sup m_ω(N) >= sup e_{e^*ω}(N)/7 = ∞`, and `ω` is nonzero on `Z_2(K\Y)` because `c` is
     non-torsion on `H_2(K)`.
   - Normal subgroups of `G` suffice: normal cores in `G` have finite index and decrease the lattice
     `p_*Z_2`, so they increase `m_ω`. ∎
