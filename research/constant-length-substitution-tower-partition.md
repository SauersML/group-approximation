---
rg: 2
id: constant-length-substitution-tower-partition
kind: claim
title: For a primitive substitution ζ of constant length q with a non-periodic fixed point, ζ is a homeomorphism of the two-sided subshift X onto a clopen V with X = V ⊔ TV ⊔ … ⊔ T^(q−1)V and ζ∘T = T^q∘ζ
artifacts:
  - research/artifacts/sk-verify-14-2026-09-13-part4.md
---

**ESTABLISHED (unreviewed derivation from Mossé; sk-free-8).** Let `ζ` be a primitive substitution of constant length `q` with a non-periodic fixed point. Let `X` be its two-sided subshift: all bi-infinite sequences whose finite windows lie in the language. Then:
1. `ζ(Tx) = T^q ζ(x)`;
2. `ζ: X → X` is injective;
3. `V = ζ(X)` is clopen, and `X = ⊔_(k<q) T^k V`.

So `(V, T^q|_V) ≅ (X,T)`.

The same statement is attributed to Mossé in the secondary literature: "the substitution τ: X_τ → τ(X_τ) is one-to-one, and moreover, the collection {σ^kτ(X_τ): k = 0,…,ℓ−1} is a clopen partition of X_τ" (Donoso–Durand–Maass–Petite, as quoted by a web search, not opened).

Route: `constant-length-substitution-tower-partition-proof`.

**Review (sk-verify-14, 2026-09-13): PASS, conditional on the literature import `mosse-bilateral-recognizability`.** Re-derived the derivation from Mossé's two theorems: the cut set is a coset of `qZ` with a continuous phase, `ζ(X) = V_0` by unique desubstitution, and the inverse is continuous. Mossé 1996 was fetched on MSI (numdam) but its text was not re-read. The elementary Thue–Morse proof was re-derived independently of Mossé. See `research/artifacts/sk-verify-14-2026-09-13-part4.md` §4.
