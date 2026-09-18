---
rg: 2
id: cantor-crossed-q-rings-need-odd-divisible-coinvariants
kind: claim
title: Over a torsion-free Farrell-Jones group, clopen symbols detect the odd part of the dimension group tensor K_2(Q), so Cantor-crossed Q-hosts need odd-divisible coinvariants
distinct_from:
  cantor-crossed-clopen-symbols-factor-through-coinvariants: that proves the clopen symbols factor through D_X ⊗ K_2(Q); this asks that the odd part of that map be injective, which turns non-divisibility of D_X into an obstruction.
  fjc-crossed-products-of-k-trivial-regular-rings-vanish: that treats coefficient rings with K(R) = 0; this uses the same assembly for R = LC(X,Q), whose K-theory is LC(X,Z) ⊗ K_*(Q).
  minimal-cantor-crossed-product-k-theory-formula: that is the case Γ = Z over F_q, where the E_(0,n) term K^0 ⊗ K_n(F_q) is a direct summand; this is the degree-2 edge term for any torsion-free Farrell-Jones group over Q.
artifacts:
  - research/artifacts/gq-gq-k2-q-toeplitz-k2.md
---

**OPEN.** Let `Γ'` be a torsion-free group satisfying the `K`-theoretic Farrell–Jones conjecture with
additive categories as coefficients, with respect to `VCyc`. Let `Γ'` act on a compact totally
disconnected space `X`, put `B = LC(X,Q) ⋊_alg Γ'` and `D_X = H_0(Γ'; LC(X,Z))`. Then for every odd prime
`ℓ` the `ℓ`-primary part of `σ : D_X ⊗ K_2(Q) -> K_2(B)` of
`cantor-crossed-clopen-symbols-factor-through-coinvariants` is injective.

## Consequences if true

1. **Obstruction.** Suppose `D_X / ℓ D_X ≠ 0` for one odd prime `ℓ`. Choose the infinitely many primes
   `p ≡ 1 mod ℓ` (Dirichlet). Each contributes the nonzero summand `D_X ⊗ (F_p^x)[ℓ^∞]` to the image of
   `σ`. So the clopen symbols of `B` generate an infinitely generated group.
   - For every ring `R ⊇ B` through which this stays injective, `E_N(R)` is not finitely presented for
     any `N >= 3` (`infinitely-generated-symbols-block-fp-elementary-groups`).
   - It fails at every full clopen corner whose class is not `ℓ`-divisible
     (`full-corners-must-kill-rational-k2-symbols`).
2. **Harmonic rings.** For `R = F ⋊ Γ'` with `F` the harmonic coefficient ring,
   `harmonic-coefficient-rings-are-k-equivalent-to-lc` reduces the passage from `B` to `R` to the twisted
   Nil terms of `F` under infinite cyclic subgroups.
3. **Groups with torsion.** For `SL_3(Z)` acting on a space with an odometer factor, pass to the
   torsion-free `Γ(d)`, `d >= 3`, through the block Morita equivalence
   `LC(X,Q) ⋊ Γ ≅ M_n(LC(C,Q) ⋊ Γ(d))`, where `C` is a block. This needs Farrell–Jones for subgroups of
   `GL_n(Z)`: Bartels–Lück–Reich–Rüping, arXiv:1204.2418, whose abstract reads "We prove the K- and
   L-theoretic Farrell-Jones Conjecture (with coefficients in additive categories) for GL_n(Z)", together
   with inheritance to subgroups, which was not quoted.

**Test case.** For `R_T` the question is moot on the host route: `bounded-harmonic-rings-are-not-finitely-presented`
already refutes finite presentation of every `E_N(R_T)`. By part 3 of the factorization node, the invariant for any
Toeplitz model over the `SL_3(Z)` congruence odometer is `H_0(Γ; Q_X) / ℓ` for the hole module `Q_X`.

## Attempts

1. **Proof sketch (gq-k2-q, 2026-09-18).** Artifact §3. It has four steps and three gaps:
   - (a) Assembly reduces to homotopy orbits, `K(B) ≃ K(LC(X,Q))_(hΓ')`, as in
     `fjc-crossed-products-of-k-trivial-regular-rings-vanish-proof`, via
     `regular-coherent-laurent-coefficients-kill-twisted-nil-terms`.
     - **Gap 1:** regular coherence of `LC(X,Q)[Z^m]` is not written. It is a filtered colimit of
       `Q[Z^m]^k` with flat transition maps.
   - (b) The spectral sequence is `H_p(Γ'; K_q(LC(X,Q))) ⇒ K_(p+q)(B)`, with
     `E^2_(0,2) = D_X ⊗ K_2(Q)`, and its edge map is `σ`.
   - (c) Only `d^2` from `E_(2,1)` and `d^3` from `E_(3,0)` can hit `E_(0,2)`.
     - **Gap 2:** that they are induced by the Postnikov invariants of `K(Q)`. This needs an equivariant
       splitting `K(LC(X,Q)) ≃ K(Q) ∧ S[LC(X,Z)]`.
     - **Gap 3:** that these operations have no odd torsion in the relevant degrees. The integral stable
       homology of `HZ` has no odd torsion below degree 4.
   - (d) So the odd part of `E^2_(0,2)` survives to `E^∞_(0,2) ⊆ K_2(B)`.
2. **Calibration.**
   - For `Γ' = Z` the conclusion agrees with `minimal-cantor-crossed-product-k-theory-formula`.
   - For a system whose hole module is the augmentation ideal of a perfect group, `H_0 = Γ^ab = 0`, so no
     obstruction arises (artifact §4). The invariant is therefore not automatically nonzero for Toeplitz
     extensions of `SL_3(Z)` odometers.
