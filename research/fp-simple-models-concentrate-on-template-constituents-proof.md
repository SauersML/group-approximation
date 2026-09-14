---
rg: 2
id: fp-simple-models-concentrate-on-template-constituents-proof
kind: route
title: Markov on relator defects, collapse of scalar-relator and bounded-dimension constituents, and the template carries the rest
target: fp-simple-models-concentrate-on-template-constituents
requires: [finitely-generated-linear-groups-are-residually-finite]
---

Notation as on the claim. `τ` is the normalized trace, and `‖U − I‖_2² = 2 − 2 Re τ(U)` for unitary `U`.

**Step 0 (words).** For every word `w`, `lim_ω ‖ρ_k(W_k(w)) − π_k(w̄)‖_2 = 0`, where `π_k = ρ_k∘φ_k` on `X`.
- `Π` is a homomorphism, so `lim_ω ‖π_k(g)π_k(h) − π_k(gh)‖_2 = 0` and `lim_ω ‖π_k(g^{-1}) − π_k(g)^{-1}‖_2 = 0`. Here
  `π_k(g)` is any representative sequence of `Π(g)`.
- `ρ_k` is a homomorphism, so `ρ_k(W_k(w))` is the product of the `π_k(x)^{±1}` along `w`.
- On unitaries `‖AB − A'B'‖_2 ≤ ‖A − A'‖_2 + ‖B − B'‖_2`. Induct on the length of `w`.

Consequences:
- For `r ∈ R`, `r̄ = e`, so `Δ_k := Σ_{r∈R} ‖ρ_k(W_k(r)) − I‖_2² → 0` along `ω`.
- `E_k := ‖ρ_k(W_k(c)) − I‖_2² → η² > 0` along `ω`.

**Step 1 (additivity).** For `g ∈ Q_k`,
`‖ρ_k(g) − I‖_2² = Σ_σ p_σ (2 − 2 Re χ̃_σ(g)) = Σ_σ p_σ ‖σ(g) − I‖_2²`, with each norm normalized in its own representation.
Put `δ_σ = Σ_r ‖σ(W_k(r)) − I‖_2²` and `e_σ = ‖σ(W_k(c)) − I‖_2² ∈ [0,4]`. Then
`Σ_σ p_σ δ_σ = Δ_k` and `Σ_σ p_σ e_σ = E_k`.

**Step 2 (four classes of constituents).**

(i) *Every relator is scalar in `σ`.*
- `Z_σ = {q : σ(q) ∈ C·I}` is a normal subgroup of `Q_k`.
- `x ↦ φ_k(x) Z_σ` kills `R`, so it defines a homomorphism `S → Q_k/Z_σ`. Its kernel has finite index in the infinite simple
  group `S`, so it is `S`.
- So `σ(φ_k(x))` and `σ(φ_k(y))` are scalars. They commute, `σ(W_k(c)) = I`, and `e_σ = 0`.

(ii) *Some relator `r` has `|χ̃_σ(W_k(r))| ≤ θ`.*
- Then `‖σ(W_k(r)) − I‖_2² = 2 − 2 Re χ̃_σ(W_k(r)) ≥ 2 − 2θ`, so `δ_σ ≥ 2 − 2θ`.
- By Markov, the total weight of class (ii) is at most `Δ_k/(2−2θ) → 0`, and its contribution to `E_k` is at most
  `4Δ_k/(2−2θ) → 0`.

(iii) *`dim σ ≤ D`, and `σ` is in neither (i) nor (ii).*

*Lemma.* For every `D` and `ε > 0` there is `δ(D,ε) > 0` such that, for `n ≤ D` and `a ∈ U(n)^X`,
`Σ_r ‖r(a) − I‖_2² < δ(D,ε)` implies `‖c(a) − I‖_2² < ε`.
- *Proof.* Otherwise there are `a_j ∈ U(n_j)^X` with `n_j ≤ D`, defect `→ 0`, and `‖c(a_j) − I‖_2² ≥ ε`.
- Pass to a subsequence with `n_j = n` and `a_j → a` in the compact space `U(n)^X`. Then `r(a) = I` for all `r`, so `a`
  defines a homomorphism `S → U(n)`.
- Its image is a finitely generated linear group, so it is residually finite
  (`finitely-generated-linear-groups-are-residually-finite`). It is also a quotient of the simple group `S`, so it is trivial or
  isomorphic to `S`. An infinite simple group is not residually finite, so the image is trivial.
- So `c(a) = I`, which contradicts `‖c(a_j) − I‖_2² ≥ ε` by continuity. ∎

The constituents in (iii) with `δ_σ < δ(D,ε)` contribute at most `ε` to `E_k`. Those with `δ_σ ≥ δ(D,ε)` have total weight at
most `Δ_k/δ(D,ε) → 0`.

(iv) *Everything else.* These are exactly the constituents with `dim σ > D`, every relator ratio `> θ` in absolute value,
and some relator non-scalar: the set `T_k(θ,D)`. Each contributes at most `4 p_σ`.

**Step 3 (conclusion).** `η² = lim_ω E_k ≤ ε + 4 lim_ω Σ_{T_k(θ,D)} p_σ` for every `ε > 0`, so
`lim_ω Σ_{T_k(θ,D)} p_σ ≥ η²/4`. The same bookkeeping gives `lim_ω Σ_{T_k(θ,D)} p_σ e_σ ≥ η²`. ∎

**Corollary 1.**
- *Diagonal choice.* Put `θ_m = 1 − 1/m` and `D_m = m`. Let:
  - `A_m = {k : Σ_{σ∈T_k(θ_m,D_m)} p_σ e_σ ≥ η²/2}`, which lies in `ω` by Step 3;
  - `B_m = A_1 ∩ … ∩ A_m ∩ {k ≥ m}`;
  - `m(k) = max{m : k ∈ B_m}`, which is finite.

  For each `M`, `{k : m(k) ≥ M} ⊇ B_M ∈ ω`, so `m(k) → ∞` along `ω`. Since `T_k(θ,D)` shrinks as `θ` and `D` grow,
  `k ∈ A_{m(k)}`.
- *Choice of constituent.* Since `Σ_{T} p_σ ≤ 1`, some `σ_k ∈ T_k(θ_{m(k)}, D_{m(k)})` has `e_{σ_k} ≥ η²/2`. Then
  `dim σ_k > m(k) → ∞`, every relator has `|χ̃| > 1 − 1/m(k)`, and some relator is non-scalar.
- *The projective homomorphism.*
  - `d_proj(σ(g), I)² = min_λ (2 − 2 Re(λ̄ τ(σ(g)))) = 2 − 2|χ̃_σ(g)|`, so the relators tend to `0` in `d_proj`.
  - `d_proj` is bi-invariant, and the null sequences form a normal subgroup of `∏ U(n_k)`.
  - So `w ↦ (σ_k(W_k(w)))_ω` is a homomorphism from the free group to `∏_ω PU(n_k)` that kills `R`. It factors as
    `Ψ : S → ∏_ω PU(n_k)`.
- *Ψ is nontrivial.* Suppose `d_proj(σ_k(φ_k(y)), I) ≤ β_k → 0`, i.e. `σ_k(φ_k(y)) = λ B'` with `‖B' − I‖_2 ≤ β_k`. Write
  `A = σ_k(φ_k(x))`.
  - Scalars cancel in commutators, and `[A,B'] − I = (AB' − B'A)A^{-1}B'^{-1}`.
  - `AB' − B'A = (A − I)(B' − I) − (B' − I)(A − I)`, with `‖A − I‖_op ≤ 2`.
  - So `e_{σ_k} = ‖[A,B'] − I‖_2² ≤ (4β_k)² → 0`, which contradicts `e_{σ_k} ≥ η²/2`.
  - So `Ψ` is nontrivial, and it is injective because `S` is simple.
- *Adjoint.* `A ↦ A ⊗ Ā` is a homomorphism `U(n) → U(n²)`, constant on scalar classes, with `τ(A ⊗ Ā) = |τ(A)|²`. With
  `t = |τ(A)|`, `2 − 2t ≤ 2 − 2t² ≤ 2(2 − 2t)`. By bi-invariance, `d_proj` and the `‖·‖_2` distance of adjoints are equivalent.
  So `σ_k ⊗ σ̄_k` gives an injective homomorphism `S → ∏_ω U(n_k²)`. ∎

**Corollary 2.** If every constituent of dimension `> D` is θ-gapped, then `T_k(θ,D)` is empty, which contradicts
`η²/4 > 0`. ∎

**Permutation template.** `Q_k = ⟨σ_k(X)⟩`. The normalized Hamming distance is the average over `Q_k`-orbits `Ω_j`, weighted
by `p_j = |Ω_j|/|Ω_k|`, and it is bi-invariant, so Step 0 holds verbatim in it. The classes are:
- (i) every relator trivial on `Ω_j`. Then `S → Sym(Ω_j)` is a homomorphism to a finite group, hence trivial, and `c` acts
  trivially.
- (ii) some relator moves at least a `(1−θ)`-fraction of `Ω_j`. The weight is at most `Σ_r d(σ_k(W_k(r)),1)/(1−θ) → 0`.
- (iii) the template orbits. A nontrivial permutation moves at least 2 points, so `2/|Ω_j| < 1 − θ`.

Each orbit contributes at most `p_j` to `d(σ_k(W_k(c)),1)`, so the template orbits weigh at least `η`. ∎
