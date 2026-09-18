---
rg: 2
id: faithful-pair-finite-steinberg-actions-need-noncentral-k2-proof
kind: route
title: Rational scalars are elementary and central, a perfect central extension lifts centres, and pair-finite faithful actors have finite centre
target: faithful-pair-finite-steinberg-actions-need-noncentral-k2
requires:
  - ibn-failure-makes-rational-scalars-elementary
  - type-a-actors-have-no-infinite-virtually-central-subgroup
  - leavitt-scalar-commutators-block-fp-central-quotients
---

Notation as in the target. Assume `K` is central in `Γ`. Commutators are
`[x,y] = xyx^-1y^-1`.

**Step 1: rational scalars.**
- For `λ ∈ Q^x`, part 3 of `ibn-failure-makes-rational-scalars-elementary`
  (Leavitt `(1,2)` family, `d = 2`) gives `λ I_N ∈ E_N(R)`.
- `λ` is central in `R`, so `λ I_N` commutes with every matrix, and lies in
  `Z(E_N(R))`.
- `λ ↦ λ I_N` is injective. The unital map `Q -> R` is injective, since `Q` is
  a field and `R ≠ 0`.
- So `Q^x · I_N` is a copy of `Q^x` inside `Z(E_N(R))`.

**Step 2: `Γ` is perfect.** For `i ≠ j`, pick `k ∉ {i,j}`, which is possible
since `N >= 3`. Then `x_ij(r) = [x_ik(r), x_kj(1)]`, and these elements
generate `Γ`.

**Step 3: item 1.**
- `π` is onto, so `π(Z(Γ)) ⊆ Z(E_N(R))`.
- Conversely, let `π(p)` be central, and put `φ(g) = [g, p]`. It lies in `K`,
  because `π(φ(g)) = [π(g), π(p)] = 1`.
- Since `K` is central,
  `φ(gh) = g φ(h) g^-1 · [g,p] = φ(h) φ(g)`.
  So `φ` is a homomorphism from `Γ` to the abelian group `K`.
- `Γ` is perfect (Step 2), so `φ` is trivial, and `p` is central.

**Step 4: item 2.**
- `π(Z(Γ)) = Z(E_N(R))` contains `Q^x · I_N` (Steps 1 and 3).
- If `Z(Γ)` were finitely generated, the abelian group `π(Z(Γ))` would be too.
  Then so would its subgroup `Q^x · I_N ≅ Q^x`. But `Q^x` is not finitely
  generated, because its primes are independent.
- In particular `Z(Γ)` is infinite.

**Step 5: item 3.**
- `Γ/M` acts faithfully on `S`, with the same orbits of two-element subsets.
- The image of `Z(Γ)` is central in `Γ/M`. By
  `type-a-actors-have-no-infinite-virtually-central-subgroup`, corollary 1, it
  is finite. So `Z(Γ)/(M ∩ Z(Γ))` is finite.
- If `M = 1`, then `Z(Γ)` is finite, which contradicts Step 4.
- A type (A) action is faithful and has finitely many orbits of two-element
  subsets, so none exists.

**Step 6: item 4.**
- Let `M <= Z(Γ)`. By Step 5, `M` has finite index in `Z(Γ)`. It is not finitely
  generated: otherwise `Z(Γ)` would be a finite extension of a finitely
  generated group, contradicting Step 4.
- `M <= Z(Γ) = Z(Γ) ∩ [Γ,Γ]`, since `Γ` is perfect.
- Part 0 of `leavitt-scalar-commutators-block-fp-central-quotients` applies with
  `H = Γ` and `C_0 = C = M`. It shows that `Γ/M` is not finitely presented.

**Unconditional form.** This is the contrapositive of item 3.

**Trust surface.** Step 1 rests on part 3 of
`ibn-failure-makes-rational-scalars-elementary`, which is a lane proof and has
not been independently reviewed.
