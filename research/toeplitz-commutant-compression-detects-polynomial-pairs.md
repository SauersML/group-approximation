---
rg: 2
id: toeplitz-commutant-compression-detects-polynomial-pairs
kind: claim
title: Compressing the commutant of an isometry to its defect corner is a homomorphism, and a transcendental compression yields an algebraically independent commuting pair; doubly commuting isometries with nonzero joint defect are exactly unital embeddings of the Toeplitz tensor square
distinct_from:
  leavitt-endomorphism-relative-commutants-are-finite: that commutant C_u is taken against a whole unital copy of L (two isometries u s_0, u s_1); this commutant is taken against ONE isometry S and its left inverse, and is strictly larger, so it is a weaker YES-side target. Part (e) shows a transcendental element of any C_u already gives a transcendental compression here.
  leavitt-copy-centralizing-units-are-self-doubling: that characterizes the commutant of a unital copy of L by twisted fixed points of the doubling map; this characterizes the commutant of one isometry by the one-sided map Φ(a) = S a S' and reads it off in the defect corner.
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that OPEN claim forbids commuting independent pairs; this gives a sufficient condition, testable by linear algebra, for such a pair to exist.
  no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2: that is the L ⊗ L embedding question; part (e) shows a YES there gives a unital embedding of the Toeplitz tensor square J ⊗ J, hence a transcendental compression.
  leavitt-isometry-centralizers-are-monogenic: that computes the full centralizer of a monomial isometry; this is about the commutant of an arbitrary isometry together with its left inverse, and about the defect corner.
artifacts:
  - experiments/leavitt-toeplitz-commutant-2026-09-17/toeplitz_scout.py
  - experiments/leavitt-toeplitz-commutant-2026-09-17/results.txt
---

**ESTABLISHED** by `toeplitz-commutant-compression-detects-polynomial-pairs-proof` (lane w18 obstruction-miner,
elementary, not reviewed, no priority claimed).

**Setting.** `k` is a field and `A` a unital `k`-algebra. `S, S' ∈ A` satisfy `S'S = 1`. Put `P = 1 - SS'`, an
idempotent with `PS = 0` and `S'P = 0`, and `Φ(a) = S a S'`. Let `C(S,S') = { T ∈ A : TS = ST, TS' = S'T }`.
An element `c` of the corner `PAP` (unit `P`) is *transcendental* if `q(c) ≠ 0` for every nonzero `q ∈ k[z]`,
with `c^0 = P`.

`J = k⟨x, y | yx = 1⟩` is the Toeplitz (Jacobson) algebra and `p = 1 - xy`.

## Statement

**(a) Description.** `C(S,S') = { T ∈ A : T - Φ(T) ∈ PAP }`. For `T ∈ C(S,S')`, `T - Φ(T) = TP = PTP`.

**(b) Compression.** `κ(T) = PTP` is a unital homomorphism `C(S,S') -> PAP`. Its kernel is
`{ T ∈ C(S,S') : T = Φ(T) }`, and its image is `PAP ∩ (1 - Φ)(A)`.

**(c) Detection.** If `T ∈ C(S,S')` and `κ(T)` is transcendental in `PAP`, then `S` and `T` commute and are
algebraically independent over `k`: `F(S, T) ≠ 0` for every nonzero `F ∈ k[x, y]`.

**(d) Toeplitz tensor square.** Every nonzero two-sided ideal of `J ⊗_k J` contains `p ⊗ p`. Hence the following
are equivalent:
1. there is a unital injective homomorphism `J ⊗_k J -> A`;
2. there are `S, S', R, R' ∈ A` with `S'S = 1 = R'R`, each of `S, S'` commuting with each of `R, R'`, and
   `(1 - SS')(1 - RR') ≠ 0`.

For such a pair, `R ∈ C(S,S')` and `κ(R)` is transcendental, so (c) applies. In particular `S` and `R` are
algebraically independent, and `k[x_1, x_2]` embeds in `A`.

**(e) Leavitt consequences.** Let `A = L = L_k(1,2)`.
1. A unital homomorphism `L ⊗_k L -> L` gives a unital embedding `J ⊗_k J -> L`. So a YES to Ara–Cortiñas
   Question 5.7 over `k` implies `toeplitz-tensor-square-embeds-in-binary-leavitt`.
2. For a unit `u`, set `S = u s_0` and `S' = t_0 u^(-1)`. If some `z ∈ C_u` (the relative commutant of
   `leavitt-endomorphism-relative-commutants-are-finite`) is transcendental over `k`, then `z ∈ C(S,S')` and
   `κ(z)` is transcendental.

So the chain of YES-side conditions is:

```text
Q5.7 YES  =>  J ⊗ J embeds unitally in L  =>  some isometry S of L has T ∈ C(S,S') with κ(T) transcendental
          =>  leavitt-algebras-contain-no-two-variable-polynomial-ring fails at k
(some C_u contains a transcendental element)  =>  (the third condition)
```

**What it changes.**
- The firewall claim `leavitt-algebras-contain-no-two-variable-polynomial-ring` is now attacked, on the YES
  side, by a one-isometry linear problem. Fix `S`; then decide whether the corner `PLP ∩ (1 - Φ)(L)` contains a
  transcendental element.
- On the NO side, a proof of that claim must in particular rule out every such corner element, for every isometry
  `S`.
- `J ⊗ J` is the natural Toeplitz analogue of `L ⊗ L`, and it sits between the two open problems in the chain
  above. Neither reverse implication is known.
