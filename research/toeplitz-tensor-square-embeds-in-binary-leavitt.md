---
rg: 2
id: toeplitz-tensor-square-embeds-in-binary-leavitt
kind: claim
title: The binary Leavitt algebra over F_2 contains two doubly commuting isometries with nonzero joint defect, equivalently a unital copy of the Toeplitz tensor square J ⊗ J
distinct_from:
  no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2: that asks for L ⊗ L inside L; this asks only for J ⊗ J, which a YES there gives (toeplitz-commutant-compression-detects-polynomial-pairs, part e1). Only the images of s_0 ⊗ 1 and 1 ⊗ s_0 and their left inverses are needed, not the relation s_0 t_0 + s_1 t_1 = 1.
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that OPEN claim forbids commuting independent pairs; this claim, if true, refutes it at k = F_2 with an explicit pair of commuting isometries.
  toeplitz-commutant-compression-detects-polynomial-pairs: that proves the reductions and equivalences; this is the open existence statement they point to.
  leavitt-isometry-centralizers-are-monogenic: that computes the full centralizer of a monomial isometry; here it rules out a monomial first isometry (Attempts).
artifacts:
  - experiments/leavitt-toeplitz-commutant-2026-09-17/toeplitz_scout.py
  - experiments/leavitt-toeplitz-commutant-2026-09-17/results.txt
---

**OPEN** (posed by lane w18 obstruction-miner, 2026-09-17).

Let `L = L_(F_2)(1,2)` and `J = F_2⟨x, y | yx = 1⟩`, the Toeplitz (Jacobson) algebra. The claim is that there
exist `S, S', R, R' ∈ L` such that:
- `S'S = 1` and `R'R = 1`;
- each of `S, S'` commutes with each of `R, R'`;
- `(1 - SS')(1 - RR') ≠ 0`.

By `toeplitz-commutant-compression-detects-polynomial-pairs` (d), this is equivalent to a unital embedding
`J ⊗ J -> L`.

**Where it sits.** The implications, all proved in `toeplitz-commutant-compression-detects-polynomial-pairs`, are:

```text
L ⊗ L -> L unital (Ara–Cortiñas Q5.7, YES)
   => this claim
   => some isometry S of L has T ∈ C(S,S') with PTP transcendental in the corner P L P
   => F_2[x, y] embeds in L, refuting leavitt-algebras-contain-no-two-variable-polynomial-ring at F_2
```

- A refutation of this claim answers Ara–Cortiñas Q5.7 negatively over `F_2`. It follows from the Q_2 firewall
  at `F_2`, and it is no harder to prove. Whether it is strictly easier is not known.
- A proof of this claim refutes Q_2 at `F_2`. It does not by itself give commuting *units*, so it does not touch
  `leavitt-commuting-units-are-algebraically-dependent`.
- For the `F_2[Z^4]` target of `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`, a proof supplies
  polynomial, not Laurent, variables. An isometry `R` with `RR' ≠ 1` is not a unit, so a further step would be
  needed.

**Why it is natural.** `J` embeds unitally in `L` via `x ↦ s_0`, `y ↦ t_0`: every nonzero ideal of `J`
contains `p = 1 - xy`, which is the one-factor case of step 4 of the proof route, and `p ↦ s_1 t_1 ≠ 0`. So the
question is whether the "tensor square" of an embeddable algebra embeds.

The C*-analogue holds: `O_2 ⊗ O_2 ≅ O_2`, and `s_0 ⊗ 1` and `1 ⊗ s_0` are doubly commuting isometries in
`O_2 ⊗ O_2` with joint defect `s_1 s_1^* ⊗ s_1 s_1^* ≠ 0`. So an obstruction must, as for Q5.7, use finite depth.

## Attempts

**Monomial first isometry (proved dead, lane w18).** Let `S = s_w` with `w = v^m`, `v` primitive.
- By `leavitt-isometry-centralizers-are-monogenic`, `C(S, S') ⊆ C_L(s_w) = F_2[s_v]`.
- `κ` is a homomorphism (`toeplitz-commutant-compression-detects-polynomial-pairs` (b)), and
  `κ(s_v)^m = κ(s_w) = P s_w P = 0` because `P s_w = 0`.
- So `κ(C(S,S')) ⊆ F_2[κ(s_v)]` consists of algebraic elements. By step 6 of the proof route, a partner `R`
  would have transcendental `κ(R)`.

So no doubly commuting partner with nonzero joint defect exists for a monomial `S`, and none for `S = s_w`
conjugated by a unit either, since conjugation preserves all the relations. The first isometry must be
non-monomial, and not conjugate to a monomial one.

**Exact screen (lane w18, `experiments/leavitt-toeplitz-commutant-2026-09-17/`).** Take `S = u s_0` for eight units
`u` (transvections `1 + s_a t_b` with `(s_a t_b)^2 = 0`, a prefix swap, and products). In the boxes
`(N, L) = (2, 3)` and `(3, 4)`, `C(S,S')` is only the scalars. The flip control gives `M_2(F_2)`. So short units
give nothing, and a witness would have to be designed, as for `leavitt-endomorphism-relative-commutants-are-finite`.

**Unverified pointer (not used).** `J` is, I believe, the Leavitt path algebra of the graph with a loop at `v` and
one edge `v -> w`. If so, `J ⊗ J` is a Kumjian–Pask algebra of a product 2-graph, and this claim is a special case
of Bilich–Hazrat–Nam, arXiv:2512.09241v2, Question 2.8, as quoted on `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`.
The identification of product Kumjian–Pask algebras with tensor products was not checked against a source here.
