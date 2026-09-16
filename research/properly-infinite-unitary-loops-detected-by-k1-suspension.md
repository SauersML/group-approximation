---
rg: 2
id: properly-infinite-unitary-loops-detected-by-k1-suspension
kind: claim
title: Based loops of unitaries in a properly infinite algebra are null iff their K1 class in the suspension vanishes
distinct_from:
  stw99-problem-lxi-properly-infinite-k1-injective: the root is about path components of U(A); this is about the fundamental group of U(D), and is implied by the root via C(T, D).
artifacts:
  - research/artifacts/lxi-quotient-minimal-counterexamples-2026-09-16.md
---

Let `D` be a unital properly infinite C\*-algebra and let `l: [0,1] → U(D)` be continuous with
`l(0) = l(1) = 1`. Put `SD = C_0((0,1), D)`. If the unitary `1 + (l − 1)` of `(SD)~` has trivial class in
`K_1(SD)`, then `l` is homotopic to the constant loop 1 relative to `{0, 1}`.

Equivalently, the natural homomorphism `kappa_D: pi_1(U(D), 1) → K_1(SD)` is injective. It is always
surjective for properly infinite `D`: Bott periodicity identifies `K_1(SD)` with `K_0(D)`, and every class
in `K_0(D)` is realized by a projection `e`, hence by the loop `t ↦ e^{2πit} e + 1 − e`. So the claim says
`pi_1(U(D), 1) ≅ K_0(D)` via the Bott map.

## Attempts

- **Implied by LXI.** Route `unitary-loop-detection-from-lxi`. With `prime-quotient-minimal-k1-trivial-unitaries-are-null`,
  it is equivalent to LXI (route `stw99-lxi-from-prime-case-and-loop-detection`).
- **Matrix form** (artifact, Proposition 6). For a fixed `D`, the claim holds iff
  `pi_1(U(D), 1) → pi_1(U(M_2(D)), 1)`, `[l] ↦ [diag(l, 1)]`, is injective. The proof applies
  `brr-commutator-criterion-null-unitary` in `M_2(C(T, D))` with `p = diag(1, 0)`. So the claim is the loop
  analogue of BRR Proposition 5.2(ii).
- **Known cases.** The claim holds for `D` whenever `C(T, D)` is K1-injective, by the argument of the from-LXI
  route. This covers Z-stable `D`, since `C(T) ⊗ D` is then Z-stable
  (`z-stable-unital-algebras-are-k1-bijective`). It also covers purely infinite simple `D`, by Rohde's thesis
  (IMADA, University of Southern Denmark, March 2009), Theorem 5.2.11. That theorem says a unital continuous `C(X)`-algebra over a
  finite-dimensional compact `X` with purely infinite simple fibres is K1-injective. It applies with `X = T`.
  Its proof was read but its inputs from BRR were not rechecked.
- **Dead ends.** Transporting the halving homotopy to loops is no easier than the unitary version. There is no
  delooping that turns a loop in `U(D)` into a unitary of a properly infinite algebra, other than `C(T, D)`,
  which gives back the unitary problem. `C(T, D)` is never prime, so Theorem 3 of the artifact cannot be
  iterated to reduce everything to the prime case.
