# EX review, analysis lanes, part 5 (2026-09-13)

Lane `ex-verify-analysis`. Verdict legend as in `ex-review-analysis-2026-09-12.md` §0. Main tip at
review time: `5e8bc6217`.

## 1.11 ex-rr0-dichotomy: what a counterexample to Rørdam's dichotomy must look like

These nodes do not flip any root:
- `stw99-problem-xxix-rr0-dichotomy` is OPEN. Its new routes require the OPEN
  `finite-simple-rr0-algebras-have-weak-cancellation` and `rr0-simple-algebras-have-corona-factorization`.
- `stw29-rr0-mixed-simple-algebra-exists` is OPEN, with no route.
- `finite-simple-rr0-algebras-have-stable-rank-one` is OPEN, with no route.

Imports used, all through citation routes with `requires: []` and not re-read here:
- Ortega--Perera--Rørdam arXiv:0904.0541: Theorem 4.3, the corona factorization property corollary,
  and the mixed refinement monoid;
- Ara--Goodearl, tame refinement monoids are separative;
- Rainone arXiv:1502.06153, Theorems 4.11, 4.13, 4.16 and 4.21;
- Rørdam, *The real rank of certain simple C*-algebras*.

### `stw29-counterexample-level-two-fingerprint` (c94145c599): PASS

Re-derived.
- **(1 ⇒ 2).** If every nonzero projection were infinite, real rank zero would put an infinite
  projection in every nonzero hereditary subalgebra, so the algebra would be purely infinite. So some
  nonzero q is finite. Simplicity gives [p] ≤ l[q] for an infinite matrix projection p, so n[q] is
  infinite for a least n ≥ 2. Then C = M_{n−1}(qAq) is finite, simple and of real rank zero (Brown--
  Pedersen), while M_2(C) is infinite.
- **(2 ⇔ 3).** Blackadar's separable inheritance for simplicity and real rank zero.
- **(a).** 2u is properly infinite by (F2). Repeated application of OPR Theorem 4.3 gives the
  orthogonal e_i with 2u ≤ 2[e_i].
- **(c).** 2u properly infinite gives 2u = 4u + w. Put r = 2u + w, so 2u + r = 4u + w = 2u. Then
  x = u and y = u + r have x + y = 2x = 2y = 2u. Also x ≠ y, since u = u + r with r ≠ 0 would make u
  infinite. So V(C) is not separative.
- **(d).** C*-algebras of real rank zero are exchange rings. So a counterexample to XXIX gives a
  simple non-separative exchange ring, and the Ara--Goodearl--O'Meara--Pardo separativity problem is
  open, as stated.

### `stw29-separative-projection-monoid-dichotomy` (c94145c599): PASS

- **Part 1** is the (c) computation, using only a finite and an infinite projection.
- **Part 2.** Property (SP) plus separativity gives the dichotomy. Weak cancellation equals
  separativity for simple conical monoids (AGOP Lemma 2.1).
- **Limit permanence.** V is continuous under inductive limits, and separativity is a Horn condition
  among finitely many equations, so it passes to direct limits of monoids.
- **Building blocks.** Stable rank one (cancellation) and purely infinite simple algebras are
  separative. The C(X) ⊗ O_∞ case was not re-checked.
- **Consequence.** Rørdam's building blocks are non-separative. This follows from part 1 applied to
  his limit B together with limit permanence.

### `coinvariant-tarski-lemma-simple-dimension-groups` (16b29537a3): PASS

Re-derived.
- **Congruence.** Transitivity follows by refinement.
- **Division.**
  - Refine Nx = Σ_i c_i into N columns c_ij, each summing over i to x.
  - Density (D) gives d_ij with 0 < d̂_ij, N d̂_ij < ĉ_ij and ĉ_ij − N d̂_ij < Nε. Faithfulness (O)
    makes d_ij and c_ij − N d_ij positive.
  - s(x − y) > 0 on S, so r = x − y ∈ G^+ by (O).
- **The move.** x = y + r ~ x' = Σ α_{t_i}(d_ij) + r. Then N s(x' − x) = s(e) − (error), where the
  error is bounded by mN·(L+1)·Nε < η/2, and ê ≥ η on S by (U) and compactness. So e' = x' − x > 0,
  and [x] = [x] + [e'].
- **Proper infiniteness.** In the simple conical coinvariant monoid, infinite elements are properly
  infinite. And (k+1)θ ≤ kθ makes kθ infinite, so θ is properly infinite.
- **Hypothesis tests.** Z fails (D), Z² with the product order fails (U), and the OPR mixed monoid
  carries no states. All correct.

### `simple-af-integer-crossed-products-dichotomy` (cd50958abc, 16b29537a3): PASS

Re-derived.
- **(P1).** Kishimoto compression into D, as in Rørdam 2005 Lemmas 5.1 and 5.4. It is a trust
  surface, not re-read.
- **(P2).** α(p) ~ p, so Σ = K_0(D)^+/~ maps to V(A).
- **(P3).** A state on Σ normalised at a nonzero class gives an α_*-invariant positive homomorphism
  K_0(D) → R. For AF D this is a densely finite lower semicontinuous trace, invariant by uniqueness.
  τ∘E is faithful and gives stable finiteness.
- **(P4).** With no invariant trace, Goodearl--Handelman/Tarski give (k+1)[x] ≤ k[x], so [x] is
  properly infinite in Σ, hence in V(A). A properly infinite class of projections is a properly
  infinite projection of A. By (P1), every nonzero hereditary subalgebra of A contains one, so A is
  purely infinite.
- **Scope.** The unital case always falls in case 1, since Z is amenable. The interesting case is
  non-unital, and the node says so. Novelty beyond Rainone is marked unverified.

### `simple-coefficient-crossed-products-dichotomy` (16b29537a3): PASS

- Real rank zero with stable rank one gives (R) and (U), while (O) and (D) are hypotheses. So the
  coinvariant lemma applies to Rainone's type semigroup S = V(A)/~, and V(A) = K_0(A)^+ by
  cancellation.
- **Case B.** Tarski (Rainone Theorem 4.11) gives (k+1)θ ≤ kθ. The lemma makes S purely infinite, and
  Rainone 4.21 (1) ⇒ (3), through 4.16 with (SP), makes the crossed product purely infinite.
- **Case A.** Rainone 4.13 gives an invariant faithful tracial state, and stable finiteness follows.
- Exclusivity is correct.
- **Scope.** Case 2 needs a non-amenable Γ, and the node says so. This removes Rainone's
  almost-unperforation hypothesis through the lemma. The claim is packaged with its hypotheses, and
  novelty is marked unverified.
