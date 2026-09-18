---
rg: 2
id: effective-minimal-free-subshifts-via-overlap-recurrence
kind: route
title: Overlap-recurrent hyperaperiodic point, orbit closure equals the explicit set Y_OC with decidable forbidden balls
target: decidable-fp-groups-have-effective-minimal-free-subshifts
requires:
  - covering-towers-iff-effective-minimal-free-subshifts
  - decidable-groups-have-overlap-recurrent-aperiodic-points
---

**Route. OPEN.** The route rests on two prerequisites.
- The first, `covering-towers-iff-effective-minimal-free-subshifts`, is
  ESTABLISHED.
- The second, `decidable-groups-have-overlap-recurrent-aperiodic-points`, is
  OPEN.

**Argument.** Let `Λ` be an infinite finitely presented group with solvable
word problem.
1. The second prerequisite gives a computable `y`, computable `R_n` and `m_n`,
   and (OC) and (A).
2. By the Corollary of the first prerequisite, the orbit closure of `y` equals
   `Y_OC = {z : ∀n ∀g ∃h ∈ B(R_n − m_n)g, z(μh) = y(μ) for all μ ∈ B(R_n)}`.
   This set is nonempty, effectively closed with a decidable forbidden set,
   minimal and free.
3. That is (M2) for `Λ`.

**How it can fail.**
- Only the second prerequisite is open.
- It is strictly stronger than (M2), which corresponds to towers with arbitrary
  finite families `L_n`.
- It can fail on its own at the one-patch rigidity. Lemma T rules out
  subgroup-return designs, and Toeplitz and weakly mixing `Z` examples violate
  the margin (artifact of the premise).
- If it fails, the general-tower form of (M2) remains. That form is the target
  itself, rewritten by the first prerequisite.
