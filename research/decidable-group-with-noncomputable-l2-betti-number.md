---
rg: 2
id: decidable-group-with-noncomputable-l2-betti-number
kind: claim
title: Some finitely generated group with decidable word problem has a noncomputable kernel dimension over its rational group ring
distinct_from:
  decidable-groups-have-right-computable-l2-betti-numbers: that is the established upper bound, right-computable in general and computable under the determinant conjecture; this asks for a group where the second alternative fails, which refutes the conjecture.
  binary-leavitt-unit-group-has-irrational-l2-betti-numbers: that gives irrational but computable kernel dimensions over the unit group, inherited from a lamplighter; this asks for noncomputable ones.
---

**OPEN.** There are a finitely generated group `G` with decidable word problem and a matrix
`T` over `Q[G]` such that `dim_vN ker T` is not a computable real.

**Payoff.** By `decidable-groups-have-right-computable-l2-betti-numbers` (Löh--Uschold,
arXiv:2202.03159, Theorems 1.1–1.2; Groth 2012 in degree 0), `G` violates Lück's determinant
conjecture (route `determinant-counterexample-via-noncomputable-l2-betti-number`). Löh--Uschold
Theorem 1.4 shows that groups of determinant class with decidable word problem realize exactly
the nonnegative computable reals. So the claim asks for a value in the gap between their
Theorems 1.1 and 1.4.

## Attempts

- **Necessary shape.**
  - `G` is nonsofic, since sofic groups satisfy the determinant conjecture.
  - The real is right-computable but not computable, like `1 - Ω` for a halting probability
    `Ω`.
  - The matrix has infinite spectrum, as in `determinant-conjecture-counterexample-exists`.
- **Grabowski's Turing dynamical systems** (arXiv:1004.2030, Section 6).
  - They realize numbers `1/64 - (2/8^3) Σ_(i in Σ) 2^(-i)` (as extracted from the PDF text)
    from groups `M^(⊕Z) ⋊ ((Aut(M) ≀ Z) * Z/2)`, `M = (Z/2)^3`, where the action of `Z/2`
    encodes `Σ`.
  - For computable `Σ` the presentation is recursive (his Section 6d lemma) and the number is
    computable.
  - For noncomputable `Σ` the relations encode `Σ`, so these groups are not candidates.
  - The values are measures of sets of configurations of a measure-preserving action on a
    compact abelian group. I found no variant that runs a universal machine to produce a
    noncomputable value over a decidable group. Soficity of these groups (abelian-by-sofic)
    was not checked, so this is no proof that the mechanism cannot work.
- **Inside the binary Leavitt unit group** (decidable, nonsofic, contains `V`).
  - Sofic subgroups give only computable numbers.
  - A witness would need an operator whose spectral mass near `0` escapes every computable
    bound, which is exactly the determinant failure the program lacks.
  - No construction.
- **Literature bound.** Löh--Uschold (2022/2023) prove the upper bounds and the determinant-class
  realization. In their introduction they do not claim a noncomputable value over a decidable
  group. No wider search was made.
