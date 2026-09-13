---
rg: 2
id: pauli-projector-hamiltonians-are-stabilizer-approximable
kind: claim
title: Sums of Pauli projectors have stabilizer states within a factor 2+sqrt2 of the ground energy, so their b > (2+sqrt2)a promise problems are in NP
artifacts:
  - research/artifacts/pauli-frustration-stabilizer-rounding-2026-09-12.md
distinct_from:
  quantum-pcp-constant-gap-local-hamiltonian: that conjectures QMA-hardness at a constant gap for general local terms; this shows that when all terms are Pauli projectors the YES energy must be at least a 1/(2+sqrt2) fraction of the NO floor, unless QMA is in NP.
  nlts-hamiltonians-from-good-qldpc-codes: that proves low-energy states of code Hamiltonians need logarithmic depth; this shows such Pauli-projector Hamiltonians, noncommuting or not, still have stabilizer (classically described) approximate ground states in the multiplicative sense.
---

**ESTABLISHED (ordinary proof, unreviewed).** Let

```text
H = sum_a w_a (I - s_a P_a)/2,     w_a >= 0,   s_a in {+1,-1},
```

with Hermitian `n`-qubit Paulis `P_a` of any weight, commuting or not, given as
an explicit polynomial-size list. Then

```text
min_(phi stabilizer) <phi|H|phi>  <=  (2+sqrt2) lambda_min(H).               (PP)
```

More generally, (PP) holds for `H = sum_a w_a (I - Pi_a)` where each `Pi_a` is the
projector onto a stabilizer code space (`Pi_a = prod_(i<=r_a) (I+g_(a,i))/2` for
independent commuting signed Paulis generating a group without `-I`). Each term
penalizes leaving a code space; single Pauli projectors are the case `r_a = 1`.

Consequently, deciding `lambda_min(H) <= a` versus `lambda_min(H) >= b` for such
instances is in NP whenever `b > (2+sqrt2)a`.

**Mixed terms (PP-mix).** If `H = sum_a w_a(I-Pi_a) + sum_b v_b h_b` with
`0 <= h_b <= I` arbitrary and non-stabilizer weight `V = sum_b v_b`, then some
stabilizer state has energy at most `(2+sqrt2) lambda_min(H) + V`. So the promise
problem is in NP when `V < b - (2+sqrt2)a`. A QMA-hard family with negligible
YES energy and NO floor `b` needs non-stabilizer term weight at least about `b`,
unless QMA is in NP. The witness is a stabilizer
tableau, and its energy is an exact rational computed by `F_2` linear algebra.
The same holds for explicit Pauli sums: `lambda_max >= W-F_Y` versus
`lambda_max <= W-F_N` is in NP when `F_N > (2+sqrt2)F_Y`.

**Bearing on the root.** If QMA is not in NP, any QMA-hard family whose terms
are Pauli projectors, such as code checks together with Pauli measurement terms,
has YES energy at least `b/(2+sqrt2)`. A constant-gap construction with
frustration-free or near-frustration-free YES outputs must use non-Pauli terms.
This complements the frustration-free branch of
`anchored-criterion-components-are-shift-satisfiable`. The ratio threshold is not
known to be sharp: stabilizer witnesses fail below `1+1/sqrt2` (two terms
`(I-X)/2`, `(I-Z)/2`).
