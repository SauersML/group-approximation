---
rg: 2
id: congruence-transporter-girth-proof
kind: route
title: Entry degrees grow at most exponentially, kernel elements cost at least M/2
target: congruence-transporter-girth
requires: []
---

# Entry degrees grow at most exponentially, kernel elements cost at least M/2

Write elements of `G` as pairs `w = (n_w, A_w)` with `n_w ∈ EL_r(R)` and
`A_w ∈ SL_d(ℤ)`, multiplication `(n_1, A_1)(n_2, A_2) =
(n_1 · {}^{A_1}n_2, A_1 A_2)`, where `{}^{A}n` applies the monomial
substitution `x^a ↦ x^{Aa}` entrywise.  Define two weights:

- `D(w)` := the maximal ℓ¹-norm of an exponent vector occurring in an
  entry of `n_w` (with `D = 0` for `n_w = 1`, since the identity matrix has
  constant entries);
- `‖A_w‖` := the ℓ¹ operator norm of `A_w`.

**Weights under multiplication.**  Exponent vectors of a product of two
Laurent monomials add, and matrix multiplication only sums such products,
so `D(n·n') ≤ D(n) + D(n')`; a substitution obeys
`‖Aa‖_1 ≤ ‖A‖·‖a‖_1`, so `D({}^{A}n) ≤ ‖A‖·D(n)`; and operator norms are
submultiplicative.

**Exponential upper bound along words.**  Let `w_k` be the value of an
`F`-word of length `k` and `C = C(F) ≥ 2` as in the claim (a bound valid
for all letters and their inverses).  Appending one letter `g` gives

```text
‖A_{w_i}‖ ≤ ‖A_{w_{i-1}}‖·C ≤ C^i,
D(w_i)   ≤ D(w_{i-1}) + ‖A_{w_{i-1}}‖·D(g) ≤ D(w_{i-1}) + C^i,
```

so by induction `D(w_k) ≤ C + C² + ⋯ + C^k ≤ C^{k+1}` and
`‖A_{w_k}‖ ≤ C^k ≤ C^{k+1}`.

**Every nontrivial kernel element is heavy.**  Let `v = (n, A) ∈ ker π_M`,
`v ≠ 1`.

- If `A ≠ 1`: `A ≡ 1 (mod M)` forces some entry of `A` to differ from the
  corresponding entry of the identity by a nonzero multiple of `M`, so
  `‖A‖ ≥ M − 1 ≥ M/2`.
- If `A = 1` and `n ≠ 1`: some entry `f` of `n` differs from the
  corresponding entry `δ` of the identity, and `f − δ` is a nonzero element
  of the ideal `I_M = ker(R → F_q[(ℤ/M)^d])`.  In the quotient the
  coefficients of `f − δ` sum to zero within each residue class of
  exponents mod `Mℤ^d`; a class supporting exactly one exponent of
  `f − δ` would retain its nonzero coefficient, so some class supports two
  distinct exponents `a ≠ b` with `a − b ∈ Mℤ^d ∖ {0}`.  Then
  `‖a − b‖_1 ≥ M`, so `max(‖a‖_1, ‖b‖_1) ≥ M/2` and `D(v) ≥ M/2`.

Combining, `C^{k+1} ≥ max(D(v), ‖A_v‖) ≥ M/2`, i.e.
`k ≥ log_C(M/2) − 1`, which is item 2.

**Item 1.**  Since `(M-1)·m ≡ −m (mod Mℤ^d)` for `m = (1,…,1)`, the ring
reduction sends `(x_1⋯x_d)^{M-1} ↦ x̄^{-m}`, so

```text
v_0 := h · e_12\big(−(x_1⋯x_d)^{M-1}\big)
     = e_12\big((x_1⋯x_d)^{-1} − (x_1⋯x_d)^{M-1}\big) ∈ ker π_M ∩ hΓ,
```

the middle factor lying in `Γ` because `(x_1⋯x_d)^{M-1} ∈ R_+`.  And
`1 ∉ hΓ`: elements of `Γ = EL_r(R_+)` are products of elementary matrices
over the subring `R_+` and so have all entries in `R_+`, while
`1 ∈ hΓ ⟺ h^{-1} = e_12(−(x_1⋯x_d)^{-1}) ∈ Γ` has an entry outside `R_+`.

**Item 3.**  With `M ≥ 2·C^{1/ε + 2}`, item 2 gives every nontrivial
kernel word length `≥ 1/ε + 1 > 1/ε`; every slot-admissible word valued in
`ker π_M ∩ hΓ` is such a word by item 1's nontriviality, so the necessary
condition of `pair-constraint-graph-criterion` item 3 holds with room to
spare.  No claim of sufficiency is made; the surviving question is recorded
as `marked-pair-cut-problem`.
