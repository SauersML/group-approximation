---
rg: 2
id: scalar-unitary-commutators-force-k0-trace-values
kind: claim
title: If unitaries U, V in M_n(A) satisfy V U V^-1 U^-1 = exp(2 pi i theta), then n theta lies in the K_0 trace image; over a torsion-free group a non-integer n theta refutes Kadison--Kaplansky on G * Z
distinct_from:
  reduced-projection-iff-gapped-spectral-measure: that detects projections through gaps in spectral measures of one self-adjoint element; this detects K_0 trace values through exact scalar commutators of two unitaries, a second witness shape with no spectral gap in it.
  fractional-matrix-trace-gives-projection-in-g-star-z: that turns a K_0 trace defect into a projection; this is a source of K_0 trace defects, Heisenberg relations with scalar commutator.
---

**ESTABLISHED** by `scalar-unitary-commutators-force-k0-trace-values-proof`.

**Theorem.** Let `A` be a unital C\*-algebra with a tracial state `τ`, with `τ_*` its unnormalized
extension to matrices. If `U, V ∈ M_n(A)` are unitaries with

```text
V U V^(-1) U^(-1)  =  exp(2πiθ) · 1_n ,
```

then `nθ ∈ τ_*(K_0(A))`.

**Consequences.**
- **A third witness shape.** Let `G` be torsion-free, and let `U, V ∈ M_n(C*_r G)` be unitaries whose
  commutator is the scalar `exp(2πiθ)` with `nθ ∉ Z`. Then `τ_*(K_0(C*_r G)) ⊄ Z`. By
  `fractional-matrix-trace-gives-projection-in-g-star-z`, `C*_r(G * Z)` then has a nontrivial
  projection. When `C*_r(G)` is selfless, `C*_r(G)` itself has one
  (`selfless-projection-traces-equal-k0-trace-image`). So an exact rotation relation with non-integer
  `nθ` inside matrices over the reduced algebra of a torsion-free group is a Kadison--Kaplansky
  counterexample.
- **Group elements never qualify.** For `U = λ(g)` and `V = λ(h)`, the commutator is `λ([h,g])`,
  which is scalar only when `[h,g] = e`, and then `θ ∈ Z`. A witness must use exotic unitaries.
- **Obstruction form.** Let `G` be torsion-free with `τ_*(K_0(C*_r G)) ⊆ Z`, for example any
  torsion-free group with surjective assembly. Then no `M_n(C*_r G)` contains a rotation pair with
  `nθ ∉ Z`. In particular there is no unital `*`-homomorphism `A_θ → M_n(C*_r G)` with `θ ∉ Q`.
  Neither the trace nor injectivity needs to be preserved.

**Model tests.**
- In `A_θ` itself `θ ∈ Z + θZ = τ_*(K_0(A_θ))`.
- In a commutative algebra such as `C*_r(Z^2)` only `θ ∈ Z` occurs.
- A trivial model cannot fail the hypothesis silently: `A = C` forces `exp(2πiθ) = 1`, so `θ ∈ Z`.

**Credit.** The mechanism is the de la Harpe--Skandalis determinant
(*Déterminant associé à une trace sur une algèbre de Banach*, Ann. Inst. Fourier 34 (1984)). That
paper was not re-read, and the proof route derives everything it uses from Bott periodicity. The
observation is classical in spirit; its use here as a witness shape for Kadison--Kaplansky is packaging.
