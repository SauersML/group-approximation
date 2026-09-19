---
rg: 2
id: homogeneous-k-orbit-factor-has-no-finite-a-refinement
kind: claim
title: The finite K-orbit factor has no finite equivariant refinement for the dense arithmetic action
distinct_from:
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that constructs the K-orbit commutant leak and gives its matrix-ultraproduct consequence; this isolates the exact finite-factor obstruction behind the failure of common congruence levels.
  sl2-homogeneous-quotient-crossed-product-is-connes-embeddable: that asks for arbitrary non-Cartan matrix microstates of the crossed product; this only excludes exact finite action models extending the integral K-orbit factor.
  coordinate-action-not-sofic: that is nonsoficity of a Kun--Thom coset action; this is an exact finite-factor theorem for the compact homogeneous quotient and makes no claim about approximate action models.
---

Put

```text
L = SL_n(Q_p),  K = SL_n(Z_p),
A = SL_n(Z[1/p]),  C = SL_n(Z),  X = L/Lambda',
```

where `Lambda' < L` is a cocompact lattice and
`r=|K\L/Lambda'|>=2`.  The `C`-invariant algebra

```text
D_C = L^infinity(X)^C = L^infinity(X)^K = C^r
```

is not contained in any finite-dimensional `A`-invariant von Neumann
subalgebra of `L^infinity(X)`.  Equivalently, the finite `K`-orbit partition
has no finite `A`-equivariant refinement.  In particular there is no common
finite action level on which the two adjacent profinite pieces in `(HQ5)`
act while retaining the nonconstant `K`-orbit label.

The proof is
`dense-transitive-action-has-no-nontrivial-finite-factor-proof`.

**Scope.**  This kills exact common-level, Cartan-preserving constructions.
It does not decide whether
`L^infinity(X) rtimes A` is Connes embeddable: a matrix-ultraproduct embedding
need not arise from finite `A`-actions and need not carry
`L^infinity(X)` into diagonal algebras.  Therefore the surviving positive
route is necessarily non-Cartan, while the surviving negative route must
exclude such non-Cartan microstates rather than merely repeat the
finite-level mismatch.
