---
rg: 2
id: pauli-block-phases-have-uniform-two-matching-soundness
kind: claim
title: Signed Pauli block phases have uniform primitive two-matching soundness
distinct_from:
  matrix-phased-translations-exact-identity-scalarize: that allows arbitrary matrix phases but assumes the identity matching exact; this allows both matching errors and uses the discrete Pauli quotient jointly with the identity test.
  schreier-matchings-kill-alternating-forms: that changes the sampler to bounded involutive linear generators; this keeps the original primitive field multiplier and treats its induced symplectic obstruction after affine label correction.
---

ESTABLISHED.  In `(MP1)`, suppose `E` is a tensor power of `C^2` and every
block phase is a signed Hermitian Pauli operator:

```text
R_x=sigma_x W(v_x),       sigma_x in {+1,-1},
                         v_x in F_2^(2m).                    (PB1)
```

Let `epsilon_1^2` and `epsilon_alpha^2` be the normalized-HS energies of the
identity and primitive-alpha matchings.  There is a universal constant `C`
such that

```text
E_(a,b)||X(a)Z(b)-Z(b)X(a)||_2^2
 <= C(epsilon_1^2+epsilon_alpha^2).                           (PB2)
```

The constant is independent of `n`, the number `m` of qubits, the matrix
dimension, and Pauli multiplicity.  Thus neither high-dimensional Clifford
mixing nor a sparse Pauli anticommutation graph gives a primitive two-matching
counterrepresentation once the alpha relation is imposed jointly.

The proof is `pauli-block-two-matching-soundness-proof`.  Its three uniform
inputs are: scalar affine-orbit soundness after random linear functionals of
the Pauli label, alphabet-independent affine correction, and the constant
minimum distance of a nonzero binary polynomial of degree at most two.
