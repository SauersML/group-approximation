---
rg: 2
id: schur-packet-head-actuator-generates-over-tail-proof
kind: route
title: Scale the missing packet coordinate by the Toeplitz head swap
target: schur-packet-head-actuator-generates-over-tail
requires:
  - toeplitz-head-tail-unital-self-embedding
  - toeplitz-tail-plus-one-swap-generates
  - predicate-rank-gate-doubles-restriction-multiplicity
---

Use the faithful lower-unitriangular model from
`schur-child-crosses-toeplitz-compressor-proof`.  Its only multiplication
term is `B_p q'`.  Scale every `q`- and central coordinate by `e_2`, every
baseline `p`-coordinate by `1`, and the extra `p_m`-coordinate and its
`B_p` block by `s`.  The head swap is the identity on tape cells numbered at
least two, hence

```text
s e_2=e_2,       1 e_2=e_2.                              (SAT3)
```

These are exactly the identities needed for every commutator coefficient,
so the finite packet multiplication table is unchanged.  The distinct
storage coordinates and `s,e_2!=0` make the model faithful.  All child
coefficients lie in the unital subring `sigma(T)`, proving the first part of
`(SAT2)`.

The extra packet generator has a storage root with coefficient `s`, together
with finitely many triangular `s`-entries.  Elementary row and column
commutators with coefficient-one roots in `EL_r(sigma(T))` isolate the storage
root; conversely they generate and cancel the other `s`-entries.  Hence
`<alpha(Gamma),iota(B_f)>` contains one elementary root `e_ij(s)`.  Weyl
elements over `1 in sigma(T)` move it to every root position.  Since

```text
T=<sigma(T),s>
```

by `(TSG3)`, the standard elementary commutator relation
`[e_ij(a),e_jk(b)]=e_ik(ab)` shows that these roots generate `EL_r(T)`.
This proves the second part of `(SAT2)`.

The accompanying MSI experiment checks `(SAT3)`, all `128^2` products in a
nondegenerate two-pair/three-center packet table, faithfulness, and the full
matrix-algebra generation of head/tail truncations of sizes three through
ten.
