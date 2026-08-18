---
rg: 2
id: transported-pauli-exceptional-commutator-infinite-order
kind: claim
title: The exceptional transported-Pauli/raw commutator has infinite order
distinct_from:
  pauli-carrier-membership-decoder: This proves one explicit mixed raw/comb direction is genuinely infinite; it does not yet recover the transported carrier inside the raw binary algebra.
artifacts:
  - docs/TRUE_TRANSPORTED_PAULI_ORBIT_FINGERPRINT.md
  - experiments/atlas_double_pauli_comb_blocks.py
---

In the exact binary Leavitt-prefix image used by the transported-Pauli audit,
let `raw` be the raw compressor, let `X'_1=comb^* X_1 comb`, and put

```text
h = [X'_1,raw] = X'_1 raw X'_1 raw.
```

Then `h` has infinite order.  More precisely, in the standard `Z`-grading of
the binary Leavitt algebra, the unique lowest homogeneous term of `h` has
degree `-8` and is

```text
m = 00 (0010101010)^* = 00 (00 10101010)^*.
```

For every `n>=1`, the degree `-8n` homogeneous component of `h^n` is the
single nonzero prefix monomial

```text
m^n = 00 (00 (10101010)^n)^*.
```

Hence `h^n != 1` for every positive `n`.

This upgrades `(POF10)` in
`TRUE_TRANSPORTED_PAULI_ORBIT_FINGERPRINT.md` from the bounded statement
"none through exponent 128" to an all-depth theorem.  It identifies a first
explicit genuinely infinite mixed raw/comb direction.  What remains open is
the useful-action question: whether this direction yields a recoverable
multiplication/covariance module on the raw coefficient packet, rather than
merely an infinite transverse orbit.
