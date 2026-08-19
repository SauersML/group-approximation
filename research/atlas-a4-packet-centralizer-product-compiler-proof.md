---
rg: 2
id: atlas-a4-packet-centralizer-product-compiler-proof
kind: route
title: Shift each local A4 rounding theorem by one fixed exact packet alignment
target: atlas-a4-packet-centralizer-product-compiler
requires:
  - atlas-shortest-a4-triangle-packet
  - a4-near-context-centralizer-product-rounding
artifacts:
  - experiments/atlas_a4_reference_alignment.py
---

Let `r_0` and `R_k=rho_k(r_0)` be the fixed inner alignment from the target
claim.  The audit verifies all thirty pair-cubes at `R_k`.  Thus for every
packet edge the appropriate **reference mixed pair** is a regular A4 pair,
even though the two unaligned same-chart letters need not generate A4.
Restriction of `Reg(A8)` to each such A4 is

```text
[A8:A4] Reg(A4) = 1680 Reg(A4),
```

so the local rounding theorem applies with multiplicity `1680 k_n`.

For a word `(b_2 a_1)^3`, put

```text
A=rho(a),
B_ref=R rho(b) R^*,
V=U R^*.
```

The reference pair `(A,B_ref)` is regular A4 and

```text
V B_ref V^* = U rho(b) U^*.
```

Hence the packet defect is exactly the defect entering
`a4-near-context-centralizer-product-rounding`.  It gives

```text
V = o_2(1) + C_A C_(B_ref)
  = o_2(1) + C_A R C_b R^*.
```

Multiplying on the right by `R` yields

```text
dist_2(U, C_A R C_b) -> 0.                            (1)
```

For a factor-reversed word `(b_1 a_2)^3`, conjugate the represented word by
`U^*`.  The fixed reference packet identity gives

```text
(R^* rho(b) R rho(a))^3=1.
```

Put

```text
A=rho(a),
B_ref=R^* rho(b) R,
V=U^* R.
```

Then `V B_ref V^*=U^*rho(b)U`, so local rounding gives

```text
dist_2(V, C_a R^* C_b R) -> 0.
```

Multiplying by `R^*` and taking adjoints gives

```text
dist_2(U, C_b R C_a) -> 0.                            (2)
```

There are exactly thirty contexts, independent of `n`.  Taking the maximum of
(1)--(2) proves `(A4-PACKET-CENT)`.

### Why the shift cannot be omitted

The unshifted compiler would require `(rho(a),rho(b))` itself to be the named
regular A4 pair.  Exact `GL_4(F2)` arithmetic shows that this is false for the
packet: some same-chart pair products have order `6` (the central `C3` edges of
the `S3 x C3` component), and the remaining checked packet products have order
`2`, not `3`.  The fixed alignment `R` is therefore mathematical data, not a
gauge convention.
