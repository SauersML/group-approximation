---
rg: 2
id: trace-zero-involution-projective-transfer-equals-rcc
kind: claim
title: Trace-zero involution projective transfer is already the full relative-commutant wall
distinct_from:
  projective-transfer-equals-rcc-for-perfect-pairs: that identifies arbitrary-unitary projective transfer with ordinary relative-commutant collapse for perfect pairs; this proves that restricting the transferred witness to a trace-zero self-adjoint involution does not weaken the qualitative statement.
  sl3-two-point-lamp-mark-is-single-rcc-scalar: that consumes one involutory witness furnished by the arithmetic lamp group; this audits whether the involution hypothesis itself makes the missing transfer easier and proves that it does not.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that supplies the canonical commuting-coordinate producer; this is a representation-theoretic reduction applying to every relative-commutant leak, without assuming a Bernoulli model.
---

Let `C <= A = <C,h>` and let `pi:A->U(M)` be a representation in a finite
tracial von Neumann algebra.  If there is a unitary

```text
u in pi(C)' cap M
```

for which `[u,pi(h)]` is not scalar, then in `M_2(M)` there is a
**trace-zero self-adjoint involution**

```text
v in pi_2(C)' cap M_2(M)
```

for which `[v,pi_2(h)]` is not scalar.  Quantitatively, if

```text
e(u,pi(h)) = 1-|tau([u,pi(h)])|^2 >= epsilon,
```

then

```text
e(v,pi_2(h))
 >= Phi(epsilon)
 := 1-((1+sqrt(1-epsilon))/2)^2 > 0.                 (TZI1)
```

Consequently, for perfect `C` and `A`, the following qualitative statements
are equivalent in tracial matrix ultraproducts:

1. `pi(C)'=pi(A)'`;
2. projective centrality transfers from `C` to `h` for every unitary;
3. projective centrality transfers from `C` to `h` for trace-zero
   self-adjoint involutions only.

Thus merely specializing PRCC to the involutory base lamp does **not** lower
the qualitative matrix-coordinate wall.  Any genuinely weaker lamp theorem
must use additional joint relations of that lamp, such as

```text
[c,h c h^-1]=1,
```

or its full commuting-orbit/canonical mixed-moment packet; the conditions
`c^2=1`, `tau(c)=0`, and `[c,C]=1` alone cannot be the source of a shortcut.

The statement is amplification-stable and needs no dimension-dependent
constant.  In particular a positive-energy sequence remains positive-energy
after the `2 x 2` dilation by the explicit modulus `(TZI1)`.
