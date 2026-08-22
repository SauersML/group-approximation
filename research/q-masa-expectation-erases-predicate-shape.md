---
rg: 2
id: q-masa-expectation-erases-predicate-shape
kind: claim
title: The flip-free q-MASA expectation retains only the scalar predicate density
---

Let

```text
D_f=<J,z_1,...,z_k>,
K_f=<J,q_1,...,q_N,q_(N+1)>
```

inside a Schur packet, and let

```text
P_f=p_- sum_(x:f(x)=1) p_x,
p_-=(1-J)/2.
```

The subgroup calculation `(QMR2)` gives `D_f intersect K_f=<J>`. Hence

```text
C[D_f] intersect C[K_f]=C[J].                             (QEE1)
```

If `E_(K_f)` denotes coefficient truncation from the packet group algebra to
`C[K_f]`, then

```text
E_(K_f)(P_f)=(|f^(-1)(1)|/2^k) p_-.                      (QEE2)
```

For nonconstant `f`, `P_f` is not in `C[K_f]`. More strongly, two predicates
with the same number of satisfying assignments have identical images under
`E_(K_f)`, regardless of the locations of those assignments.

Thus the flip-free endpoint cannot be the algebra through which the explicit
Schur density

```text
P_f=2D(Z_(C_f)-Z_(B_f))
```

is sent to a proper corner. The packet-headed Toeplitz identity
`1-xy=P_f` is an exact pre-reset coupling, but it must be attached while the
selector algebra (or the full packet character-density element) is still
present. Passing first to a `K_f`-only HNN/Morita interface irreversibly
replaces the predicate by its scalar Hamming density. This is independent of
the later negative-regular averaging in
`full-reset-makes-q-masa-negative-regular`.

