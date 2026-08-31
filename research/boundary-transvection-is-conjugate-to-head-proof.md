---
rg: 2
id: boundary-transvection-is-conjugate-to-head-proof
kind: route
title: The Toeplitz truncation error and head are conjugate rank-one transvections
target: toeplitz-folner-compressions-cannot-retain-jacobson-head
requires:
  - binary-jacobson-steinberg-cover-is-elementary
---

Let `v_0,...,v_(N-1)` be the standard basis of `F_2^N), and define

```text
S_N v_r=v_(r+1)       for r<N-1,       S_N v_(N-1)=0,
T_N v_0=0,            T_N v_r=v_(r-1) for r>0.
```

Direct evaluation on the basis gives

```text
T_N S_N=I-P_(N-1),                 S_N T_N=I-P_0,       (BTH1)
```

where `P_r` projects onto `F_2v_r`.

For an `N by N` matrix `a), write

```text
X_ij(a)=I_(28N)+E_ij tensor a.
```

These matrices obey the exact elementary identities

```text
X_ij(a)X_ij(b)=X_ij(a+b),
[X_ij(a),X_jk(b)]=X_ik(ab)                              (BTH2)
```

for distinct `i,j,k`. All signs disappear in characteristic two.

The finite-section value of the relation

```text
[x_ij(T),x_jk(S)] x_ik(1)^(-1)=1
```

is, by `(BTH1)--(BTH2)`,

```text
X_ik(T_N S_N)X_ik(I)^(-1)
 =X_ik(I-P_(N-1)+I)
 =X_ik(P_(N-1)).                                        (BTH3)
```

The head word has finite-section value

```text
X_ab(I-S_NT_N)=X_ab(P_0).                               (BTH4)
```

Both differences from the identity in `(BTH3)--(BTH4)` are rank-one
nilpotent operators with square zero. More explicitly,

```text
E_ik tensor P_(N-1)
```

sends the one basis vector `e_k tensor v_(N-1)` to
`e_i tensor v_(N-1)` and kills the other standard basis vectors.
The second operator does the same for the ordered pair

```text
e_b tensor v_0  |->  e_a tensor v_0.
```

A basis permutation carrying the first ordered pair to the second
conjugates one nilpotent to the other. Thus

```text
X_ik(P_(N-1)) and X_ab(P_0)
```

are conjugate in `GL_(28N)(F_2)`.

Let `rho_N` be any unitary representation of this finite group.
Images of conjugate elements are unitarily conjugate. Since normalized
Hilbert--Schmidt distance to the identity is invariant under unitary
conjugation, `(TFC2)` follows.

For a direct sum of such sectors, squared normalized Hilbert--Schmidt
distances are the dimension-weighted sums of the sectorwise squares.
The equality therefore remains exact after arbitrary multiplicities and
after mixing different values of `N`.

A fixed finite presentation may encode the displayed Steinberg relation
as a bounded derived word rather than a named relator. In that case its
defect is bounded by a fixed word-length multiple of the presentation
defect. Equation `(TFC2)` still forces the finite-section head defect
to zero whenever the presentation defect tends to zero.

The proof is specific about its scope. It rules out the ordinary
finite-section functor, including all choices of unitary representation
after truncation. It does not turn an arbitrary approximate group
representation back into truncated ring operators, which is the surviving
dimension-free rigidity problem.
