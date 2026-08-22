---
rg: 2
id: extraspecial-fourier-zero-cell-is-fixed-face-pruning
kind: claim
title: The extraspecial Fourier zero cell is exactly deletion of a shear-fixed character face
distinct_from:
  extraspecial-common-gauge-fourier-controller: that constructs the common-gauge controller and stops at its joint Pauli atom; this identifies the exact finite character action of its corrected payload and proves the finite-normalizer no-go.
  finite-clifford-couplings-cannot-prune-a-forbidden-atom: that treats an arbitrary forbidden selector character in a finite Clifford overgroup; this computes the specific shear and fixed face created by ESF3--ESF9.
  central-marked-two-cycle-zero-compression-cell: that succeeds when the selected source is moved to a disjoint atom; this proves that the ESF source fails precisely on the payload-trivial fixed face.
---

**ESTABLISHED.**  Retain the notation of
`extraspecial-common-gauge-fourier-controller` and put

```text
V=SC,                     U_i=S W_i S^-1.              (EFZ1)
```

The `U_i` are commuting involutions commuting with the Pauli packet.  The
relations and `V^2=1` give

```text
V X_i V^-1=U_i X_i,       V U_i V^-1=U_i.             (EFZ2)
```

Thus `V` normalizes the finite abelian group

```text
D=<J,X_1,...,X_k,U_1,...,U_k>                          (EFZ3)
```

by a shear.  On its character labels `(a,chi) in K x K^dual`, with `a`
the `X`-character, the shear is

```text
(a,chi) |-> (a+chi,chi).                               (EFZ4)
```

The ESF source `q` is the marked face `J=-1,a=0`, with `chi` unrestricted.
Consequently its intersection with its `V`-translate is exactly

```text
J=-1,              a=0,              chi=0.           (EFZ5)
```

This is the trivial-payload projection `P_K` in `(ESF5)`.  Hence the desired
ordinary zero-compression relation is not missing a further Fourier
calculation: it must delete the fixed face `(EFZ5)`.

No bounded completion consisting of a finite group normalizer table can do
this while preserving `D`.  Let `G` be any finite coupled group containing
`D`, with `J` central, and containing `V` with action `(EFZ2)`.  The character

```text
lambda(J)=-1,        lambda(X_i)=lambda(U_i)=1         (EFZ6)
```

is fixed by `V`, so it extends to `<D,V>` by choosing `lambda(V)=1`.
Inducing this character to `G` gives a finite-dimensional marked
representation in which the vector over the identity coset lies in `q` and
is fixed by `V`.  In particular

```text
q V q !=0.                                                (EFZ7)
```

The same conclusion holds for a residually finite completion in which the
finite subgroup `<D,V>` embeds: pass to a finite quotient injective on it and
apply the same induction argument.

If a proposed finite table evades `(EFZ7)` by making `D` noninjective, then
`(EFZ6)` fails to descend only when the kernel contains a word having odd
`J` exponent and trivial `X,U` exponents.  Equivalently the marked sign has
been identified with an affine parity word in the selector/payload group.
That is exactly affine-support cheating; it cannot encode absence of only
the trivial payload character for `k>1`.

Therefore ESF3--ESF9 rule out every finite or residually finite
normalizer-based wordization of the rank-`1/|K|` source.  A surviving cell
must make the payload word participate outside its finite shear normalizer
(a nonnormal corner/two-cell), or use an infinite non-residually-finite actor
whose finite-dimensional representations cannot retain `(EFZ5)`.
