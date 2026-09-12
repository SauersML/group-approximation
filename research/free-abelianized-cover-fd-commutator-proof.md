---
rg: 2
id: free-abelianized-cover-fd-commutator-proof
kind: route
title: Kill the eigenspace permutation and the block conjugation action, both of which factor through the base
target: free-abelianized-cover-fd-radical-is-commutator
requires:
  - free-abelianized-cover-has-nontrivial-fd-radical
  - universal-mf-quotient
artifacts:
  - research/artifacts/torsion-free-cover-fd-radical-and-heisenberg-2026-09-08.md
---

Assume `Rad_MF(G) = G`.  By `universal-mf-quotient` every homomorphism from
`G` to a countable MF group is trivial, since such a homomorphism factors
through `G/Rad_MF(G) = 1`.

Two families of groups are used as MF targets, and both are covered by
existing nodes.  Finite groups are residually finite, hence MF
(`mf-positive-controls`).  A countable subgroup of `U(m)` is MF because a
finite-dimensional unitary representation is a constant-sequence
representation into the norm-matrix corona, and a constant sequence is null
only if it is zero; that is the same observation the chain
`Rad_MF <= Rad_fd <= Res_fin` rests on in
`five-radicals-from-residually-finite-target`.

## 1. Every joint eigenspace is invariant

Let `rho : E -> U(d)`.  The first prerequisite's proof supplies the joint
eigenspace decomposition for the abelian kernel,

```text
C^d = H_1 (+) ... (+) H_k,     rho(a)|_(H_j) = chi_j(a) I,            (EIG)
```

and the permutation homomorphism `G -> Sym(k)` of `(PERM)`.  `Sym(k)` is
finite, hence MF, so that homomorphism is trivial.  Therefore every `H_j` is
invariant under all of `E`.

## 2. Each block acts by scalars

Fix `j` and put `m = dim H_j`.  Equip `M_m(C)` with the Hilbert-Schmidt inner
product and consider

```text
sigma(e) B = rho(e)|_(H_j) B rho(e)|_(H_j)^*.
```

Conjugation by a unitary preserves the Hilbert-Schmidt inner product, so
`sigma : E -> U(M_m(C))` is a finite-dimensional unitary representation of
`E`, of dimension `m^2`.  By `(EIG)` the elements of `A` act on `H_j` as
scalars, and scalars conjugate trivially, so `sigma` kills `A` and factors
through `G`.  Its image is a countable subgroup of a unitary group, hence MF,
so the hypothesis forces `sigma` to be trivial.

Thus `rho(e)|_(H_j)` commutes with every `B in M_m(C)`.  Commuting with the
diagonal matrix units forces a matrix to be diagonal, and commuting with the
off-diagonal matrix units then forces the diagonal entries to be equal, so
`rho(e)|_(H_j)` is scalar.

Since this holds for every block and the blocks are invariant, `rho(E)` is
abelian, so `[E,E] <= ker rho`.  As `rho` was arbitrary,

```text
[E,E] <= Rad_fd(E).
```

## 3. The reverse inclusion

`[R,R] <= [F,F]`, so

```text
E/[E,E] = F/[F,F][R,R] = F/[F,F],
```

free abelian on `X u {z}`.  Characters separate a free abelian group of any
rank: given a nonzero element, choose a coordinate with nonzero entry `m`, a
prime `p` not dividing `m`, and send that coordinate to `exp(2 pi i / p)` and
every other coordinate to `1`; the value at the element is
`exp(2 pi i m/p) != 1`.  Composing with `E ->> E/[E,E]` gives a
one-dimensional unitary representation of `E` detecting any element outside
`[E,E]`, so `Rad_fd(E) <= [E,E]`.  Together with step 2 this is `(FDC1)`.

## 4. Nontriviality

If `G != 1` pick `g != 1` and `f` with `q(f) = g`.  The detector `(DET)` of
the first prerequisite gives `[fbar, zbar] != 1`, and it lies in `[E,E]`.  So
`Rad_fd(E) = [E,E] != 1`.

(The hypothesis makes this automatic in another way as well: a group with full
MF radical has no nontrivial finite quotient, so it is not residually finite
unless trivial, and the first prerequisite already applies.)
