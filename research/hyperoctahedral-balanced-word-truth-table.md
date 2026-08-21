---
rg: 2
id: hyperoctahedral-balanced-word-truth-table
kind: claim
title: One balanced router word realizes every Boolean truth table in a hyperoctahedral packet
distinct_from:
  controlled-central-phase-finite-group-barrier: that rules out one central commutator character; this uses a full nonabelian signed-permutation packet and arbitrarily many balanced conjugates of one router.
  packet-dressed-shared-implementer-requires-one-outer-class: that bounds two dressed normalizers of one base group; this is an exact finite direct-power generation theorem for a translation tuple.
---

Let `A=C_2^r`, `N=|A|>=8`, and let

```text
B_N=C_2^N semidirect S_N
```

be the signed permutation group in its natural action.  Write `tau_a in S_N`
for translation by `a` in the regular action of `A` on itself, put
`k=(tau_a)_(a in A) in B_N^A`, and let

```text
H=<Delta(B_N'), k Delta(B_N') k^(-1)> <= (B_N')^A.     (HBT1)
```

Then

```text
(B_N')^A <= H.                                        (HBT2)
```

In fact

```text
H=(B_N')^A.                                           (HBT2')
```

In particular, because `N` is even, the scalar signed permutation
`z=-I_N` lies in `B_N'`.  For every subset `F subseteq A` there is a word
`W_F(t)` with constants from `B_N'`, built from constants and conjugates
`t g t^(-1)`, such that

```text
W_F(tau_a)=z  if a in F,
W_F(tau_a)=1  if a notin F.                            (HBT3)
```

The word is balanced in the variable `t`.  Consequently, on operators
`t=tau_a tensor V` and `g=g tensor I`, the external factor `V` cancels
identically and `(HBT3)` remains exact.  Since all groups are finite, a word
`W_F` is computable by breadth-first search in `H`.

More generally, `full-conjugation-table-cancels-router-multiplicity` shows
that no chosen tensor-product model is needed: if the router implements the
full conjugation table of `tau_a` on the constant packet, then every balanced
truth word has the intended value, with a dimension-free robust estimate, in
an arbitrary representation.  The remaining issue is encoding that
selector-dependent conjugation table by group relations.

## Proof

Inside the pure permutation subgroup `S_N^A`, consider

```text
L=<Delta(A_N), k Delta(A_N) k^(-1)>.
```

It is a subdirect product of copies of the nonabelian simple group `A_N`.
By the diagonal-block classification of subdirect powers of a nonabelian
simple group, two coordinates `a,b` can belong to one diagonal block only if
an automorphism `phi of A_N` identifies both coordinate maps.  The first
diagonal copy forces `phi=id`; the conjugated copy then forces

```text
tau_a g tau_a^(-1)=tau_b g tau_b^(-1)  for every g in A_N.
```

Thus `tau_b^(-1)tau_a` centralizes `A_N` in `S_N`.  That centralizer is
trivial, and the regular translations are distinct, so `a=b`.  Every block
is a singleton and hence `L=A_N^A`.

Let `d_j` flip the sign of the `j`-th natural basis vector.  Fix distinct
`j,k,l`.  The two-sign flip `e_(j,l)=d_jd_l` belongs to `B_N'`, so its
diagonal copy belongs to `H`.  Choose `pi in A_N` fixing `l` and sending `j`
to `k` (possible because `N>=8`).  Conjugate `Delta(e_(j,l))` by the element
which is `pi` in one chosen `A`-coordinate and the identity elsewhere, then
multiply by `Delta(e_(j,l))^(-1)`.  The result is trivial off that coordinate
and equals

```text
(d_k d_l)(d_j d_l)=d_j d_k
```

there.  Such pairs generate the even-sign subgroup `C_2^(N-1)` independently
in every coordinate.  Together with `A_N^A`, this gives

```text
(C_2^(N-1) semidirect A_N)^A=(B_N')^A <= H.
```

The reverse inclusion follows from the definition of `H`, proving `(HBT2')`.

Finally `z=-I_N` flips `N` signs and `N` is even, so `z in B_N'`.  Every
nonzero translation of `A` is a product of `N/2` transpositions; since
`N>=8`, this number is even, so every router `tau_a` also lies in `A_N` and
hence in `B_N'`.  The tuple
which is `z` precisely on `F` belongs to `H`.  Replacing generators of the
first diagonal copy by constants and generators of the second by
`t g t^(-1)` yields `(HBT3)` and makes the exponent sum of `t` zero.

## Interface warning

This theorem removes the **truth-table** and **common-router multiplicity**
problems, but does not by itself groupify a BCS context.  Pauli covariance
determines `t=tau_a tensor V` only on a Pauli isotypic carrier.  The constants
needed to generate `B_N'` leave the Pauli normalizer, so an arbitrary group
representation may attach additional multiplicity actions to those
constants.  A successful compiler must preserve a common finite type for
the whole hyperoctahedral constant packet, or cancel that second layer too.
