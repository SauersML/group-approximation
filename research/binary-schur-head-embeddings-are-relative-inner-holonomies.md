---
rg: 2
id: binary-schur-head-embeddings-are-relative-inner-holonomies
kind: claim
title: Every unital binary Schur head duplicates the full block and carries only a relative projective holonomy
distinct_from:
  binary-schur-child-toeplitz-self-embedding: that constructs one standard diagonal head embedding; this classifies all sectorwise unital embeddings and proves that deleting one child is impossible.
  hnn-conjugacy-cannot-return-schur-morita-multiplicity: that rules out a direct parent-child conjugacy by multiplicity vectors; this identifies the complete moduli of the matrix-amplified child embedding which avoids that obstruction.
  atlas-a4-packet-four-rectangle-normal-form: that reduces the A4 context network to four unitary cycle variables; this identifies relative projective holonomy as the only variable available in one binary Schur head.
---

Let `k` be a splitting field and let one forbidden Schur sector have

```text
I_x=M_n(k),                 M_2(C_x)=M_n(k) direct_sum M_n(k). (BRH1)
```

Every unital `k`-algebra homomorphism

```text
psi:I_x -> M_2(C_x)                                      (BRH2)
```

has the form

```text
psi(a)=(u_+ a u_+^-1, u_- a u_-^-1)                     (BRH3)
```

for some `u_+,u_- in GL_n(k)`.  Consequently both child components are
faithful and each target simple restricts to one copy of the unique `I_x`
simple.  Once the packet fixes the two child frames, the remaining comparison
datum is the relative class

```text
[h]=[u_-^-1 u_+] in PGL_n(k).                            (BRH4)
```

Indeed each coordinate projection of `psi` is a unital endomorphism of the
simple algebra `M_n(k)`.  It is injective, hence an automorphism by dimension,
and Skolem--Noether makes it inner.  This also proves that no unital binary
Toeplitz endomorphism with `Sigma(P)=1-x^2y^2` can send one child to the
augmentation or to zero: the two-site head unit has nonzero identity in both
simple components.

Under a common change of target head frame `(BRH4)` is unchanged; under a
change of source frame it is conjugated.  Independent changes of the two child
frames alter `(BRH4)` and are therefore edge gauges, not symmetries of one
fixed packet chart.  Their product around a closed return cycle is gauge
invariant up to conjugacy.

More generally, a unital map `M_n(k)->M_n(k)^m` consists of `m` inner
automorphisms and forces `m` faithful branches.  Thus changing the arity of
the Toeplitz shift never creates a paid exit by itself.

The classification turns the analytic return problem into a holonomy problem.
A branch-changing return chart can only compare the two inner frames, and a
cycle of such charts reads the product of their relative classes in
`PGL_n(k)`.  This is the precise slot in which the A4 atlas collision
`q_19243` can be installed: it is not a selector scalar and need not delete a
branch; it is a nontrivial relative projective frame around the return cycle.

The theorem is exact and dimension-free, but it does not prove that an
approximate matrix return pays for nontrivial `[h]`.  That quantitative
four-holonomy statement is the remaining content of the 19243 lane.
