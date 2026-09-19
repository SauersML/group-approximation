---
rg: 2
id: multiplicity-space-centralization-after-code-block-pinching
kind: claim
title: Centralize or refine the zero-adjoint multiplicity algebra after transverse code-block pinching
distinct_from:
  code-distance-upgrades-pair-energy-to-full-pinching: that removes every nonzero adjoint code character and rounds one reflection into the code PVM commutant; this asks to abelianize the untouched zero-character multiplicity algebra.
  bounded-type-noncentral-code-sectors-round-uniformly: that rounds multiplicity algebras of uniformly bounded irreducible type by compactness; this asks for one modulus on unbounded-type diffuse blocks.
  repeated-ldpc-shared-face-marginal-synchronization: that is the full occurrence synchronization statement; this isolates its residual after transverse code-character and sparse-tail correction.
---

OPEN.  Work on the diffuse block left by the common outlier cut.  After the
transverse correction from
`code-distance-upgrades-pair-energy-to-full-pinching`, let

```text
A=span{q_c:c in C}
```

be an exact code PVM algebra.  The remaining coordinate reflections lie,
up to the controlled transverse error, in

```text
A'=direct_sum_(c in C) q_c M q_c.                         (MSC1)
```

Prove a dimension- and length-independent modulus which uses the balanced
equality, local all-dual parity, and complete-pair energies to produce a
refining PVM

```text
(p_(c,z))_(c,z in C),   p_(c,z)<=q_c,   sum_z p_(c,z)=q_c, (MSC2)
```

such that the refined code reflections

```text
T_i=sum_(c,z) (-1)^(z_i)p_(c,z)                           (MSC3)
```

approximate all synchronized coordinate occurrences in average normalized
Hilbert--Schmidt distance.  Equivalently, the balanced test must abelianize
the within-atom multiplicity representations, not merely make them commute
with the outer code labels.

The obstruction is exact.  Relative to `A`, an operator block
`q_c X q_c` has zero adjoint character.  Therefore code distance, the
generator/full-pinching inequality, and every transverse Fourier estimate
assign it zero energy.  In the extreme one-atom case `q_0=I`, all reference
reflections are `S_i=I`; then every reflection already commutes with `A` at
zero cost.  Code-block pinching has made no progress at all on the internal
tuple.  Thus a proof must exploit the balanced relations **inside** each
multiplicity block and show genuine contraction or common refinement there.

This is the precise genuinely noncentral diffuse gate.  The all-local-dual
tail inequality can peel sparse coordinate support into a shortened core,
and relative code distance handles every nonzero adjoint character on that
core.  Neither result sees `(MSC1)`'s zero-character summands.  A positive
proof must supply an operator-valued agreement/self-improvement step which
is stable under arbitrary direct sums and arbitrary block dimensions.

## Attempts

1. **Apply de la Salle blockwise.**  Theorem 1.4 of
   [de la Salle, arXiv:2103.14126](https://arxiv.org/abs/2103.14126)
   rounds one PVM to commute with a fixed PVM in the same algebra.  With
   fixed PVM `(q_c)`, its output lies in `A'`, exactly `(MSC1)`.  It does not
   make two independently rounded coordinate PVMs commute within `q_cMq_c`.
   The one-atom example shows this loss is sharp.

2. **Round many almost-commuting reflections generically.**  Glebsky's
   [Theorem 4, arXiv:1002.3082](https://arxiv.org/abs/1002.3082) gives a
   normalized-HS modulus `delta(epsilon,k)` for each fixed number `k` of
   selfadjoint matrices.  It is not uniform as `k=L` grows.  The repository's
   sparse Clifford cycle shows that no such uniform theorem can follow from
   average pair energy alone; the parity layer must enter the proof.

3. **Invoke graph-product stability.**  Spaas
   [arXiv:2603.02058](https://arxiv.org/abs/2603.02058) proves strict
   same-dimension HS stability for each fixed chordal graph product of
   abelian groups.  The theorem has no graph-uniform averaged-relator
   modulus, and the occurrence equalities and parity words are quotient
   relations outside the graph-product presentation.  It therefore does
   not act on the internal blocks in `(MSC1)`.

4. **Import operator-valued agreement testing.**  Ji--Natarajan--Vidick--
   Wright--Yuen
   [arXiv:2111.08131](https://arxiv.org/abs/2111.08131) construct a common
   codeword PVM in the same tracial algebra, but their theorem assumes the
   augmented tensor-code line/point and subcube-commutation measurements.
   Those primitive common measurements, interpolation maps, and growing
   incidence are absent from the bounded-template all-dual LDPC overlay.
   Splitting them into bounded occurrences recreates `(MSC2)` as the missing
   agreement step.

5. **Treat relative commutation as enough.**  It is not.  Ioana's
   [non-HS-stability of `F_2 x F_2`, arXiv:2108.09589](https://arxiv.org/abs/2108.09589)
   warns that approximate relative commutation of two nonabelian families
   need not admit same-dimensional correction.  This does not give a
   counterexample to `(MSC2)`, because it lacks the all-dual parity and
   balanced overlay.  It does show that those extra relations must be used
   quantitatively; no abstract relative-commutant theorem can close the
   gate.

The most focused next attack is a blockwise self-improvement inequality:
construct from the local face PVMs a submeasurement refining `(q_c)` whose
orthogonality defect and inconsistency with every occurrence are bounded by
`o(1)` with constants independent of `|C|`, `L`, and the ranks `tau(q_c)`.
De la Salle orthogonalization would then finish `(MSC2)`; constructing that
submeasurement is the unresolved content.

