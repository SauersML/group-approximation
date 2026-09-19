# STW VIII / IX(2): status and coherence audit (2026-08-30)

## Current-status check

Problem VIII remains open in the current primary sources checked.

- Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*,
  [arXiv:2506.10902](https://arxiv.org/abs/2506.10902), v2 with addenda through
  April 2026, states VIII as the open question whether every separable exact
  quasidiagonal C\*-algebra is AF-embeddable and states IX(2) as its faithful
  quasidiagonal-trace special case.
- Y. Liu, *Characterizing AF-embeddable C\*-algebras by representations*,
  [Acta Math. Hungar. 173 (2024), 139--153](https://doi.org/10.1007/s10474-024-01442-x),
  describes the same assertion as a major open problem and gives a
  representation-theoretic equivalence, not a solution.
- Moradi--Amini, *On locally finite-dimensional traces II*,
  [arXiv:2606.13924](https://arxiv.org/abs/2606.13924), proves new results on
  quasidiagonal and locally finite-dimensional traces but does not claim VIII
  or IX(2).
- Dadarlat, *AF-embeddings of residually finite-dimensional C\*-algebras*,
  [Muenster J. Math. 11 (2018), 211--216](https://www.uni-muenster.de/FB10/mjm/vol_11/mjm_vol_11_05.pdf),
  Theorem 1.1, proves UHF-embeddability for separable exact RFD algebras whose
  rational `K^0`-homology is locally finitely generated.  This is used below
  for a semiprojective positive class, not as a solution of VIII.

The February 2026 seminar announcement about AF embeddings for certain
decomposition-rank-one systems was not used as a theorem: no primary preprint
containing that result was located in the check.

## Exact gap exposed by the audit

Quasidiagonality gives c.p.c. maps to unrelated finite-dimensional algebras
which are asymptotically multiplicative and isometric.  An embedding into an
AF inductive limit requires more: after choosing connecting homomorphisms, the
successive maps must be summably close.  Block-summing independent models does
not repair this in operator norm, because every old bad block survives
isometrically under an injective connecting map.

For a faithful quasidiagonal trace, norm detection can be recovered from
faithfulness once multiplicative models are coherently connected.  The trace
version therefore isolates two missing compatibility requirements: connecting
homomorphisms between the finite-dimensional models and compatible traces on
those models.

The Cairn nodes attached to this audit prove both coherence criteria from
scratch.  They do not assert that exactness produces the missing coherence.

## Finite-group permanence without a coherence theorem

There is a separate situation in which no interstage coherence has to be
created.  If `eta:A->E` is any AF embedding and a finite group `F` acts on
`A`, the finite regular covariant representation gives an injective map

```text
A rtimes F -> M_|F|(E).
```

The coefficient algebra is represented diagonally using the finitely many
maps `eta alpha_(t^-1)`, while the group acts by permutation matrices.
Faithfulness follows from the coefficient expectation, and the target is AF.
Crucially, the action is not required to extend to `E`.

The same matrix model respects traces: if `sigma eta=tau` and `tau` is
invariant, then `tr_|F| tensor sigma` restricts to `tau E_A`.  Thus both plain
and trace-preserving AF-embeddability pass through finite crossed products.
For group algebras, the analogous coset regular representation proves that
AF-embeddability passes from a finite-index subgroup of a countable amenable
group to the whole group, without normality or splitting.

This finite-dimensional reservoir is essential to the argument.  For an
infinite acting group the regular representation lands in adjointable
operators on an infinite Hilbert module, not in a finite matrix amplification
of the AF target.  The theorem therefore supplies no permanence for general
`Z`-crossed products and does not address the unsolved step of coherifying
arbitrary quasidiagonal models.

## Continuous blocks and finite pullback gluings

AF-embeddability also has a constructive continuous-coordinate permanence
which is independent of the finite crossed-product argument.  For a
second-countable locally compact `X`, choose a Cantor surjection

```text
K -> X^+.
```

It gives `C_0(X)->C(K)`.  Tensoring this inclusion with an AF embedding
`A->E` gives

```text
C_0(X,A) -> C(K) tensor_min E,
```

and the target is AF.  Hence every C*-subalgebra of a finite direct sum of
such continuous blocks is AF-embeddable.  A finite pullback tree embeds by
its leaf-coordinate maps into precisely such a finite direct sum, so no
surjectivity assumption is needed.  Mapping tori and finite recursive
subhomogeneous constructions are immediate special cases.

The construction retains a useful unital trace statement.  If the `X_j` are
compact and a faithful `tau_j` extends across a unital `A_j->E_j`, choose a
full-support probability `mu_j` on `X_j`.  Extend the state `mu_j` from the
pulled-back copy of `C(X_j)` to `C(K_j)`; its representing measure `nu_j`
pushes forward to `mu_j`.  Then `nu_j tensor sigma_j` extends
`mu_j tensor tau_j`.  Positive weighted coordinate sums are faithful states
on every common-unit subalgebra of the finite direct sum and extend to the
direct sum of the AF targets.  Their restrictions are therefore
quasidiagonal traces.  This is a trace-preserving permanence theorem for
IX(2), not a construction of an AF embedding from an arbitrary
quasidiagonal trace.
