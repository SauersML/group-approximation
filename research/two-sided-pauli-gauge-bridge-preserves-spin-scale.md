---
rg: 2
id: two-sided-pauli-gauge-bridge-preserves-spin-scale
kind: claim
title: A two-sided Pauli bridge renews private gauges while preserving conditional spin multiplicity
distinct_from:
  branch-reset-amalgam-preserves-mark-and-balances-types: that balances one raw selector chart against a reset group and does not attach a second semantic context; this uses the two transverse maximal abelian charts of one Pauli group to connect old and new gauge-doubled contexts.
  selector-free-spin-reset-leaves-contexts-independent: that leaves all old/fresh sign pairs independent; this forces both private gauge distributions to the same uniform ray conditional on every shared logical character.
  derived-lifted-gauge-reset-spin-bridge: that tries to make the forward semidirect implementer a commutator phase in the next Schur packet; this bypasses that requirement with a two-sided finite connector.
---

Fix a finite elementary abelian logical overlap `T` and `k` private gauge
bits. Let `G_0,G_1` be finite marked packet groups containing

```text
D_0=<J,T,z_1,...,z_k>,       D_1=<J,T,s_1,...,s_k>,     (TPG1)
```

and suppose that, for every logical character `lambda` and private gauge
character `epsilon`, each relevant marked packet simple has dimension `D`
and restricts to `D` copies of the corresponding character of `D_a`.

Let `E_k` be the extraspecial Pauli group with diagonal generators `Z_i`,
transverse generators `X_i`, and central sign `J`. Put `H=E_k times T` and
embed

```text
D_0 -> H: z_i -> Z_i,       D_1 -> H: s_i -> X_i.       (TPG2)
```

Then the graph-of-groups fundamental group

```text
Gamma=G_0 *_(D_0) H *_(D_1) G_1                         (TPG3)
```

embeds both packet factors and has the following exact marked
representation-ring law. Conditional on any `lambda`, if
`m^a_(lambda,epsilon)` are the packet-simple multiplicities and `n_lambda` is
the multiplicity of the unique `J=-1` spin type of `H`, then

```text
D m^0_(lambda,epsilon)=n_lambda
 =D m^1_(lambda,epsilon)       for every epsilon.        (TPG4)
```

Thus both private gauge charts are uniform, their total multiplicities agree,
and the common multiplicity currency remains measured in units of the same
packet dimension `D`. No old logical selector is identified with a transverse
new selector; only private gauge shares enter `(TPG2)`.

For approximate finite-dimensional models, exactify the three fixed finite
tables and align their two abelian overlaps. The weighted distance from
`(TPG4)` is at most `C sqrt(E)`, with `C` independent of ambient dimension.

