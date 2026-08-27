---
rg: 2
id: native-hecke-graph-action-is-the-permanence-firewall
kind: claim
title: Soficity of the arithmetic Hecke graph action would make the native candidate sofic
distinct_from:
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that uses the complete-graph/commuting lamp algebra and Connes embeddability; this applies the graph-wreath permanence theorem directly to the smaller right-angled Coxeter candidate.
  native-sl3-group-is-hecke-graph-wreath-product: that is the algebraic identification; this audits the current sofic permanence boundary.
---

The 2024 theorem of Gao--Patchell--Kunnawalkam Elayavalli, *Sofic actions on
graphs* (arXiv:2408.15470, Theorem 1.12), says that if a sofic group acts
soficly on a graph and the vertex group is sofic, then the associated graph
wreath product is sofic.

Here `A=SL_3(Z[1/2])` is linear and hence sofic, and the vertex group `C_2`
is finite.  Therefore

```text
A acting soficly on Theta_h
    ==> G_cc is sofic
    ==> G_cc is hyperlinear.                            (SPF1)
```

Consequently the native transfer claim implies, in particular, that this
explicit arithmetic Hecke graph action is **not sofic**.

The published automatic-action theorem does not decide this case: it proves
soficity for transitive graph actions of sofic groups with amenable vertex
stabilizer, whereas the stabilizer here is

```text
Stab_A(C)=C=SL_3(Z),
```

which is nonamenable and Kazhdan.  Profinite density of `C` in `A` blocks
exact finite quotient models but does not by itself block approximate sofic
graph actions.  Thus no known graph-product or graph-wreath permanence
theorem presently refutes `G_cc`; it relocates the candidate's difficulty to
the soficity of one explicit nonamenable-stabilizer Hecke action.
