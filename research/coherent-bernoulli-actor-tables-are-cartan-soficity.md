---
rg: 2
id: coherent-bernoulli-actor-tables-are-cartan-soficity
kind: claim
title: Coherent Bernoulli actor-table extraction is exactly Cartan completion and action soficity
distinct_from:
  finite-cylinder-mixed-traces-kill-normalizer-holonomy: that classicalizes an ALREADY EXACT finite transformation-group table; this proves that producing the joint table is the whole invariant-Cartan/sofic-action gate and gives a permutation-valued countermodel before joint multiplication.
  approximate-bernoulli-lamp-extraction-is-cartan-completion: that identifies the global missing lemma at the ultraproduct level; this supplies the finite completion dictionary, the forest-gauge calculation, and a sharp defect-one countermodel in which all individual cylinder tests are exact.
  scalar-trace-of-diagonal-normalizer-is-permutation-blind: that uses cancellation between two unitary blocks; this countermodel has honest finite permutations, exact atomwise mixed traces, and exact overlap covariance, so no bistochastic or scalar-trace weakness is involved.
---

**ESTABLISHED REDUCTION.**  Let `G` act on a countable set `X`, let

```text
A=L^infinity({+-1}^X),       M=A rtimes G,
```

and fix a trace-preserving embedding `Theta:M->product_U M_(d_n)`.  The
following are equivalent for this particular embedding.

1. After conjugating and amplifying representatives, its finite Bernoulli
   cylinder algebras admit one family of finite actor tables whose
   permutations are asymptotically multiplicative, implement all cylinder
   transports, and represent the actor unitaries modulo diagonal phases.
2. There is a full diagonal ultraproduct `D_U` such that

   ```text
   Theta(A) subset D_U,       Theta(u_g) D_U Theta(u_g)*=D_U
   for every g in G.                                      (CAT1)
   ```

Thus coherent extraction **from the given microstate** is exactly invariant
diagonal/Cartan completion, not a consequence of finite-window Fourier
moments.  If the requirement that the tables represent this particular
`Theta` is forgotten, existence of such a table sequence with the Bernoulli
cylinder laws is exactly soficity of the pmp Bernoulli action.  If the tables
also carry the coordinate-site decoder used in orbit approximations, their
existence is exactly soficity of the set action `G` on `X`.

For the Kun--Thom pair both relevant actions are nonsofic.  Consequently any
theorem extracting these tables from arbitrary normalized-HS microstates
would prove `invariant-cartan-completion`, hence non-Connes-embeddability of
the Kun--Thom crossed product.  It cannot be inserted as a routine rounding
step.

## The finite completion space

For a finite site window `F subset X`, put `Omega_F={+-1}^F`.  For `g in G`
the covariance equations determine only

```text
(g omega)_(g x)=omega_x     when x in F and g x in F.   (CAT2)
```

The partial site bijection in `(CAT2)` always extends to a bijection of `F`,
and hence to a permutation of `Omega_F`.  Therefore every actor element has
an individual exact completion.  The missing condition is to choose the
completions so that

```text
d_Hamm(sigma_g sigma_h,sigma_(gh)) -> 0.                (CAT3)
```

Adding multiplicity copies does not make `(CAT3)` automatic: it enlarges the
completion torsor.

This has a tree/groupoid interpretation.  On a finite forest of translated
windows, choose a basis at each root and transport it along the unique paths.
Every edge unitary is then permutation-valued.  Closing an edge creates a
cycle, and the product of the edge gauges around that cycle is precisely the
uncontrolled actor-table holonomy.  Cylinder moments constrain the vertex
measures and overlap covariance constrains the edge maps; neither compares
the two paths around a cycle.  Actor multiplicativity does compare them for
the original unitaries, but independent normalizer rounding need not preserve
that comparison.  Preserving all comparisons simultaneously is `(CAT3)`.

## Sharp finite countermodel

The independence is already exact and permutation-valued.  Fix a finite
window `F` and actor labels `g,h,gh`.  Choose arbitrary permutation
completions

```text
pi_g, pi_h, pi_(gh) in Sym(Omega_F)
```

of their respective overlap transports `(CAT2)`.  On

```text
Y=Omega_F times Z/3Z
```

define `sigma_1=1` and, for `k in {g,h,gh}`,

```text
sigma_k(omega,t)=(pi_k(omega),t+1).                     (CAT4)
```

With uniform measure, every cylinder atom has exactly the Bernoulli mass
`2^(-|F|)`.  Each `sigma_k` implements every named overlap covariance
exactly, and, because it shifts the last coordinate without fixed points,

```text
tr(p_omega P_(sigma_k))=0
```

for every atom `omega` and every nonidentity named actor.  These are the full
cylinder-resolved mixed canonical traces, not just scalar actor traces.
Nevertheless `sigma_g sigma_h` shifts the last coordinate by `2`, whereas
`sigma_(gh)` shifts it by `1`.  They disagree at every point:

```text
d_Hamm(sigma_g sigma_h,sigma_(gh))=1,
||P_(sigma_g)P_(sigma_h)-P_(sigma_(gh))||_2^2=2.        (CAT5)
```

Hence individual exact permutationization, exact cylinder laws, and exact
finite-window covariance give no bound at all on actor-table coherence.  A
normalized-HS microstate separately supplies small multiplicativity defect
for its original unitaries; the open operation is a **simultaneous** rounding
which retains that defect.  This is precisely why
`finite-cylinder-mixed-traces-kill-normalizer-holonomy` starts after a finite
group action has been extracted: its character argument kills stabilizer
holonomy inside a joint table, but cannot manufacture `(CAT3)`.

