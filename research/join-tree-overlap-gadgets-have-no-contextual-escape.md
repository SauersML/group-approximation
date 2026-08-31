---
rg: 2
id: join-tree-overlap-gadgets-have-no-contextual-escape
kind: claim
title: Join-tree overlap gadgets globalize both probability models and odd-subset characters
artifacts:
  - research/join-tree-overlap-gluing-and-robust-gap-proof.md
distinct_from:
  lcs-parity-gadgets-preserve-odd-dictator-affine-hull: that is the exact affine closure inside one long-code context; this shows that acyclic overlap consistency glues those local closures to global scalar data.
  odd-subset-relaxation-needs-local-extendability: that refutes an unrestricted cyclic multi-context argument; this supplies a correct theorem under a join tree and an explicit edgewise extendability hypothesis for the F_2 lift.
  perfect-completeness-constant-soundness-lcs-compiler: that asks for a perfect commuting versus finite-dimensional gap; this proves that its shared-auxiliary escape must create genuinely cyclic contextual incidence.
---

Let `{X_c:c in V(T)}` be finite variable contexts with allowed assignment
sets `S_c subseteq {+1,-1}^{X_c}`.  Assume `T` is a join tree: it is a
tree on the contexts, and for every variable `x` the nodes containing `x`
form a connected subtree.  Shared auxiliary variables are allowed and are
included among the `X_c`.

### Exact probability gluing

Suppose `p_c` is a probability distribution supported on `S_c` and, on
every edge `e=cd` of `T`, the two marginals on
`R_e=X_c intersect X_d` agree.  Then there is a probability distribution
`p` on global assignments whose marginal on every context is `p_c`.
Consequently:

```text
a join-tree constraint system with a perfect compatible
context model has a global scalar satisfying assignment.             (JTG1)
```

In particular, a perfect commuting-operator LCS model on a join-tree
incidence cannot be contextual: take the joint spectral distribution in
each commuting equation context and glue the identical overlap marginals.

There is a robust finite inequality.  For arbitrary context distributions
`p_c`, put

```text
eta_c = p_c(assignments outside S_c),
delta_cd = TV((res_R)_* p_c,(res_R)_* p_d).              (JTG2)
```

If there is no global assignment whose restrictions lie in every `S_c`,
then

```text
sum_c eta_c + sum_(cd in E(T)) delta_cd >= 1.            (JTG3)
```

Thus any verifier which samples every local-validity and tree-overlap check
with probability at least `w_min` has classical loss at least `w_min`.
The bound is dimension-free at the level of the observed context laws.

### Exact odd-subset gluing

Assume additionally that every edge is bi-extendable:

```text
res_R(S_c)=res_R(S_d) for every edge cd.                 (JTG4)
```

Let `t_c in F_2^{S_c}` have odd augmentation, and suppose their `F_2`
pushforwards agree on every separator.  Then there is
`t in F_2^{Sol}` on the set `Sol` of global satisfying assignments such
that every context marginal of `t` is `t_c` and `t` has odd augmentation.
Equivalently, every compatible family of local odd-subset characters is an
odd product of global dictator characters.

Therefore every parity equation, with any auxiliary LCS variables, which is
satisfied by all global honest assignments is also satisfied by every such
compatible odd-subset family.  On a join tree, overlap auxiliaries do not
repair the zero-noise long code; they merely replace the local affine hull
by the odd affine hull of global sections.

The topology is sharp.  The Mermin--Peres square has six contexts and
context-intersection graph `K_(3,3)`, so it has no join tree.  Its row and
column parity equations have no scalar solution but do have an exact
two-qubit Pauli solution.  Hence cyclic shared auxiliaries can break
atomwise scalar extendability.  This fixed gadget is not a decoder: it
already has a finite-dimensional perfect strategy, so adjoining it cannot
create a finite-versus-commuting gap.  The remaining seam is a
source-dependent cyclic coupling whose near-perfect finite-dimensional
models robustly decode the source while its perfect commuting model
survives.
