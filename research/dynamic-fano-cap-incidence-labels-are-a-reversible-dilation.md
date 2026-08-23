---
rg: 2
id: dynamic-fano-cap-incidence-labels-are-a-reversible-dilation
kind: claim
title: Dynamic maximal-cap labels are a reversible dilation, not a Fano-profile selector
distinct_from:
  rstar-cap-support-is-one-character-row: that identifies cap support with one scalar character row in the original context; this shows why allowing the row label to be a local quantum output loses exactly that scalar conclusion.
  tracial-cap-menus-are-central-core-partitions: that classifies tracial decompositions of one supplied model into deterministic cap profiles; this constructs the always-available nondeterministic incidence refinement and proves it has no semantic strength.
  fano-maximal-cap-overlap-has-positive-sequential-mass: that selects a profile with positive sequential overlap among noncommuting cap projections; this treats a commuting local label register separately at every context and shows why local cap conditioning is insufficient.
---

**ESTABLISHED REVERSIBLE-DILATION FIREWALL.**  Put

```text
V=F_2^3,
T=V\{0},
L=V^*\{0},
I={(t,lambda) in T times L:lambda(t)=1}.              (DFI1)
```

Every `t in T` is incident with exactly four `lambda in L`, while the fiber

```text
C_lambda={t:lambda(t)=1}                              (DFI2)
```

is one of the seven maximal Fano caps.  Consider the operation which refines
one `R_*` context output `t` to an incidence output `(t,lambda) in I`, and in
every inter-context constraint forgets `lambda` and checks only the old
output `t`.

This refinement is exactly reversible at the level of perfect tracial,
Connes-embeddable, and finite-dimensional models:

```text
old model exists  iff  incidence-refined model exists.             (DFI3)
```

Moreover every old model has a trace-preserving incidence refinement after
tensoring by a four-point classical ancilla at that context.  Thus the fact
that the refined output is always contained in a selected maximal cap gives
no restriction whatsoever on the old seven-point support.

## Explicit lift

Let `(p_(c,t))_(t in T)` be the context PVM of an arbitrary perfect model in
a finite tracial von Neumann algebra `(M,tau)`.  For each `t`, choose a
bijection

```text
j_t:{lambda in L:lambda(t)=1}->{1,2,3,4}.              (DFI4)
```

Let `D_c=C^4` have minimal projections `e_(c,1),...,e_(c,4)`, use an
independent copy for every refined context, and put

```text
N=M tensor-bar (tensor_c D_c).                          (DFI5)
```

At context `c` define

```text
q_(c,t,lambda)
 =p_(c,t) tensor e_(c,j_t(lambda)) tensor 1_(other ancillas)
                                      if lambda(t)=1,  (DFI6)
```

and zero otherwise.  Orthogonality of the old atoms and of the four
ancilla atoms shows that `(q_(c,t,lambda))_((t,lambda) in I)` is a PVM.  Its
old marginal is exactly

```text
sum_(lambda:lambda(t)=1) q_(c,t,lambda)
 =p_(c,t) tensor 1.                                    (DFI7)
```

Consequently every old constraint, consistency row, and correlation is
unchanged after the label is forgotten.  Product trace makes the inclusion
`M -> N` trace preserving.  This proves the forward implication in `(DFI3)`
simultaneously for arbitrary finite tracial models, CE models, and matrix
models.  The reverse implication follows simply by taking the marginals in
`(DFI7)`.

For each local label put

```text
z_(c,lambda)=sum_(t:lambda(t)=1)q_(c,t,lambda).         (DFI8)
```

Conditioned on this local projection, the visible output lies in the maximal
cap `C_lambda`.  But the seven projections in `(DFI8)` are merely a local
PVM.  In general they are neither central nor shared between contexts, and
no one of them equals the identity.  Requiring, for a fixed profile
`alpha=(lambda_c)_c`,

```text
z_(c,lambda_c)=1             for every c               (DFI9)
```

is exactly the deterministic character-row quotient of
`rstar-cap-support-is-one-character-row`; it is not a consequence of the
incidence dilation.

## Universal form

The same argument applies to any family of local support sets `(K_l)_l`
covering a finite relation `R`: if every `t in R` belongs to at least one
`K_l`, then an auxiliary output `l` constrained only by `t in K_l` can
always be added after a finite classical dilation.  If the fiber sizes are
not constant, split each old atom using a classical ancilla of common size
and repeat labels, or use the finite direct-sum refinement.  Hence a local
support-cover label has semantic force only when some additional relation
turns it into a deterministic/shared selector.

## Consequence for the FC gate

The seven maximal caps do give an exact local cover, and a quantum model can
always announce a cap containing the assignment it actually produced.  This
does **not** choose one parity identity per context in advance.  Therefore a
compiler cannot replace FC-char by the apparently weaker statement

```text
each context has an auxiliary cap label containing its local output.      (DFI10)
```

Statement `(DFI10)` is satisfied by every model, including a full-support
factor model and every matrix countermodel.  To feed the `7^m` finite LCS OR,
the compiler must still force `(DFI9)`, find a different perfect trace which
already satisfies it, or introduce genuinely global relations coupling the
local labels.  The last option is not a local Fano selection theorem: its
soundness and perfect completeness are the unresolved global compiler.
