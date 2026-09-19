---
rg: 2
id: position-window-ucp-sections-collapse-to-folner-vectors
kind: claim
title: Any position-indexed window section of a group quotient collapses under the trivial character to an invariant Folner vector
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
distinct_from:
  explicit-finite-face-ucp-section-is-edge-equivariant: that exhibits the window shape succeeding over the finite face `P_13`; this proves it cannot succeed over an infinite quotient group, and the two are the same computation at a finite and an infinite index set.
  triangle-relator-extension-admits-local-ucp-sections: that is the open positive target; this refutes one named family of candidate constructions for it and leaves the target open, since sections need not have window shape.
  deligne-fixed-projective-representation-folner-compression-no-go: that refutes Folner compression of a fixed projective representation in the Deligne presentation; this refutes operator-coefficient window sections of a group C-star quotient and produces its Folner vector by applying the trivial character, with no projective cocycle and no fixed representation.
---

**ESTABLISHED (no-go).**  Let `Gamma ->> Lambda` be a surjection of discrete
groups with `Lambda` infinite, `q:C^*(Gamma)->>C^*(Lambda)` the induced
surjection, and `sigma:Lambda->Gamma` any set section.  Call a map `s` defined
on the group words of `C^*(Lambda)` an **orthogonal-position/window section**
if it has the form

```text
s(u_k) = sum_(g in Lambda) c_g^* m(g,k) c_(gk),
sum_(g in Lambda) c_g^* c_g = 1,                             (PW1)
```

with finitely many nonzero `c_g in C^*(Gamma)` and middle factors `m(g,k) in
C^*(Gamma)` each of which is a group word `u_(w(g,k))` -- for instance the
window word `u_(sigma(g)^(-1) sigma(gk))`.  Let `K` be a finite generating set
of `Lambda`.  Then

```text
q(s(u_k)) = u_k  for all k in K   is impossible.             (PW2)
```

Quantitatively, if `||q(s(u_k))-u_k|| <= delta` for all `k in K` and
`(Lambda,K)` has Kazhdan constant `kappa>0`, then

```text
delta >= kappa^2/2.                                          (PW3)
```

Proof: `position-window-ucp-section-folner-no-go-proof`.

**What exactly is killed.**  Positivity is never used: `(PW2)` refutes the
*shape*, whether or not `s` is ucp, and whether or not it is defined beyond the
generating words.  Nor is it a global-versus-local distinction: a *local* ucp
section only has to work on one finite-dimensional operator system, but local
splitting requires it to work on all of them, in particular on
`span{u_g : g in F^(-1)F}` for a finite `F` containing a generating set --
where `(PW2)` already applies.  Operator-valued coefficients buy nothing: the
trivial character `epsilon` of `C^*(Lambda)` (which always exists) is
multiplicative, so `c_g |-> epsilon(q(c_g))` sends the whole construction to a
scalar `l^2(Lambda)` vector and the operator degrees of freedom disappear.  The
middle factors are irrelevant for the same reason -- every group word has
character value `1` -- so no cleverness in the choice of window word helps.

Consequently the following are all excluded as routes to
`triangle-relator-extension-admits-local-ucp-sections`: random sections built
from coset representatives, `l^2`-windows, operator-valued partitions of unity
indexed by group positions, and orthogonal coset-module (Stinespring
orthogonal-position) constructions.

**What survives.**  Two things.  First, the same formula over a *finite*
quotient group: there the collapsed vector is the normalized indicator of the
finite group, which is genuinely translation invariant, which is exactly why
`explicit-finite-face-ucp-section-is-edge-equivariant` exists.  Second, any
construction whose corrections are **not** indexed by group positions with a
right-translation reindexing -- in particular corrections drawn from the
relator ideal itself, as in
`finite-relator-reservoir-repairs-every-fd-packet`.  A successful section must
use genuinely nonorthogonal, off-fibre interference; that is the positive
content of this no-go.
