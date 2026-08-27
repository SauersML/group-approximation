---
rg: 2
id: explicit-finite-face-ucp-section-is-edge-equivariant
kind: claim
title: Finite group quotients have explicit averaged ucp sections, relatively exact on one lifted subgroup
artifacts:
  - research/artifacts/finite-relator-reservoir-compactness-2026-08-23.md
distinct_from:
  triangle-relator-extension-admits-local-ucp-sections: that asks for ucp lifts of every finite-dimensional operator system of the whole colimit algebra; this supplies one in closed form for the single finite face `C^*(P_13)` and proves nothing about any operator system meeting the rest of the group.
  triangle-colimit-llp-reduces-to-relator-local-splitting: that is the equivalence identifying LLP of the colimit with local splitting; this constructs one explicit section of that extension over a finite subalgebra and is a fragment of the positive side, not a reformulation of it.
  position-window-ucp-sections-collapse-to-folner-vectors: that proves the same averaging shape cannot be run over the infinite colimit; this exhibits it working on the finite face, and the two are the same computation read at a finite and an infinite index set.
  kernel-relator-forces-two-edge-ucp-section-gap: that proves no section of the triangle's finite face quotient can be arbitrarily close to the canonical lifts on both generating edges; this constructs a section exactly on either one edge.
---

**ESTABLISHED.**  Let `p:H->>F` be any surjective homomorphism with `F`
finite.  Let `p_*:C^*(H)->>C^*(F)` be the induced full group C-star quotient,
and choose any set section `sigma:F->H` with `sigma(1)=1`.  Define

```text
Theta_sigma(u_g) := |F|^(-1) sum_(x in F)
                    u_(sigma(x))^* u_(sigma(xg)),
                                     g in F.                 (FF1)
```

Then

```text
(a) Theta_sigma extends to a ucp map C^*(F) -> C^*(H);
(b) p_* o Theta_sigma = id_(C^*(F));                          (FF2)
(c) if L<=F has a subgroup lift L_tilde<=H on which p is an
    isomorphism, sigma may be chosen right-L-equivariantly, and then
    Theta_sigma is a right C^*(L)-module map (using the lifted copy in
    the range); in particular Theta_sigma(u_l)=u_(l_tilde).
```

The relative section exists by choosing one representative of every right
`L`-coset and propagating through the lifted subgroup.

Proof: `explicit-finite-face-ucp-section-proof`.

**Triangle specialization.**  In the setting of
`triangle-colimit-llp-reduces-to-relator-local-splitting`, take

```text
H=E=P_1 *_(P_0) P_3,       F=P_13,       p=q_E.
```

Both `P_1` and `P_3` are subgroup lifts.  Hence the section can be chosen to
fix `P_1` exactly, or instead to fix `P_3` exactly.  These choices cannot in
general be combined: `kernel-relator-forces-two-edge-ucp-section-gap` gives a
quantitative obstruction detected by every nontrivial `n in ker q_E`.

**Scope, stated honestly.**  Existence of *some* ucp section over `C^*(F)` is
not new and is not the point: `C^*(F)` is finite-dimensional, hence nuclear,
so Choi--Effros already lifts every ucp map out of it.  The content is that the
section is written in closed form for every finite group quotient, that its
positivity proof
is a single Hilbert-module matrix coefficient rather than an abstract lifting
theorem, and that `(c)` makes it **exact on one edge**: all of the
incompatibility with the ambient algebra is pushed onto the `P_3` side.  This
is the precise form of the "one-edge defect" idea, and it is the natural base
case for any inductive attack on
`triangle-relator-extension-admits-local-ucp-sections`.  The kernel-relator
gap shows this base case is intrinsically one-sided, not merely presented that
way for convenience.

**Why it does not globalize, and why that is consistent.**  `(FF1)` is exactly
an orthogonal-position/window section in the sense of
`position-window-ucp-sections-collapse-to-folner-vectors`, with position index
running over `P` and constant coefficients `|P|^(-1/2)`.  That no-go forces the
associated scalar vector to be right-translation invariant; over the finite `P`
the normalized indicator of `P` *is* invariant, which is why `(FF1)` exists,
and over the infinite `Lambda` no nonzero finitely supported vector is, which is
why the same formula cannot be run there.  The two nodes are one computation at
two index sets, and the boundary between them is finiteness of the face.
