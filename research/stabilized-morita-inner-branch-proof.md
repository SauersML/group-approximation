---
rg: 2
id: stabilized-morita-inner-branch-proof
kind: route
title: Multiply the two-by-two dilation and audit the prefix-frame stabilizer
target: stabilized-morita-branches-are-inner-but-incoherent
requires: []
---

Write `q_i=A-p_i`.  Since `p_i^2=p_i`, `q_i^2=q_i`,
`q_i s_i=0`, and `t_iq_i=0`, direct multiplication gives

```text
U_iV_i=
 [[s_it_i+q_i^2, q_is_i],[t_iq_i,t_is_i]]=I_2,         (SMP1)
```

and the reverse product is identical.  Moreover

```text
E_11V_i=t_iE_11,             U_iE_11=s_iE_11.          (SMP2)
```

For three-block elementary roots, conjugation by
`diag(P,Q,R)` sends

```text
X(C) |->X(PCQ^(-1)),
Y(C) |->Y(QCR^(-1)),
Z(C) |->Z(PCR^(-1)).                                  (SMP3)
```

Taking `(P,Q,R)=(I_2,U_i,I_2)` and using `(SMP2)` proves
`(SMI2)`.  Products of the `U_i` append the `t` prefixes on the right-root
coefficient and the reversed `s` prefixes on the left-root coefficient, so
their iterations reproduce the dual-prefix convention exactly.

For the coherence audit, fix a base prefix frame.  A prefix permutation
supported in its complement fixes both its column and dual row, hence its
middle-block conjugation fixes the corresponding `X` and `Y` roots.  There
are infinitely many such permutations, giving an infinite subgroup of the
root centralizer.  The general centralizer-filling theorem therefore makes
the areas of the corresponding commutator words unbounded.

Pairwise prefix transitivity does not contradict this.  Given an ordered
pair `(u,v)`, one can complete the source and target cylinders to prefix
codes and build a unit carrying a prototype pair to `(u,v)`.  If `g_u` is
the globally chosen one-frame transporter and `g_(u,v)` is this contextual
pair transporter, then

```text
h=g_(u,v)^(-1)g_u                                      (SMP4)
```

lies in the prototype-frame stabilizer.  Replacing the contextual occurrence
by the globally named one is exactly conjugation by `[h,X_base]` (and the
analogous `Y` commutator).  Uniform replacement would contradict the
unbounded-area conclusion above.

At the matrix level one could still hope for an analytic replacement of
this van Kampen step.  However applying a Kazhdan or `(TT)/T` estimate to
`h |->rho(h)Xrho(h)^(-1)-X` requires `rho` to be an exact actor
representation.  For an arbitrary presentation microstate, the failure of
`rho` to be multiplicative is the same moving-word error the construction
is intended to control.  This proves the stated residual without claiming
that analytic coherence is impossible.

Finally, let `V_n` denote the finite Weyl coefficient space of the
depth-`n` prefix packet.  The proposed full linear/symplectic Morita actor
does not satisfy the hypothesis of the gapped finite-actor localization
lemma.  If a fixed actor `K` preserved every `V_n`, then for `0 != v in V_1`

```text
K v subset V_1,                                             (SMP5)
```

so `K` could not be transitive on the nonzero vectors in
`union_n V_n`.  Conversely, an actor transitive on that union must move some
`V_n` out of itself and hence does not act by automorphisms of the finite
Pauli group whose Reynolds square function is being used.  Passing to
`Stab_K(V_n)` makes the actor depend on `n`; ambient property `(T)` gives no
uniform gap for this subgroup family.  Thus unimodularity of individual
prefix combinations and exact Fourier/shear transport prove orbit
statements, but not the finite invariant-packet plus uniform-gap statement
needed for one-word Gram localization.
