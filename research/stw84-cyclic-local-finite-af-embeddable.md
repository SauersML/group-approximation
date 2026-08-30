---
rg: 2
id: stw84-cyclic-local-finite-af-embeddable
kind: claim
title: Cyclic locally finite extensions are AF-embeddable and reduce to their augmentation ideals
distinct_from:
  stw84-locally-finite-by-abelian-reduces-to-twisted-af-lattices: that theorem isolates arbitrary locally-finite-by-cyclic groups as the first positive-rank nuclear-dimension hinge; the present theorem proves AF-embeddability for the entire hinge and removes its unavoidable scalar fixed quotient.
  stw84-kernel-finite-locally-finite-by-abelian-computation: that theorem computes nuclear dimension under an invariant finite-subgroup exhaustion; here no such exhaustion is assumed and only AF-embeddability plus an exact ideal reduction is concluded.
artifacts:
  - research/artifacts/stw84-cyclic-group-af-action-2026-08-30.md
---

Let `K` be a countable locally finite group and let `alpha in Aut(K)`.  Put

```text
G=K rtimes_alpha Z,       B=C*(K),
I_K=ker(epsilon:B->C),
```

where `epsilon(lambda_k)=1` is the augmentation character.  Then:

1. `C*(G)=B rtimes_alpha Z` is AF-embeddable, and hence quasidiagonal.
2. There is a canonical exact sequence

   ```text
   0 -> I_K rtimes_alpha Z
     -> C*(G)
     -> C(T)
     -> 0.                                               (CAF1)
   ```

3. Consequently, if

   ```text
   dim_nuc(I_K rtimes_alpha Z)<=d,
   ```

   then

   ```text
   dim_nuc(C*(G))<=d+2.                                 (CAF2)
   ```

Thus the unrestricted cyclic nuclear-dimension problem is reduced to the
nonunital augmentation-ideal action; the scalar quotient costs at most two
in the extension estimate.

There is also a universal firewall against the most direct proposed route:
the ordinary Rokhlin dimension of the unital action

```text
alpha:Z curvearrowright C*(K)
```

is infinite for every `K` and `alpha`.  Indeed, augmentation is an
equivariant quotient onto the trivial action on `C`, finite Rokhlin dimension
passes to quotients, and the trivial integer action on `C` has infinite
Rokhlin dimension.  Hence any Rokhlin-tower proof must first pass to
`I_K`, use a relative notion invisible to augmentation, or separate the
scalar fiber as in `(CAF1)`.

For the stress test

```text
K=Alt_fin(Z),       alpha=shift,
```

the induced automorphism of `C*(K)` is approximately inner.  Nevertheless,
`K` has no exhaustion by finite `alpha`-invariant subgroups: the orbit of one
adjacent three-cycle generates all of `K`.  Thus approximate innerness at the
AF-algebra level does not recover the kernel-finite mechanism.  In
particular, this example is AF-embeddable by the theorem above but remains a
genuine test for finite nuclear dimension of the augmentation ideal crossed
product.
