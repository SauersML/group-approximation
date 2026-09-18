---
rg: 2
id: sl-n-q-lies-in-one-factor-of-every-normal-series
kind: claim
title: In every normal series of a group containing SL_n(Q), a single factor carries a perfect image of SL_n(Q) with all its root groups
distinct_from:
  extension-product-closures-cannot-create-sl-n-q: that shows the class of groups receiving only trivial maps from SL_n(Q) contains every abelian and every Q-free group and is closed under extensions, which already implies the "no layered host" consequence below; this localizes SL_n(Q) in one factor of an arbitrary normal series of an arbitrary overgroup, with a self-contained proof.
  lifts-add-no-unipotent-divisibility: that fixes the three-term shape Q-free, central, Q-free, and also covers the solvable groups Aff(Q), B_2(Q) and U_3(Q); this allows any finite normal series whose factors are abelian or Q-free, including abelian kernels that contain Q, but only for the quasi-simple type SL_n(Q)/C.
  gl-n-q-embeds-in-fp-simple-group: that is the open embedding problem; this constrains the shape of every host.
  gl-n-q-embeddings-detected-by-nontrivial-homomorphisms: that says a homomorphism from these inputs is injective once one named element survives; this uses the same root-element normality to force SL_n(Q) into a single factor of any normal series of any overgroup.
artifacts:
  - research/artifacts/gq-bhm-pattern-union-and-scope.md
---

**ESTABLISHED** through `sl-n-q-lies-in-one-factor-of-every-normal-series-proof`.
Not independently reviewed. The argument is elementary and self-contained, and no
priority is claimed. Write *Q-free* for "contains no subgroup isomorphic to
`(Q,+)`".

## Statement

Let `n >= 2`, let `C` be a central subgroup of `SL_n(Q)` (so `C <= {±I}`), and let
`H` be a group identified with `SL_n(Q)/C`. For `i ≠ j` let `X_ij <= H` be the
image of the root group `{I + qE_ij : q in Q}`. It meets `C` trivially, so
`X_ij ~ (Q,+)`.

Let `H <= E`, and let `1 = S_0 <= S_1 <= ... <= S_k = E` be subgroups that are all
normal in `E`. Let `t` be the least index with `H <= S_t`. Then:

1. every `X_ij` meets `S_(t-1)` trivially, so `X_ij` embeds in `S_t/S_(t-1)`;
2. the image of `H` in `S_t/S_(t-1)` is a nontrivial perfect group.

So the factor `S_t/S_(t-1)` is nonabelian and contains `(Q,+)`.

## Consequences

The first consequence also follows from the earlier
`extension-product-closures-cannot-create-sl-n-q`: its class contains the abelian
and the Q-free groups and is closed under extensions. The new content here is the
localization in items 1 and 2, and a proof that cites no simplicity theorem.

- **No layered host.** Suppose some finite series of normal subgroups of `E` has
  every factor abelian or Q-free. Then `E` contains none of `GL_n(Q)`, `SL_n(Q)`,
  `PGL_n(Q)`, `PSL_n(Q)` for any `n >= 2`. Each of them contains a copy of some
  `SL_n(Q)/C`: `SL_n(Q) <= GL_n(Q)`, and `PSL_n(Q)` is the image of `SL_n(Q)` in
  `PGL_n(Q)`.
- **Cases covered:**
  - solvable-by-(Q-free) groups: refine the solvable normal subgroup by its
    derived series, whose terms are characteristic and hence normal in `E`;
  - central lifts and covering lifts of Q-free groups with any abelian deck group.
    This includes deck groups that contain `Q`, such as the adelic solenoid
    `(R x A_f)/Q`, the case that `lifts-add-no-unipotent-divisibility` leaves
    open;
  - iterated extensions by modules of a Q-free group;
  - any mixture of these. The three-term shape of
    `lifts-add-no-unipotent-divisibility` (Q-free, central, Q-free) is one
    instance.
- **Contrast with `(Q,+)`.** `Q` is `Z`-by-`(Q/Z)`, and both factors are Q-free.
  Belk--Hyde--Matucci's `Q <= T-bar` (arXiv:2005.02036) splits the divisibility
  this way, into the centre `<z> ~ Z` of `T-bar` and `Q/Z <= T <= V`. The statement
  says `SL_n(Q)` admits no split of any length: its divisibility must be carried
  whole by a single nonabelian factor that already contains `(Q,+)`.
- **Not covered.** The solvable targets `Aff(Q)`, `B_2(Q)` and `U_3(Q)` are
  themselves poly-abelian, so a normal series cannot exclude them. For the lift
  shapes, see `lifts-add-no-unipotent-divisibility`.
