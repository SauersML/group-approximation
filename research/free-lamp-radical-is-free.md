---
rg: 2
id: free-lamp-radical-is-free
kind: claim
title: The sofic radical of the free-lamp Kun--Thom group is a free group
distinct_from:
  sofic-radical-soficization: That is the general structure theorem identifying the radical as the kernel of soficization; this computes that kernel for one explicit family and finds it free.
  literal-witness-kernel-free: That computes the kernel of the literal group onto its Clifford witness and finds it free of infinite rank; this computes the sofic radical of the Kun--Thom free-lamp amalgam, a different group and a different subgroup.
  invariant-graph-clifford-phase: That classifies the central lamp quotients keeping the marked word alive; this identifies the isomorphism type of the whole radical.
  kun-thom-clifford-radical-phase: That exhibits one word in the radical of this group together with its Clifford detector; this computes the entire radical and identifies it as a free group.
  kun-thom-clifford-cover-weakly-sofic: That is a metric approximation statement about the Clifford central quotients of this group; this is a purely algebraic identification of its sofic radical and says nothing about metrics.
  simple-sofic-total-mf-radical: That concerns the MF radical of a simple sofic group, which is everything; this concerns the sofic radical of a nonsofic amalgam, which is a proper free normal subgroup.
artifacts:
  - notes/NOTEPAD.md
---

Let `Gamma<G` be a Kun--Thom infranormal nonnormal Kazhdan pair, `K` a
nontrivial countable residually finite group, `N=<<Gamma>>_G`, and

```text
H_K = G *_Gamma (Gamma x K).
```

1. **Normal form.**  `H_K = (*_(G/Gamma) K) semidirect G`, the lamp at the
   coset `g Gamma` being `g k g^(-1)`.
2. **The radical is the collapsing kernel.**  `Rad_sof(H_K)` is the kernel of
   the natural surjection

   ```text
   *_(G/Gamma) K  ->>  *_(G/N) K
   ```

   induced by `G/Gamma -> G/N`, and `H_K/Rad_sof(H_K) = G *_N (N x K)`
   embeds in `G x ((G/N) * K)`, which is residually finite.
3. **It is free.**  That kernel meets every conjugate of every free factor
   trivially, so it acts freely on the Bass--Serre tree of the free product
   and is therefore a free group.

Consequently `H_K` is **(free)-by-(residually finite) and not sofic**: an
extension with a free kernel and a residually finite quotient, whose whole
failure of soficity is carried by the action of `G` on that free kernel, not
by any pathology of the kernel itself.  The nonsoficity is immediate from
`sofic-radical-soficization` once the radical is nontrivial, which holds
exactly when `Gamma` is not normal.
