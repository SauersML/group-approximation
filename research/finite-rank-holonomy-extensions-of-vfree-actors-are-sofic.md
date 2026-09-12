---
rg: 2
id: finite-rank-holonomy-extensions-of-vfree-actors-are-sofic
kind: claim
title: Finite-rank holonomy extensions of virtually free actors are sofic
distinct_from:
  abelian-by-virtually-free-groups-are-sofic: that treats arbitrary semidirect products with abelian kernel; this allows a nonabelian holonomy kernel and proves its amenability from the regular finite-rank realization.
  free-actor-extensions-cannot-host-nonce-relation: that concerns transformation crossed products by the free actor itself; this rules out enlarging that actor by any homogeneous finite-rank phase or permutation extension.
  finite-permutation-cocycles-cannot-cancel-infinite-isotropy: that blocks cancellation by a cocycle with fixed finite permutation target; this allows arbitrary matrix-valued base functions and instead uses the global extension grading.
---

Let `Q` be a countable virtually free group acting pmp on `(X,mu)`, with
orbit relation `R_Q`. Suppose

```text
1 -> K -> Gamma --p--> Q -> 1                            (VFH1)
```

is a group extension admitting a regular-trace homogeneous finite-rank
realization

```text
rho(g)=b_g(u_(p(g)) tensor 1_n) in M_n(L(R_Q)),
rho(gh)=rho(g)rho(h),
(tr_n tensor tau_R)(rho(g))=1_(g=e).                    (VFH2)
```

Then `K` is amenable and `Gamma` is sofic. Consequently no finite-rank
phase, permutation, or finite-central holonomy extension over the native
Manzoor virtually-free actor can be nonhyperlinear or retain a non-CE
relation algebra through `(VFH2)`.

The conclusion allows `K` to be infinitely generated and nonabelian. What
is load-bearing is that kernel elements occupy only the amenable
matrix-valued base and that the quotient is virtually free. A surviving
isotropy construction must abandon this global homogeneous-extension form,
use a non-virtually-free quotient, or use a nonamenable coefficient algebra;
merely adjoining more finite-rank holonomy above the native grades cannot
work.
