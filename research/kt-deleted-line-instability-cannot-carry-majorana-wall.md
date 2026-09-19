---
rg: 2
id: kt-deleted-line-instability-cannot-carry-majorana-wall
kind: claim
title: The canonical deleted-line Kazhdan instability witnesses cannot carry the Kun--Thom Majorana wall
distinct_from:
  kt-full-actor-extension-is-locally-hs-unstable: that proves bad full-actor microstates exist but gives them no separated lamp; this tests the explicit Becker--Lubotzky/Fournier-Facio--Gerasimova--Spaas codimension-one witnesses and proves their one-dimensional flexible correction makes the Majorana return collapse.
  kt-majorana-wall-certifies-macroscopic-actor-instability: that says any full wall is far from exact actors under every bounded amplification; this applies the contrapositive to the standard instability construction, whose exactification uses only one added dimension.
---

Let `sigma_n:G->U(k_n)` be genuine finite-dimensional representations of the
full `q=2`, `r=d=3` Kun--Thom actor, with `k_n->infinity`.  Apply the
Becker--Lubotzky deleted-line construction to obtain asymptotic
representations

```text
tau_n:G->U(k_n-1)                                        (DLI1)
```

and codimension-one inclusions `iota_n:C^(k_n-1)->C^k_n` which almost
intertwine `tau_n` and `sigma_n` on every fixed actor window.  Let `c_n` be
any self-adjoint involution in `M_(k_n-1)`, put

```text
delta_n=max_(s in K)||[c_n,tau_n(s)]||_2,
d_n=tau_n(h)c_n tau_n(h)^*,
a_n=||c_n d_n+d_n c_n||_2.                              (DLI2)
```

Then

```text
delta_n->0       implies       liminf a_n>=2.            (DLI3)
```

Since always `a_n<=2`, the conclusion is actually `a_n->2`: the returned
Majorana becomes asymptotically equal to the original one, not
anticommuting.  Quantitatively, if `epsilon_n` is the `K union {h}` distance
between a block-unitary one-dimensional padding of `tau_n` and `sigma_n`,
then, with `q_n=(k_n-1)/k_n` and `C_K=8/kappa_K+4`,

```text
a_n >= q_n^(-1/2)[2-(4/kappa_K)sqrt(q_n)delta_n
                     -C_K epsilon_n-2/sqrt(k_n)],        (DLI4)
```

and `epsilon_n->0` by the deleted-line intertwining estimate.

Thus the standard local-HS-instability mechanism for infinite hyperlinear
Kazhdan groups does **not** produce the correlated full-actor countermodel
needed here.  A genuine Majorana wall must lie in a different, macroscopic
unstable sector: one which cannot be repaired by restoring the deleted line,
or by any other bounded amplification.

DERIVATION
kt-deleted-line-majorana-collapse-proof
