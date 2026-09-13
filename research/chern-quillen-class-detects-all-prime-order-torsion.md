---
rg: 2
id: chern-quillen-class-detects-all-prime-order-torsion
kind: claim
title: A group with a finite proper contractible complex has one mod-p class detecting every element of order p
distinct_from:
  good-groups-have-no-persistent-finite-cohomology: that says positive-degree classes on a good group die on finite-index subgroups; this constructs, on any group with a finite proper contractible complex, a class that survives on every subgroup containing an element of order p
  finite-torsion-carrier-virtual-torsionfree-criterion: that detects torsion through one finite quotient; this detects it in the discrete cohomology of the group itself, with no finite quotient involved
artifacts:
  - research/artifacts/hyperbolic-vtf-chern-quillen-persistence-2026-09-12.md
---

Let `G` act on a contractible `G`-CW complex `X` of dimension `d` with finitely many
orbits of cells, finite stabilizers fixing their cells pointwise, and every finite
subgroup fixing a point. Every word-hyperbolic group has such an `X`
(`hyperbolic-rips-complex-models-proper-actions`).

Let `M` be the lcm of the stabilizer orders, `p` a prime dividing `M`,
`M/p = p^a m` with `p` not dividing `m`, `n = 2(p-1)p^a`, `e = max(d-1,0)` and
`N = n p^e`. For a finite subgroup `F` put

```text
y_F = cbar(rho_F)^(M/|F|),
```

the mod-`p` total Chern class of the regular representation raised to `M/|F|`, and
let `y_F^(n)` be its degree-`n` part.

**Theorem.** There is `c in H^N(G;F_p)` with
`res^G_F c = (y_F^(n))^(p^e)` for every finite subgroup `F`. For every subgroup
`P = <x>` of order `p`, `res^G_P c` equals `(-m)^(p^e) β^((p-1)p^(a+e))` for `p` odd,
and `m u^(2^(a+1+e))` for `p = 2`. In particular it is nonzero.

Any such `c` is a *Chern–Quillen class of `G` at `p`*. The same holds for its powers
`c^(p^k)`.

No virtual torsion-freeness is assumed. For groups of finite virtual cohomological
dimension this detection is classical: it is proved with a representation of a finite
quotient that has torsion-free kernel, and such a quotient exists exactly when the
group is virtually torsion-free. Here the compatible local family `y_F` replaces that
global representation.

Proof: `chern-quillen-class-detects-all-prime-order-torsion-proof`. The technique is
Quillen's power-lifting (1971); no novelty is claimed for it. Unreviewed; not
Lean-verified.
