---
rg: 2
id: stw07-local-qd-subalgebras-proof
kind: route
title: Extend a local matrix approximation and retain multiplicativity and norm recovery
target: stw07-local-qd-subalgebras-force-quasidiagonality
requires: []
artifacts:
  - research/artifacts/stw07-status-and-stable-character-reduction-2026-08-30.md
---

Use Voiculescu's finite-set characterization.  Fix a finite set `F` in the
unit ball of `A` and `eta>0`.  Choose `delta>0` much smaller than `eta` and a
local algebra `B` satisfying `(LQ1)` for `F`.  After taking self-adjoint or
contractive replacements as needed, choose contractions `b_x in B` with
`||x-b_x||<delta` for `x in F`.

Quasidiagonality of `B` gives a u.c.p. map `phi:B -> M_k` such that, for
`x,y in F`,

```text
||phi(b_x b_y)-phi(b_x)phi(b_y)||<delta,
||phi(b_x)||>||b_x||-delta.                              (LQ2)
```

Arveson's extension theorem extends `phi` to a u.c.p. map
`Phi:A -> M_k`.  Contractivity and `(LQ2)` give

```text
||Phi(xy)-Phi(x)Phi(y)||
 <= ||xy-b_x b_y||
    +||phi(b_x b_y)-phi(b_x)phi(b_y)||
    +||phi(b_x)phi(b_y)-Phi(x)Phi(y)||
 < 5 delta,                                               (LQ3)
```

where the first and last terms use `||x||,||y||,||b_x||,||b_y||<=1`.
Likewise

```text
||Phi(x)|| >= ||phi(b_x)||-delta
             > ||x||-3 delta.                            (LQ4)
```

Choose `delta` so that the right sides meet `eta`.  These u.c.p. maps are
approximately multiplicative and approximately isometric on arbitrary
finite sets, hence `A` is quasidiagonal.

For the directed-limit consequence, the canonical images form a directed
family of quasidiagonal subalgebras with dense union because the connecting
maps are injective.  Apply the theorem.  Injectivity is essential to this
argument: for a noninjective system a canonical image is a quotient of a
stage, and quasidiagonality does not generally pass to quotients.
