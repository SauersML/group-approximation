---
rg: 2
id: regular-character-mf-trace-implies-group-mf-proof
kind: route
title: Unit corner, polar correction, and trace separation
target: regular-character-mf-trace-implies-group-mf
requires: [countable-group-mf-conventions]
---

## Why sufficient

Write `v_n(g) = phi_n(u_g)` for `g in G`, all estimates being in operator
norm and all limits as `n -> infinity` with `g,h` fixed.

**1. The unit corner.**  Approximate multiplicativity and `1^*=1=1.1` give
`||phi_n(1)^2-phi_n(1)|| -> 0` and `||phi_n(1)-phi_n(1)^*|| -> 0`, while
`sup_n||phi_n(1)|| < infinity` by hypothesis.  So the self-adjoint part
`h_n = (phi_n(1)+phi_n(1)^*)/2` satisfies `||h_n^2-h_n|| -> 0` with bounded
norm; its spectrum is therefore contained in shrinking neighbourhoods of
`{0,1}`, and `p_n = 1_([1/2,infinity))(h_n)` is a projection with
`||p_n-phi_n(1)|| -> 0`.  Since traces are `1`-Lipschitz for the operator
norm and `tr(phi_n(1)) -> tau(1) = 1`,

```text
tr(p_n) -> 1,   in particular p_n != 0 eventually.               (R1)
```

**2. Everything lives in the corner.**  Multiplicativity at the pairs
`(1,u_g)` and `(u_g,1)` gives `phi_n(1)v_n(g) - v_n(g) -> 0` and
`v_n(g)phi_n(1) - v_n(g) -> 0`, so with `w_n(g) = p_n v_n(g) p_n`,

```text
||w_n(g)-v_n(g)|| -> 0.                                          (R2)
```

**3. Near unitarity.**  From `||phi_n(u_g^*)-v_n(g)^*|| -> 0` and
multiplicativity at `(u_g^*,u_g)`,
`v_n(g)^*v_n(g) - phi_n(1) -> 0`; with `(R2)` and `||p_n-phi_n(1)|| -> 0`,

```text
||w_n(g)^*w_n(g)-p_n|| -> 0,   ||w_n(g)w_n(g)^*-p_n|| -> 0.      (R3)
```

For large `n` the element `w_n(g)` is therefore invertible in the corner
`p_n M_(k_n) p_n`, and its polar part `V_n(g)` is a unitary of that corner
with `||V_n(g)-w_n(g)|| -> 0`.

**4. Multiplicativity of the corrected unitaries.**  Combining `(R2)`,
`(R3)` and multiplicativity at `(u_g,u_h)`,

```text
||V_n(g)V_n(h)-V_n(gh)|| -> 0   (g,h in G).                      (R4)
```

**5. Separation.**  Let `tr_(r_n)` be the normalized trace of the corner,
`r_n = rank(p_n)`.  By `(R1)`, `(R2)` and Lipschitz continuity of `tr`,

```text
tr_(r_n)(V_n(g)) = tr(v_n(g))/tr(p_n) + o(1) -> tau(u_g),
```

which is `0` for `g != 1`.  Hence for `g != h` in any finite set,
`||V_n(g)-V_n(h)||_op >= ||V_n(g)-V_n(h)||_(2,r_n) -> sqrt 2 > 1`, using
`(R4)` to replace `V_n(g)^*V_n(h)` by `V_n(g^(-1)h)` up to a null sequence.

**6. Conclusion.**  `(R4)` and step 5 say that for every finite `F` and every
`epsilon > 0` some `V_n` is an operator-norm local model of `G` with defect
`epsilon` and separation constant `1`.  By `countable-group-mf-conventions`
that is exactly operator MF.  End proof.

## Remark

Only the trace clause is doing work beyond the weak MF definition, and it
does it twice: at `1`, to make the corner macroscopic, and at `g != 1`, to
make separation automatic rather than assumed.
