---
rg: 2
id: sl2-laurent-f2-degree-one-amalgam-is-virtually-coxeter
kind: claim
title: The degree-one truncated amalgam approximating SL_2(F_2[t,1/t]) is a Coxeter group by S_3, and its vertex group is separable
distinct_from:
  sl2-laurent-f2-amalgam-approximants-separate-the-vertex: that asks separability for every truncation degree n; this proves the first nontrivial case n=1, m=2 by an explicit Coxeter structure
  finite-bi-index-kazhdan-stabilizer-is-nonseparable: that shows Kazhdan stabilizers are nonseparable in their hosts; this exhibits an approximant of a co-dense (hence nonseparable) vertex pair in which the vertex group is separable
---

**ESTABLISHED** (complete proof in the route; unreviewed).  Notation of
`sl2-laurent-f2-amalgam-approximants-separate-the-vertex`, with involutions

```text
a = u_1,  b = w,  c = u_t,  c' = u_(t^2),  y = b c b = v'_t,  f = u_(1/t).
```

1. **Presentation.**
   `Delta_(1,2) = < a,b,c,c',f | a^2, b^2, (ab)^3, c^2, c'^2, f^2,
   [a,c], [a,c'], [c,c'], [f,a], [f,c], (bcbf)^3 >`,
   with `C1,2 = <a,b,c,c'>`.  All generators map to the named matrices in
   `SL_2(F_2[t,1/t])`, and the relators hold there.

2. **Virtually Coxeter.**  The map `a -> (12)`, `b -> (23)`,
   `c,c',f -> 1` onto `S_3` splits, and its kernel `W` is the Coxeter group
   on nine involutions `c_p, c'_p, f_p` (`p = 1,2,3`) with

   ```text
   m(c_p,c'_p) = 2,   m(c_p,f_p) = 2,   m(c_p,f_q) = 3  (p != q),   all other m = infinity.
   ```

   So `Delta_(1,2) = W ⋊ S_3`, and `C1,2 = W_T ⋊ S_3` for the standard
   parabolic `W_T = <c_p, c'_p>`.

3. **Separability.**  `W_T` is the stabilizer of an integral point of the
   closed fundamental chamber for the contragredient Tits representation,
   which is integral.  Congruences modulo primes separate it.  Hence `C1,2`
   is closed in the profinite topology of `Delta_(1,2)`.

## Reading

- The splitting is the degenerate specialization `t -> 0`, `1/t -> 0` on
  root groups.  It exists only because at degree one no relation ties
  `u_t` to `u_(1/t)` beyond `(bcbf)^3 = 1`.
- At `n >= 2` the rotation relator `b u_(t^2) b = w' a w'`, with
  `w' = y f y`, is present (it is `s u_(t^2) s^(-1) = u_1`).  Any homomorphism
  to `S_3` with `a -> (12)`, `b -> (23)` must then send `u_(t^k)` (`k <= n`)
  and `f` to `(12)`, which is evaluation at `t = 1` on every identified root
  group.  The kernel presentation acquires the six-term relator coming from
  `(yf)^3`, and no Coxeter kernel appears.  This is where the open claim now
  lives.
- Extending item 3 to `Delta_(1,m)`, `m >= 3`, adjoins the finite groups
  `V_m` and `theta(V_m)` along `V_2` and `theta(V_2)`.  A normal-form
  argument over those finite subgroups should carry separability along.
  It is not written out and not claimed here.

DERIVATION
sl2-laurent-f2-degree-one-amalgam-is-virtually-coxeter-proof
