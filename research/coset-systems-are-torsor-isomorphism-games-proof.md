---
rg: 2
id: coset-systems-are-torsor-isomorphism-games-proof
kind: route
title: Fibre colours force left translations, edge colours are exactly the coset relations, and cocommutativity forces abelian fibre images
target: coset-systems-are-torsor-isomorphism-games
requires: []
---

Notation as in the target.  `v = (v_((q,x),(q',a)))` is the magic unitary of
`A(Iso(X(S_1), X(S)))`.  Its relations are
`v_(xa) v_(x'a') = 0` whenever `col_(S_1)(x,x') != col_S(a,a')`.

**(P0) Edge colours match exactly on the coset.**  Let `(q,q') in E`, write
`D = D_(qq')` and `c = c_(qq')`, and put `s = a x^(-1)`, `s' = a' x'^(-1)`.
For right cosets, `Du = Dw` iff `u w^(-1) in D`.  Hence

```text
D (x,x') = D c^(-1) (a,a')
  iff (x,x') (a,a')^(-1) c in D
  iff (s,s')^(-1) c in D
  iff (s,s') in c D.
```

**(P1) Block form.**  For `q != q'`, the diagonal pair `((q,x),(q,x))` has
colour `(in,q,e)`, while `((q',a),(q',a))` has colour `(in,q',e)`.  These
differ, so `v_((q,x),(q',a)) = v_((q,x),(q',a))^2 = 0`.  Therefore each row
`(q,x)` is a PVM supported on the fibre `{q} x K_q`.

**(P2) Left translations.**  Fix `q`, and `x, a in K_q`, and put `s = a x^(-1)`.
Write `A = v_((q,x),(q,a))` and `B = v_((q,e),(q,s))`.

- `v_((q,x),(q,a)) v_((q,e),(q,b)) != 0` needs `x^(-1) = a^(-1) b`, that is
  `b = s`.  Summing the row `(q,e)` over `b`, using (P1), gives `A = AB`.
- `v_((q,e),(q,s)) v_((q,x),(q,b)) != 0` needs `x = s^(-1) b`, that is
  `b = a`.  Summing the row `(q,x)` gives `B = BA`.
- Hence `A = A^* = (AB)^* = BA = B`.

So with `p_q^s := v_((q,e),(q,s))`, which is a PVM over `K_q` by (P1),

```text
v_((q,x),(q,a)) = p_q^(a x^(-1)).                               (LT)
```

**(P3) The map `A(S) -> A(Iso)`.**  Send `p_q^s` to `v_((q,e),(q,s))`.  These
are PVMs, and for `(q,q') in E`, (P0) with `x = x' = e` shows that
`p_q^s p_(q')^(s') = 0` unless `(s,s') in cD`.  So (CS) holds.

**(P4) The map `A(Iso) -> A(S)`.**  Put `V_((q,x),(q',a)) = delta_(qq') p_q^(a x^(-1))`.

- **Magic unitary.**  The entries are projections, and
  `sum_a p_q^(a x^(-1)) = 1 = sum_x p_q^(a x^(-1))`.
- **Relations.**  Take a product `V_(xa) V_(x'a')` with `x in` fibre `q`,
  `x' in` fibre `q'`.  It vanishes unless `a` lies in fibre `q` and `a'` in
  fibre `q'`, so assume this.
  - **Same fibre, `q = q'`.**  The product is
    `p_q^(a x^(-1)) p_q^(a' x'^(-1))`, which is nonzero only if
    `a x^(-1) = a' x'^(-1) = s`.  Then `x^(-1) x' = a^(-1) a'`, so the colours
    agree.
  - **`(q,q')` not in `E`.**  Both colours are `(free, q, q')`.
  - **`(q,q') in E`.**  The product is `p_q^s p_(q')^(s')`, which (CS) kills
    unless `(s,s') in cD`, and then by (P0) the colours agree.

So `V` satisfies every relation of `A(Iso)`.

**(P5) The two maps are inverse.**

- `p_q^s -> v_((q,e),(q,s)) -> p_q^(s e^(-1)) = p_q^s`.
- `v_((q,x),(q,a)) -> p_q^(a x^(-1)) -> v_((q,e),(q,a x^(-1))) = v_((q,x),(q,a))`
  by (LT).
- Cross-fibre entries go to `0` and are `0` by (P1).

This proves (T1).  Tracial states and `R^U`-representations correspond, by
the definitions of `≅_qc` and `≅_qa` in
`closure-safe-support-is-exactly-the-colored-iso-rung`.

**(P6) Coproduct.**  `O(Qut X(S_1))` is `A(Iso(X(S_1),X(S_1)))`, with
`Delta(u_(yw)) = sum_z u_(yz) (x) u_(zw)`, counit `delta` and antipode
`u_(yw) -> u_(wy)`.  Through (T1) with `c = 1`, using (LT) and (P1):

```text
Delta(p_q^s) = sum_(r in K_q) u_((q,e),(q,r)) (x) u_((q,r),(q,s)) = sum_r p_q^r (x) p_q^(s r^(-1)),
epsilon(p_q^s) = delta_(s,e),      S(p_q^s) = u_((q,s),(q,e)) = p_q^(s^(-1)).
```

This proves (T2).

**(P7) (T3).**

1. **Independence.**  Nonzero members of one PVM are linearly independent:
   multiply `sum_r lambda_r p^r = 0` by `p^(r_0)`.  So the nonzero
   `p^r (x) p^t` are linearly independent in `A (x) A`.
2. **`L_q` is a subgroup.**  `epsilon(p_q^e) = 1`, so `e in L_q`.  If
   `r, t in L_q`, then `Delta(p_q^(tr))` contains the nonzero independent term
   `p_q^r (x) p_q^t`.  So `Delta(p_q^(tr)) != 0`, hence `p_q^(tr) != 0`.
3. **Classical solutions lie in `L_q`.**  For `sigma in Sol_0`,
   `p_q^s -> delta_(s, sigma_q)` is a character of `A(S_1)`, since (CS) holds
   because `(sigma_q, sigma_(q')) in D`.  So `sigma_q in L_q`.
4. **Cocommutativity forces `L_q` abelian.**  Suppose
   `flip o Delta = Delta`.  Substituting `r' = s r^(-1)`,

   ```text
   sum_r p^r (x) p^(s r^(-1)) = sum_(r') p^(r') (x) p^(r'^(-1) s).
   ```

   Compare the coefficients of `p^r (x) (.)` for `r in L_q`, using step 1.
   This gives `p^(s r^(-1)) = p^(r^(-1) s)` for all `s`.  With `s = t r` and
   `t in L_q`, `p^t = p^(r^(-1) t r)`.  Both are nonzero by step 2, and
   distinct members of a PVM are orthogonal.  So `t = r^(-1) t r`, and `L_q`
   is abelian.
5. **Conclusion.**  A compact quantum group is dual to a discrete group
   exactly when its Hopf *-algebra is cocommutative.  So a nonabelian `L_q`
   excludes a group dual.

**(P8) (T4).**

- **The gap.**  By (T1), `X(S_1) ≅_qc X(S)`, and a unital *-homomorphism of
  `A(Iso)` into `R^U` would be one of `A(S)`.  The non-embeddable Haar algebra
  of `Qut Z` is the last part of
  `closure-safe-support-is-exactly-the-colored-iso-rung`, applied to this
  pair.
- **A Hopf quotient.**  `U = diag(u, 1_(X(S)))`, with `u` the fundamental
  matrix of `Qut X(S_1)`, is a magic unitary obeying the colours of `Z`:
  - inside `X(S_1)` they are the colours of `u`;
  - mixed pairs keep the cross colour;
  - the second block is the identity.

  So `u_Z -> U` defines a surjective *-homomorphism
  `O(Qut Z) -> O(Qut X(S_1))`.  It intertwines the coproducts, since the
  identity block contributes only `delta (x) delta`, and summing over
  `z in X(S)` adds `0` to the first block.
- **Not a group dual.**  A Hopf quotient of a cocommutative Hopf algebra is
  cocommutative.  So if `Qut Z` were a group dual, every `L_q` would be
  abelian by (P7).
