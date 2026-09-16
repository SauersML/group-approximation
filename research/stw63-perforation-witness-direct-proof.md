---
rg: 2
id: stw63-perforation-witness-direct-proof
kind: route
title: Bridge soft Jiang--Su classes through integer unit multiples, then take suprema
target: stw63-distinct-z-cu-maps-need-perforation-witness
requires: []
---

## Imported structure of Cu(Z)

Robert, *Classification of inductive limits of 1-dimensional NCCW complexes*,
arXiv:1007.1964v3, published in Adv. Math. 231 (2012). The text was checked
by extraction on 2026-09-16.

- **Section 6.1.** The order on `K_0(A) disjointUnion LAff~_+(T_0(A))`
  restricts to the natural orders on the two pieces. Mixed sums are
  `([p]-[q])+lambda = [p]^-[q]^+lambda`, which is soft. The mixed order is
  `lambda <= [p]-[q]` iff `lambda <= [p]^-[q]^`, and `[p]-[q] <= lambda` iff
  `[p]^-[q]^ < lambda`.
- **Proof of Proposition 6.1.1.** It records the ordered-semigroup
  isomorphism `Cu(A) -> V(A) disjointUnion LAff_+(T_0(A))`. This applies to
  a simple inductive limit of 1-dimensional NCCW complexes having a nonzero
  projection in `A tensor K`.
- **Section 6.3.** It specializes this to `Cu(Z) = N disjointUnion [0,infinity]`.

The Jiang--Su algebra is unital with a unique tracial state. So `T_0(Z)` is
the ray of multiples of that trace. By Robert's definition, `LAff_+`
consists of suprema of increasing sequences of linear functions that are
strictly positive off the zero trace. The soft summand is therefore
`(0,infinity]`, which is the description already used in
`stw63-strict-comparison-cu-collapse-proof`. Concretely:

```text
(Z1) Cu(Z) = { e_n : n in N } disjointUnion { sigma_t : 0<t<=infinity },  e_0 = 0;
(Z2) e_n+e_m = e_(n+m),  sigma_t+sigma_s = sigma_(t+s),  e_n+sigma_t = sigma_(n+t);
(Z3) e_n<=e_m iff n<=m;  sigma_t<=sigma_s iff t<=s;
     sigma_t<=e_n iff t<=n;  e_n<=sigma_s iff n<s.
```

The same relations, including the strict mixed order, are stated
independently in Antoine--Perera--Thiel, arXiv:1410.0483v3, Paragraph 7.3.2
(re-checked against the arXiv TeX source by the referee on 2026-09-16):
`Z = N disjointUnion (0,infinity]`, `n+a = n'+a`, `n <= a` iff `n' < a`, and
`a <= n` iff `a <= n'`, where `n'` is the soft element with the same number.

Antoine--Perera--Thiel, arXiv:1410.0483v3, Paragraph 3.2.5 (checked by
extraction on 2026-09-16), shows that a *-homomorphism `phi` induces a
Cu-morphism `Cu(phi)`. We only use additivity, order preservation, `0 -> 0`
and preservation of suprema of increasing sequences.

## Step 0: suprema of soft classes

Let `0<t<=infinity`, and let `r_k<t` increase to `t`. Then
`sigma_t = sup_k sigma_(r_k)` in `Cu(Z)`.

By (Z3), `sigma_t` is an upper bound. Let `z` be any upper bound.

- If `z=sigma_s`, then `r_k<=s` for all `k`. So `t<=s` and `sigma_t<=z`.
- If `z=e_n`, then `r_k<=n` for all `k`. This forces `t` to be finite with
  `t<=n`, so `sigma_t<=z`.

Hence `sigma_t` is the least upper bound. A generalized Cu-morphism preserves
it.

## Step 1: integer bridge

Put `u=f(e_1)=f'(e_1)`. By additivity, `f(e_n)=nu=f'(e_n)` for all `n`.
Suppose `0<t<=n<s<=infinity` with `n` an integer. Then (Z3) gives
`sigma_t <= e_n <= sigma_s`. Applying the order-preserving maps gives

```text
f(sigma_t) <= nu <= f'(sigma_s),                              (1)
```

and symmetrically `f'(sigma_t) <= nu <= f(sigma_s)`.

## Step 2: eventual domination (part 1)

Let `0<t<s<infinity` and `m>=(1+t)/(s-t)`. Then `ms-(m+1)t = m(s-t)-t >= 1`.
Put `n = ceiling((m+1)t)`, which is at least `1`. Then

```text
(m+1)t <= n < (m+1)t+1 <= ms.
```

Additivity and (Z2) give `(m+1)f(sigma_t) = f(sigma_((m+1)t))` and
`m f'(sigma_s) = f'(sigma_(ms))`. Now (1) proves part 1. The second
inequality follows by interchanging `f` and `f'`.

## Step 3: localization (part 2)

**If.** Suppose `f=f'`. For `t<s`, `f(sigma_t) <= f(sigma_s) = f'(sigma_s)`,
and likewise with the roles interchanged. So no witness exists.

**Only if.** Suppose `f(sigma_a) <= f'(sigma_b)` and
`f'(sigma_a) <= f(sigma_b)` for all rationals `0<a<b<=1`. We show `f=f'`.

*Real parameters.* Let `0<t<s<infinity`.

- **An integer lies in `[t,s)`.** Then (1) gives `f(sigma_t) <= f'(sigma_s)`.
- **No integer lies in `[t,s)`.** Then `t` is not an integer. Put
  `n=floor(t)`, so `n>=0`, `n<t<n+1` and `s<=n+1`. Choose rationals `a,b`
  with `t-n <= a < b <= s-n`; this is possible because `t-n<s-n<=1`. By
  monotonicity and the hypothesis,

  ```text
  f(sigma_(t-n)) <= f(sigma_a) <= f'(sigma_b) <= f'(sigma_(s-n)).
  ```

  Add `nu=f(e_n)=f'(e_n)` and use (Z2) to get `f(sigma_t) <= f'(sigma_s)`.
  For `n=0` nothing is added.
- **`s=infinity`.** The integer `ceiling(t)` lies in `[t,infinity)`, so (1)
  applies.

Hence `f(sigma_t) <= f'(sigma_s)` for all `0<t<s<=infinity`. The same
argument with `f,f'` interchanged gives the symmetric inequalities.

*Suprema.* Fix `0<t<=infinity` and choose `r_k<t` increasing to `t`. By
Step 0,

```text
f(sigma_t) = sup_k f(sigma_(r_k)) <= f'(sigma_t),
```

and symmetrically `f'(sigma_t) <= f(sigma_t)`. So `f` and `f'` agree on soft
classes. By Step 1 they agree on compact classes. By (Z1) they agree
everywhere.

## Step 4: perforation obstruction (part 3)

Suppose `f != f'`. By part 2 there is, say, a rational pair `0<t<s<=1` with
`x=f(sigma_t)` not below `y=f'(sigma_s)`. By part 1, `(m+1)x <= my` for all
`m>=(1+t)/(s-t)`. The stated property of `S` would force `x<=y`, which is a
contradiction. The other orientation is identical.

An almost unperforated `S` has the property: take `k=m` for any single large
`m`.

## C-star consequence

For unital `phi,psi:Z->B`, `Cu(phi)(e_1) = [phi(1_Z)] = [1_B] = Cu(psi)(e_1)`.
Apply parts 2 and 3 with `S=Cu(B)`, `f=Cu(phi)`, `f'=Cu(psi)`. If `Cu(phi)`
differs from `Cu(psi)`, the witness pair above shows that `Cu(B)` is not
almost unperforated.

## Relation to the literature

**The almost-unperforated case of part 3 is already in the literature.**
Antoine--Perera--Thiel, arXiv:1410.0483v3, Proposition 7.3.10 (referee
check of the arXiv TeX source, 2026-09-16), states: if `S` is an almost
unperforated Cu-semigroup and `a` is in `S`, then a generalized Cu-morphism
`alpha_a: Z -> S` with `alpha_a(1)=a` exists iff `a` is almost divisible,
and if it exists it is unique. No almost divisibility of `S` is assumed for
uniqueness. So "`S` almost unperforated implies `f=f'`", and hence the
C-star consequence that a witness `B` has `Cu(B)` not almost unperforated,
follow directly from APT 7.3.10. Their proof compares any such map with the
canonical one through the rational intervals
`mu((k,n),a) = {x : nx <= ka <= (n+1)x}` and Lemma 7.3.9, a mechanism close
to Step 2 above. (APT Theorem 7.3.11, `Z`-multiplication iff almost
unperforated and almost divisible, is the global version.)

What this route adds beyond APT 7.3.10 is modest:

- parts 1 and 2 hold in an arbitrary Cu-semigroup;
- part 3 needs only the weaker hypothesis "`(m+1)x<=my` for all large `m`
  implies `x<=y`";
- the failure is located at a pair `f(sigma_t)`, `f'(sigma_s)` with
  rational `0<t<s<=1`.

No novelty or priority is claimed; these refinements may be folklore.
