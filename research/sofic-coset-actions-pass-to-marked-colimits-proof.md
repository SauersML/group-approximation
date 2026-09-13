---
rg: 2
id: sofic-coset-actions-pass-to-marked-colimits-proof
kind: route
title: Lift the finitely many window relations to a stage and transport the stage atlas
target: sofic-coset-actions-pass-to-marked-colimits
requires: []
---

Definition 2.1(3) of GKP: `phi: G -> Sym(A)` is an `(F,E,eps)`-orbit
approximation of `alpha: G action X` if there are a finite set `B` and
`S subset A` with `|S| > (1-eps)|A|`, and for each `s in S` an injective
`pi_s: E -> B`, such that

```text
pi_(phi(g)s)(x) = pi_s(g^(-1) x)                                   (OA)
```

for all `s in S`, `g in F`, `x in E` with `phi(g)s in S` and
`g^(-1)x in E`.  Definition 2.1(5): `alpha` is sofic if for all finite `F`,
`E` and `eps>0` some unital `(F,eps)`-multiplicative `phi` is an
`(F,E,eps)`-orbit approximation.  Multiplicativity means
`|{a : phi(g)phi(h)a = phi(gh)a}| >= (1-eps)|A|` for `g,h in F`.

Throughout, `X=G/H`, `E subset X` is finite, and `r_x in G` is a chosen
representative of `x in E`.  The **window cocycle** is the finite set

```text
W = { r_(g^(-1)x)^(-1) g^(-1) r_x :  g in F, x in E, g^(-1)x in E }  subset H.   (WC)
```

## Item 1 (separable stabilizers)

`H` closed means `H = intersection_N HN` over finite-index normal `N`.
Given `F,E,eps`, choose `N` with `r_x^(-1) r_y notin HN` for the finitely
many pairs `x != y` in `E`.  Put `A=G/N`, `phi(g)kN = gkN` (a genuine
action, so unital and exactly multiplicative), `S=A`, `B=G/HN`, and

```text
pi_(kN)(x) = k^(-1) r_x HN.
```

This is well defined: for `n in N`, `n^(-1)y HN = y (y^(-1)n^(-1)y) HN = y HN`.
It is injective on `E` by the choice of `N`.  For (OA),
`pi_(gkN)(x) = k^(-1) g^(-1) r_x HN = k^(-1) r_(g^(-1)x) HN = pi_(kN)(g^(-1)x)`,
since `g^(-1) r_x in r_(g^(-1)x) H`.  All errors are zero.

## Item 3 (directed colimits); item 2 is its special case

Fix `F,E,eps` and form `W` by (WC).

*Stage choice.*  The images `p_n(H_n)` increase, because
`p_(n+1)(H_(n+1)) >= p_(n+1) q_n(H_n) = p_n(H_n)`, and their union is `H`.
Choose `n_0` with `W subset p_(n_0)(H_(n_0))`.  Choose lifts
`l(g) in G_(n_0)` of the finitely many elements `g in F ∪ FF ∪ {r_x}`, with
`l(1)=1`, and lifts `l(w) in H_(n_0)` of `w in W`.  The finitely many
elements

```text
l(g) l(h) l(gh)^(-1)                         (g,h in F),
l(g)^(-1) l(r_x) l(w)^(-1) l(r_(g^(-1)x))^(-1)   (w = r_(g^(-1)x)^(-1) g^(-1) r_x)
```

lie in `ker p_(n_0)`.  Push everything forward to a stage `n` at which all
of them are trivial.  Pushing forward preserves `l(1)=1`, keeps `l(w)` in
`H_n` because `q(H_m) <= H_(m+1)`, and keeps the lifting property.  Extend
`l` to a map `G -> G_n` with `l(1)=1` arbitrarily off the finite set.  At
stage `n` we now have the exact identities

```text
l(g) l(h) = l(gh),     l(g)^(-1) l(r_x) = l(r_(g^(-1)x)) l(w),   l(w) in H_n.   (LIFT)
```

*Transport.*  Put `F' = l(F) ∪ l(FF)` and `E' = { l(r_x) H_n : x in E }`.
The map `x -> l(r_x)H_n` is injective: if `l(r_x)H_n = l(r_y)H_n`, apply
`p_n` and use `p_n(H_n) <= H` to get `r_x H = r_y H`.  Apply soficity of
`G_n action G_n/H_n` to `(F', E', eps)`, obtaining `phitilde`, `S`, `B` and
charts `pitilde_s`.  Define

```text
phi = phitilde o l : G -> Sym(A),        pi_s(x) = pitilde_s( l(r_x) H_n ).
```

`phi` is unital.  For `g,h in F`, `phi(g)phi(h) = phitilde(l g) phitilde(l h)`
agrees with `phitilde(l(g)l(h)) = phitilde(l(gh)) = phi(gh)` on at least
`(1-eps)|A|` points, by multiplicativity of `phitilde` on `F'` and (LIFT).
Each `pi_s` is injective because `pitilde_s` is and `x -> l(r_x)H_n` is.
For (OA), let `g in F`, `x in E`, `g^(-1)x in E`, `s, phi(g)s in S`.  By
(LIFT), `l(g)^(-1) l(r_x) H_n = l(r_(g^(-1)x)) H_n in E'`, so the stage
covariance applies to `l(g) in F'`:

```text
pi_(phi(g)s)(x) = pitilde_(phitilde(l g)s)(l(r_x)H_n)
                = pitilde_s( l(g)^(-1) l(r_x) H_n )
                = pitilde_s( l(r_(g^(-1)x)) H_n ) = pi_s(g^(-1)x).
```

So `phi` is a unital `(F,eps)`-multiplicative `(F,E,eps)`-orbit
approximation.  For item 2 take `G_n=G`, `p_n=q_n=id`, `l=id`; then (LIFT)
reduces to `W subset H_n`.

## Item 4

Item 1 makes each `G_n action G_n/H_n` sofic; apply item 3.  The model built
at a window is a genuine finite action of `G_n` composed with the
set-theoretic lift `l`, which is multiplicative only on the window.

## Item 5 (finite-presentation stop)

Let `G = <Sigma | R>` with `Sigma, R` finite and `H = <T>` with `T` finite.
Lift `Sigma` to `G_(n_0)`; the relators become elements of `ker p_(n_0)`
and die at some stage, giving a homomorphism `s: G -> G_(n_1)` with
`p_(n_1) s = id` on `Sigma`, hence everywhere.  For `t in T` pick a stage
and `h_t in H` of that stage with `p(h_t)=t`; push to a common stage, where
`s(t) h_t^(-1)` lies in the kernel and dies later.  Composing `s` with the
further `q`'s keeps it a section.  At a stage `n_2` we get `s(T) subset
H_(n_2)`, so `s(H) <= H_(n_2)`.  Then

```text
H <= s^(-1)(H_(n_2)) <= p_(n_2)(H_(n_2)) <= H,
```

where the middle inclusion is `g = p_(n_2)(s(g))`.  So `H = s^(-1)(H_(n_2))`.
A preimage of a closed subgroup under a homomorphism is closed: with
`H_(n_2) = intersection_N H_(n_2)N`, each `s^(-1)(H_(n_2)N)` is a subgroup
containing the finite-index normal subgroup `s^(-1)(N)`.  Hence `H` is
separable in `G`.  A co-dense stabilizer is not separable, which gives the
stated consequence.
