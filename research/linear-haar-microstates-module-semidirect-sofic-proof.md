---
rg: 2
id: linear-haar-microstates-module-semidirect-sofic-proof
kind: route
title: Translate a linear local code into affine permutation models of A semidirect Lambda
target: linear-haar-microstates-make-module-semidirect-products-sofic
requires: []
---

The route is self-contained and elementary. It uses the standard definition
of soficity: for every finite `F` in `Gamma` and every `delta > 0`, there is
a finite set `X` and a map `Pi : Gamma -> Sym(X)` such that

- `Pi(gh)x = Pi(g)Pi(h)x` for all `g, h in F`, except on a `delta`-fraction of `X`;
- `Pi(e)` is the identity off a `delta`-fraction;
- `Pi(g)` has at most `delta|X|` fixed points for each `g in F \ {e}`.

## 1. Theorem LSC

Fix a `(Phi,W,eps)`-code `(V, sigma, A_0, U, iota, G)`. Put `X = V x U` with
the uniform measure. For `a in A_0` and `lambda in Lambda`, define

```text
S(lambda)(v,u) = (sigma(lambda)v, u),
T(a)(v,u)      = (v, u + iota_v(a)),
Pi(a,lambda)   = T(a) S(lambda).
```

For `a` not in `A_0`, let `T(a)` be the identity. Each map is a bijection of
`X`: `S(lambda)` is a bijection because `sigma(lambda)` is one, and `T(a)`
translates each fibre `{v} x U`.

**Multiplicativity.** Let `g = (a,lambda)` and `h = (b,mu)` with
`a, b in Phi` and `lambda, mu in W`. Then `gh = (a + lambda b, lambda mu)`,
and `a + lambda b in A_0`. Direct evaluation gives

```text
Pi(g)Pi(h)(v,u) = (sigma(lambda)sigma(mu)v,
                   u + iota_{sigma(mu)v}(b) + iota_{sigma(lambda)sigma(mu)v}(a)),
Pi(gh)(v,u)     = (w, u + iota_w(a + lambda b)),   w = sigma(lambda mu)v.
```

Suppose `v in G` and `w in G`. By (C1) at `v`,
`w = sigma(lambda)sigma(mu)v`, so the first coordinates agree. Moreover
`sigma(mu)v = sigma(lambda)^{-1} w` exactly, since `sigma(lambda)` is a
permutation. Then (C2) at `w`, and linearity of `iota_w` on `A_0`, give

```text
iota_{sigma(mu)v}(b) + iota_w(a) = iota_w(lambda b) + iota_w(a) = iota_w(a + lambda b).
```

The vertices `v` with `v` or `sigma(lambda mu)v` outside `G` form at most a
`2 eps`-fraction, since `sigma(lambda mu)` is a bijection. The bad set in `X`
is a union of fibres over these vertices, so its measure is at most `2 eps`.

**Identity.** For `v in G`, (C1) gives `sigma(e)v = v`, and
`iota_v(0) = 0`. So `Pi(0,e)` is the identity off an `eps`-fraction.

**Freeness.** Let `g = (a,lambda)` be in `F \ {e}` and `v in G`.

- If `lambda != e`, then (C1) gives `sigma(lambda)v != v`, so no point of the
  fibre over `v` is fixed.
- If `lambda = e` and `a != 0`, then
  `Pi(g)(v,u) = (v, u + iota_v(a))`, and `iota_v(a) != 0` by (C3). Again no
  point of the fibre is fixed.

So `Pi(g)` has at most `eps|X|` fixed points.

Every finite `F` in `Gamma` lies in some `{(a,lambda) : a in Phi, lambda in W}`.
Given `delta`, take `eps = delta/3`. Hence `Gamma` is sofic. Sofic groups are
hyperlinear (Elek-Szabo; see also Pestov's survey *Hyperlinear and sofic
groups: a brief guide*, 2008), and then `L(Gamma)` is Connes-embeddable. QED.

## 2. Dual form

Let `A = F_p[Lambda]^m/R`, with quotient map `pi`, and `K = R^perp`. The
pairing satisfies `<lambda c, y> = <c, lambda^{-1} y>`, so `K` is
shift-invariant.

Pontryagin duality for the discrete group `F_p[Lambda]^m` and its compact
dual `(F_p^m)^Lambda` gives `K^perp = R`. For a finite window `D`, finite
dimensional duality then gives

```text
(K|_D)^perp  = R intersect F_p[D]^m,
(R intersect F_p[D]^m)^perp = K|_D.                            (D1)
```

Write `A_D = pi(F_p[D]^m)`. Then `(A_D)^*` identifies with `K|_D`: a
pattern `z in K|_D` is the functional `pi(c) -> <c,z>`.

**Microstates give codes.** Given `Phi` and `W`, choose a window `D_0` with
`Phi` contained in `A_{D_0}`, and put `D = D_0 union W D_0`. Take a microstate
`(sigma, L)` for `(D, W_1, eta)`, where `W_1 = W union D_0 union W D_0`, and
let `G_1` be its good set. Define

```text
G = { v in G_1 : sigma(lambda)^{-1} v in G_1 and sigma(lambda mu)^{-1} v in G_1
                 for all lambda in W, mu in D_0 }.
```

Each `sigma(g)^{-1}` is a bijection, so
`|G| >= (1 - (1 + |W| + |W||D_0|) eta)|V|`.

Put `A_0 = A_D` and `U = L^*`. For `v in G_1`, set
`iota_v(pi c)(y) = <c, y_v|_D>`, and for `v` outside `G_1`, set `iota_v = 0`.

- **Well defined.** If `c in R intersect F_p[D]^m`, then `<c, y_v|_D> = 0`,
  because `y_v|_D in K|_D` by the inclusion `subseteq` in (LHM).
- **(C3).** If `pi(c) != 0`, then some `k in K` has `<c,k> != 0`, and
  `k|_D = y_v|_D` for some `y in L` by the inclusion `supseteq`.
- **(C2).** Take `a = pi(c)` with `c` supported in `D_0`, and `lambda in W`. Then

  ```text
  iota_{sigma(lambda)^{-1}v}(a)(y) = sum c_{mu,i} y(sigma(mu)^{-1}sigma(lambda)^{-1}v)_i,
  iota_v(lambda a)(y)              = sum c_{mu,i} y(sigma(lambda mu)^{-1}v)_i.
  ```

  These agree because (C1) holds at `x = sigma(lambda mu)^{-1}v`:
  `sigma(lambda)sigma(mu)x = sigma(lambda mu)x = v`.

**Codes give microstates.** Given `D` (with `e in D`), `W` and `eps`, take a
code for `Phi = A_D` and `W' = W union D` on good set `G`. Put

```text
L = { y_phi : phi in U^* },   y_phi(x)_i = phi(iota_x(pi e_i)).
```

By (C2) at `v in G`, the pattern
`(y_phi)_v(mu)_i = phi(iota_{sigma(mu)^{-1}v}(pi e_i)) = phi(iota_v(pi(mu e_i)))`
is the functional `pi(c) -> phi(iota_v(pi c))` on `A_D`. That is an element
of `(A_D)^* = K|_D`.

By (C3) and linearity, `iota_v` is injective on `A_D`. So every functional
on `A_D` has the form `phi o iota_v`, and all of `K|_D` occurs. QED.

**Haar statistics.** At `v in G`, the pattern map `L -> K|_D` is linear and
surjective. The push-forward of uniform measure on `L` is therefore uniform
on `K|_D`, which is the `D`-marginal of Haar measure on `K`.

## 3. Regular vertices

For `sigma : Lambda -> Sym(V)` and finite `B, E` in `Lambda`, put
`beta_v(kappa) = sigma(kappa)^{-1} v`. Call `v` **(B,E)-regular** if both
of the following hold:

- `beta_v` is injective on `B`;
- `beta_v(kappa s) = sigma(s)^{-1} beta_v(kappa)` whenever `kappa` and
  `kappa s` lie in `B` and `s` lies in `E`.

**Lemma R.** Let `Lambda` be sofic, let `B, E, W` be finite and let
`eta > 0`. Then some `sigma` satisfies (C1) for `W` and is (B,E)-regular,
both on a `(1-eta)`-fraction of `V`.

*Proof.* Take a sofic approximation that is good on a large finite set
containing `B, E, W`, their inverses and their pairwise products. Each of the
following then holds off an arbitrarily small set:

- `sigma(g^{-1}) = sigma(g)^{-1}`;
- `sigma(g)sigma(h) = sigma(gh)`;
- `sigma(g)` has no fixed point for `g` not equal to `e`.

Only finitely many such conditions are used, and composing with a bijection
preserves the size of an exceptional set.

The regularity identity reduces to
`sigma(kappa s)^{-1} = sigma(s)^{-1} sigma(kappa)^{-1}`. For injectivity,
suppose `beta_v(kappa) = beta_v(kappa')` with `kappa` not equal to `kappa'`.
Off the small set this gives `sigma(kappa' kappa^{-1}) v = v`, which fails
off the small set. QED.

**Consequence.** Let `v` be (B,E)-regular and `x = beta_v(g)`. Then
`beta_x(kappa) = beta_v(g kappa)` for every `kappa` in `E` with `g` and
`g kappa` in `B`.

## 4. The classes (E1)-(E4)

**(E1)** Here `R = 0`, so `K|_D` is all of `(F_p^m)^D`. Take `L` to be all
of `(F_p^m)^V`. At a (D,{e})-regular vertex, `y -> y o beta_v` restricted to
`D` is onto, because `beta_v` is injective on `D`.

**(E2)** A code for `A` restricts to a submodule `A'` by replacing `A_0` with
`A_0` intersected with `A'`. A code for a submodule containing `Phi` is
already a code for `A`.

**(E3)** Let `Lambda` be amenable and let `S` be a finite symmetric set
containing `e, W, W^2, D`. By the right Folner condition, choose a finite set
`F` in which at least `(1-eps)|F|` elements `g` satisfy `gS` in `F`.

Put `V = F` and let `sigma(lambda)` be any permutation of `F` extending the
partial map `g -> g lambda^{-1}`. For such a good `g`:

- `sigma(lambda)^{-1} g = g lambda`;
- (C1) holds;
- with `L = K|_F`, the pattern of `k|_F` at `g` is `(g^{-1}k)|_D`.

Since `g^{-1}K = K`, the patterns are exactly `K|_D`.

**(E4)** The union of the `Fix_N(K)` is directed and dense, and `K|_D` is
finite. So some `N_1` has `Fix_{N_1}(K)|_D = K|_D`.

By residual finiteness, choose a normal finite-index subgroup `N` of `N_1`
avoiding the nontrivial elements of `(W+D)^{-1}(W+D)`, where `W+D` denotes
the union. Put `V = Lambda/N` and `sigma(lambda)(gN) = g lambda^{-1} N`. This
is well defined because `N` is normal, and it is an exact action that is free
on `W`.

Take `L = Fix_N(K)`, whose elements are functions on `Lambda/N`. The pattern
at `gN` is `(g^{-1}y)|_D`, and `g^{-1}` preserves `Fix_N(K)`. So the patterns
form `Fix_N(K)|_D`, which contains `Fix_{N_1}(K)|_D = K|_D` and is contained
in `K|_D`. Every vertex is good.

This alone strictly extends (DHA1). For infinite residually finite
`Lambda`, the constant subshift `K = F_p` has dense periodic points and
`K_fin = 0`.

## 5. (E5) Dense homoclinic group

Let `Lambda` be sofic, `K` a closed shift-invariant subgroup of
`(F_p^m)^Lambda`, and `K_fin` dense in `K`. Fix a window `D` containing `e`.

A dense subgroup maps onto the finite projection, so `K_fin|_D = K|_D`.
Choose `h_1, ..., h_r` in `K_fin` whose restrictions to `D` span `K|_D`.
Let `S` contain `e`, `D` and all the supports.

Apply Lemma R with `E` equal to `S` union `S^{-1}`, and `B` a finite set
containing `D`, `D S^{-1}` and `D S^{-1} S`. Let `G_r` be the set of regular
vertices, and let `G` be `G_r` intersected with the (C1) set.

For `h = h_j` and `x` in `G_r`, define the **placed copy** `h^(x)`:

- `h^(x)(beta_x(nu)) = h(nu)` for `nu` in `S`;
- `h^(x) = 0` elsewhere.

This is well defined because `beta_x` is injective on `S`. For `x` outside
`G_r`, put `h^(x) = 0`. Let `L` be the span of all `h_j^(x)`.

Fix `v` in `G`.

- **Every pattern of `K|_D` occurs.** For `mu` in `D`, `beta_v(mu)` lies in
  `beta_v(S)` iff `mu` lies in `S`, by injectivity on `B`. So the pattern of
  `h_j^(v)` at `v` is `h_j|_D`. These patterns span `K|_D`.
- **Every pattern lies in `K|_D`.** Suppose `h^(x)` has a nonzero pattern at
  `v`. Then `beta_v(mu) = beta_x(nu)` for some `mu` in `D` and `nu` in `S`.
  Since `beta_x(nu) = sigma(nu)^{-1}x`, we get
  `x = sigma(nu) beta_v(mu) = beta_v(g)` with `g = mu nu^{-1}` in
  `D S^{-1}`, by regularity at `v`.

  By the Consequence of Lemma R, `beta_x(nu') = beta_v(g nu')` for `nu'` in
  `S`. So for `mu'` in `D`, `beta_v(mu') = beta_x(nu')` iff `mu' = g nu'`, by
  injectivity on `B`.

  Hence `h^(x)(beta_v(mu')) = h(g^{-1}mu') = (g h)(mu')`, using that `h`
  vanishes off `S`. The pattern is `(g h)|_D`, which lies in `K|_D`.

By linearity of the pattern map, (LHM) holds at every `v` in `G`. By
Section 2 and Section 1, `hat K semidirect Lambda` is sofic. This strengthens
the CE conclusion of dense-homoclinic-algebraic-actions-are-ce in the
`F_p`-linear case, with no input from Hayes or Paunescu.

## 6. (E6) Permutation modules over LERF actors

Let `Lambda` be LERF, meaning every finitely generated subgroup is closed in
the profinite topology. Let `Delta` be any subgroup, `Q = Lambda/Delta`, and
`A = F_p[Q]`, with basis `Q` and the permutation action. Fix `Phi` and a
symmetric `W` containing `e`.

Let `B_0` contain the supports of `Phi`, and put `B = B_0 union W B_0`, a
subset of `Q`. Let `Gamma_B` be the finite labelled graph with vertex set `B`
and an edge `q -> s q` labelled `s` whenever `s` is in `W` and both ends lie
in `B`.

For `q, q'` in `B`, let `P(q,q')` be the set of group elements read along
paths from `q` to `q'` in `Gamma_B`. Then `J_q = P(q,q)` is a subgroup: it is
the image of the fundamental group of a finite graph, so it is finitely
generated. It fixes `q`, because paths in `Gamma_B` are genuine orbits in
`Q`. And `P(q,q') = c J_q` for any `c` in `P(q,q')`.

When `q` differs from `q'`, `c q = q'`, so `c` is not in `J_q`. Since `J_q`
is closed and equals the intersection of the sets `H J_q` over normal
finite-index `H`, some normal finite-index `H_{q,q'}` has `c` outside
`H_{q,q'} J_q`.

Let `H` be the intersection of these finitely many `H_{q,q'}` and one more
normal finite-index subgroup avoiding the nontrivial elements of `W`. This
uses residual finiteness, which follows from LERF.

**The code.**

- `V = Lambda/H` with left multiplication `sigma`. This is an exact
  homomorphism, and every point has stabiliser `H`.
- `Y` is the quotient of `V x B` by the equivalence relation generated by
  `(sigma(lambda)^{-1} v, q) ~ (v, lambda q)`, for `lambda` in `W` and `q`,
  `lambda q` in `B`.
- `U = F_p[Y]`, `A_0 = F_p[B]`, and `iota_v(q) = delta_[v,q]`, extended
  linearly.

**Checking the conditions.**

- (C1) holds because `W` meets `H` only in `e`.
- (C2) is the generating relation, applied termwise.
- (C3): a chain from `(v,q)` to `(v,q')` gives a word `w` in `P(q,q')` with
  `sigma(w)v = v`, i.e. `w` in `H`. But `H` does not meet `c J_q`. So
  `q -> [v,q]` is injective on `B_0`, and `iota_v(a)` is nonzero for nonzero
  `a` in `Phi`.

Every vertex is good.

**Corollary.** Free groups are LERF (M. Hall, *Coset representations in free
groups*, Trans. AMS 67 (1949)). So `F_p[F/N]` has linear sofic codes over `F`
for every normal `N`. Taking `F/N` to be an infinite finitely generated
simple group, such as Thompson's `T`, gives:

- `Fix_H(K)` consists only of constants for every finite-index `H`, since the
  image of `H` is `F/N`;
- `K_fin = 0` because `N` is infinite.

So (E6) lies outside both (E4) and (E5).

Suppose an "extraction lemma" held: codes for `F_p[F/N]` over `F` imply that
`F/N` is sofic. Then every finitely generated group would be sofic. So any
extraction of a sofic structure on `Q` from linear codes must use more than
the codes. The
construction is the linear form of the known fact that actions of LERF
groups are sofic.
