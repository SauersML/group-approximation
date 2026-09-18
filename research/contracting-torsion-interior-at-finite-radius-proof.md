---
rg: 2
id: contracting-torsion-interior-at-finite-radius-proof
kind: route
title: Iterate the section operator from the radius-rho0 relators; contraction climbs to the kernel and infinite order lifts along the self-replicating vertex
target: contracting-torsion-interior-at-finite-radius
requires: []
---

Notation as in `contracting-torsion-interior-at-finite-radius`. Automorphisms
act on the left, and `(gh)|_v = g|_{h(v)} h|_v`. `F = F(S)` has one letter
`s-bar` for each `s in S` (so `S` already contains inverse elements as
letters, and `F` also has formal inverses). `1-bar` is the empty word.
`pi: F -> J` is evaluation, `N = ker pi`, `N_{<= r}` is the set of words in
`N` of length `<= r`, and `M_0 = <<N_{<= rho0}>>`, so `F/M_0 = G_rho0`. For
`g in F` and a vertex `v`, write `g(v) := pi(g)(v)`. Let
`F_j = pi^-1(St_J(j))`.

## Step 1. Section cocycles on the free group

For a word `w = t_1^{e_1} ... t_k^{e_k}` (`t_i in S`, `e_i = +-1`) and `x in X`,
let `y_i = (t_{i+1}^{e_{i+1}} ... t_k^{e_k})(x)`. Let `Phi_x(w)` be the product,
in order, of the words `(t_i|_{y_i})-bar` when `e_i = +1`, and
`((t_i|_{t_i^-1(y_i)})-bar)^-1` when `e_i = -1`.

(a) *Well defined on `F`.* For `t t^-1` inserted with x-value `y` for `t^-1`,
the letter `t` has x-value `t^-1(y)`. The contributions
`(t|_{t^-1 y})-bar (t|_{t^-1 y})-bar^-1` cancel. The case `t^-1 t` is similar.
The x-values of the other letters do not change.

(b) *Cocycle.* `Phi_x(uw) = Phi_{w(x)}(u) Phi_x(w)`. So `Phi_x` is a homomorphism
on `F_1`, and `Phi_{g^-1(x)}(g) Phi_x(g^-1) = 1`.

(c) *Lifting.* `pi(Phi_x(w)) = pi(w)|_x`, by induction on the length with the
section product rule.

(d) *Length.* `|Phi_x(w)| <= |w|`, because `S` is closed under sections.

For `v = x_1 ... x_j` put `Phi_v := Phi_{x_2...x_j} o Phi_{x_1}`. By induction on
`j`, from (b) and (c): `Phi_v(uw) = Phi_{w(v)}(u) Phi_v(w)`,
`pi(Phi_v(w)) = pi(w)|_v`, and `|Phi_v(w)| <= |w|`.

## Step 2. The operator and its fixed point

For normal `M` of `F` let
`Theta(M) = { w in F_1 : Phi_x(w) in M for all x in X }`.

(i) `Theta(M)` is a normal subgroup. It is a subgroup by (b). By (b),
`Phi_x(g w g^-1)` equals `Phi_{g^-1 x}(g) Phi_{g^-1 x}(w) Phi_{g^-1 x}(g)^-1`,
because `w(g^-1 x) = g^-1 x`. This lies in `M`.

(ii) `Theta` is monotone, and `Theta(M) <= Phi_{x_0}^-1(M)`.

(iii) `M_0 <= Theta(M_0)`. If `r in N_{<= rho0}` then `r in F_1`. Each
`Phi_x(r)` lies in `N` by (c) and has length `<= rho0` by (d), so it lies in
`N_{<= rho0}`. By normality of `Theta(M_0)` this suffices.

(iv) `Theta(N) <= N`. If `w in F_1` has every section `pi(w)|_x` trivial, then
`pi(w) = 1`.

(v) *Level `n`.* If `w in F_n` and `Phi_v(w) in M` for all `v in X^n`, then
`w in Theta^n(M)`. The proof is by induction on `n`. Since
`pi(Phi_x(w)) = pi(w)|_x in St_J(n-1)` and `Phi_{v'}(Phi_x(w)) = Phi_{xv'}(w) in M`,
we get `Phi_x(w) in Theta^{n-1}(M)` for every `x`, and `w in F_1`.

Put `M_{k+1} = Theta(M_k)`. By (iii) and (ii), `M_0 <= M_1 <= ...`. By (iv),
all `M_k <= N`.

## Step 3. `U_k M_k = N`

For `w in F` let `l(w)` be the minimal length of a word in `w M_0`. We use
strong induction on `L = l(w)` for `w in N`. Choose `w'` in `w M_0` with
`|w'| = L`, so `w' in N`.

If `L <= rho0`, then `w' in N_{<= rho0} <= M_0`, so `w in M_0`.

Let `L > rho0` and `v in X^n`. Cut `w' = w_1 ... w_q` into subwords of length
`<= m`, with `q = ceil(L/m)`. By the cocycle rule
`Phi_v(w') = Phi_{v_1}(w_1) ... Phi_{v_q}(w_q)` for suitable `v_i in X^n`.
Each `Phi_{v_i}(w_i)` is a word of length `<= m` representing
`pi(w_i)|_{v_i}`. By contraction, that element has length
`<= lambda |pi(w_i)| + C <= lambda m + C`. Let `u_i` be a geodesic word for it.
The word `Phi_{v_i}(w_i) u_i^-1` lies in `N` and has length
`<= m + lambda m + C <= 2m + C <= rho0`, so it lies in `M_0`. Hence
`Phi_v(w') = u_v := u_1 ... u_q` mod `M_0`. By (c), `u_v in N`, and

`|u_v| <= q(lambda m + C) <= (L/m + 1)(lambda m + C)`
`<= (lambda + C/m) L + lambda m + C <= ((1+lambda)/2) L + lambda m + C < L`,

using `m >= 1`, `C/m <= (1-lambda)/2` and `L > rho0 >= 2(lambda m + C)/(1-lambda)`. So
`l(u_v) < L`. By induction `u_v in M_{j_v}`. Let `j = max_v j_v`. Then
`Phi_v(w') in u_v M_0 <= M_j` for all `v in X^n`, and `w' in N <= F_n`. By
(v), `w' in Theta^n(M_j) = M_{j+n}`, and `w in w' M_0 <= M_{j+n}`.

## Step 4. Lifting infinite order

`Phi_{x_0}(F_1) M_0 = F`. For `s in S`, the word `h_s` lies in `F_1`, and
`pi(Phi_{x_0}(h_s)) = pi(h_s)|_{x_0} = s`. So `Phi_{x_0}(h_s) s-bar^-1` is in
`N`, with length `<= H + 1 <= rho0`, hence in `M_0`.

Suppose `g` has infinite order mod `M_k`. Pick `h in F_1` and `c in M_0` with
`Phi_{x_0}(h) = g c`. If `h^j in M_{k+1}` (`j >= 1`), then by (ii)
`(gc)^j in M_k`, so `g^j in M_k`, a contradiction. Hence: **if `G_rho0` is not
torsion, then no `F/M_k` is torsion.**

## Step 5. The equivalences

(3) => (2) is trivial. (3) => (1) holds because `G_rho0` is finitely presented
and maps onto `J`.

(1) => (3). Suppose `G_rho0` is not torsion, and let `P = F(Y)/<<R>>` be
finitely presented with `p: P -> J` onto. Choose `lambda: F(Y) -> F` lifting
`p`, and words `mu(s) in F(Y)` with `p(mu(s)) = pi(s-bar)`. The finite set
`lambda(R) u { s-bar^-1 lambda(mu(s)) }` lies in `N`, hence in some `M_k` by
Step 3. So `lambda` induces a surjection `P -> F/M_k`. By Step 4 the target
has an element of infinite order, and so does `P`.

(2) => (3). If `G_rho0` is not torsion, then for every `rho` the finite set
`N_{<= rho}` lies in some `M_k`. So `G_rho` maps onto the non-torsion `F/M_k`
and is not torsion.

*Marked limit.* When the conditions fail, `F/M_k -> J` with every `F/M_k`
non-torsion, by Steps 3 and 4. []

## Remarks

- Only `n`, `lambda`, `C`, `H` enter `rho0`. They can be computed from a
  finite automaton for `J` together with the nucleus, so `rho0` is explicit.
- Step 3 never uses that `J` is torsion or branch. The torsion hypothesis
  enters only through the dichotomy on `G_rho0`.
- For spinal groups one can replace `M_0` by the smaller base `A * B`. Then
  Step 4 needs no radius, and the dichotomy is resolved
  (`self-similar-spinal-groups-not-fp-torsion-quotients`).
