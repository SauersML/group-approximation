---
rg: 2
id: higman-host-coset-soficity-makes-compiler-rope-sofic-proof
kind: route
title: Build the compiler's hub incidence code from coset models of the Higman host, with left-right frames on both hub coordinates
target: higman-host-coset-soficity-makes-compiler-rope-sofic
requires:
  - hub-incidence-color-code-makes-edge-coset-action-sofic
  - gkp-sofic-action-is-liftable-hamming-chart-family
  - free-cover-left-right-action-over-sofic-group-is-sofic
  - compiler-rope-edge-is-not-co-amenable
  - envelope-coset-action-sofic-once-edge-coset-action-sofic
---

Notation of the claim, on `INF`. Write `H = H_e`, `Q = Q_e = B3(1)`, `K = K_e`,
`L = L_e`, `M = M_e`. The coordinates of `k in K` are `k = (a, u, u', b, p)`, with
`a, b in F`, `u, u' in F(X_e)`, `p in P`. "a.e." means: for each fixed group
element, or finite family of them, the proportion of points where the stated property
fails tends to `0` along the relevant index. Finitely many a.e. statements hold
simultaneously a.e. All sequences below are indexed by `n in Nat` and converge along
`Nat`. So any free ultrafilter `U` serves in (HC).

## 1. The quotient `K/L` and the incidence set

Define an action of `K` on `H x P` by

```text
(a,u,u',b,p).(h,x) = ( pi(u) h pi(u')^-1 ,  jq(b) x p^-1 ).            (Q1)
```

Both coordinates are two-sided translations, so (Q1) is an action. Put `x_0 = (1,1)`.
The action is transitive, because `pi` is onto. The stabilizer of `x_0` consists of the
`k` with `pi(u) = pi(u')` and `p = jq(b)`, with `a` arbitrary. That is
`F x M x graph(jq) = L`, where `M = {(u,u') : pi u = pi u'}`. Hence `kL -> k.x_0` is a
`K`-isomorphism `K/L -> H x P`.

The embedded copy of `f in F` is `(f, w_f, 1, f, 1)` with `pi(w_f) = iota q(f)`. So

```text
F.x_0 = Q'' := { (iota q, j q) : q in Q }  <=  H x P,                   (Q2)
```

a subgroup, isomorphic to `Q` because `iota` and `j` are injective. For `k in K` we have
`kL in F.x_0` iff `k in FL`. Write `kappa(k) = k.x_0`. Since `Q''` is a subgroup,

```text
k in FL   iff   kappa(k) in Q''   iff   kappa(k)^-1 in Q'',              (Q3)
```

where `kappa(k)^-1 = (pi(u') pi(u)^-1, p jq(b)^-1)` is the inverse in the group `H x P`.

## 2. Data (RSH): a product-form relative model

**(RSH)** There are:

- finite sets `D_n` and maps `sigma_n : H -> Sym(D_n)` that form a sofic approximation
  of `H`. For fixed `h, h'`, `sigma_n(hh') = sigma_n(h) sigma_n(h')` a.e., and for fixed
  `h != 1`, `sigma_n(h) d != d` a.e.;
- finite quotients `r_n : P -> C_n` such that for each `x != 1`, `r_n(x) != 1` for all
  large `n`;
- colorings `gamma_n : D_n x C_n -> Nat` such that for every fixed `(h,x) in H x P`,
  as `n -> oo`, with the uniform measure on `D_n x C_n`,

```text
gamma_n( sigma_n(h) d , r_n(x) e ) = gamma_n(d,e)   a.e.   if (h,x) in Q'',
gamma_n( sigma_n(h) d , r_n(x) e ) != gamma_n(d,e)  a.e.   if (h,x) notin Q''.   (R)
```

## 3. (RSH) implies (HC_e)

Fix `n` and drop it from the notation. Let `X_e` be the finite generating set of `F(X_e)`,
and let `lambda : F(X_e) -> Sym(D)` be the homomorphism with `lambda(x) = sigma(pi x)`
on letters. By induction on word length, `lambda(u) = sigma(pi u)` a.e. for each fixed
`u`.

**Finite quotients for `F`.** `F` is the graph of the homomorphism
`theta : F -> F(X_e) x F(X_e) x F x P`, `theta(f) = (w_f, 1, f, 1)` (fix `w` on the letters
`x, y, t` and extend). The codomain is residually finite. If `k = (a, k') notin F`, then
`theta(a) != k'`. Choose a finite quotient `psi` of the codomain with
`psi(theta a) != psi(k')`. Then `{(a,k') : psi theta(a) = psi(k')}` is a finite-index
subgroup containing `F` and not `k`. Intersecting finitely many of these along an
enumeration of `K`, we get finite-index subgroups `F_n >= F`, decreasing, with
`∩ F_n = F`. Let `N_n = core_K(F_n)` and `Z_n = K/N_n`.

**The space and the action.** Let `A = D x Sym(D) x C x C x Z`, with the uniform
measure. For `k = (a,u,u',b,p)` put

```text
b(k)(d, s, e, t, z) = ( lambda(u) d,  s lambda(u')^-1,  r(jq b) e,  t r(p)^-1,  z k^-1 ).
```

The five coordinates are acted on by the direct factors of `K` or by exact homomorphisms,
and the actions commute exactly. So `b` is an exact homomorphism `K -> Sym(A)`. Here
`z k^-1` is right translation on `K/N_n`, which is well defined because `N_n` is normal.

**Colors.**

```text
zeta(d,s,e,t,z)  = ( s(d),  t e ),
omega(d,s,e,t,z) = ( gamma(d,e),  s,  t,  z F_n ),
R = { (omega, zeta') : gamma( s^-1 zeta'_1 , t^-1 zeta'_2 ) = gamma-component of omega },
```

where `s, t` in the definition of `R` are read off `omega`. `t e` and `t^-1 zeta'_2`
are products in `C`. The palettes are countable; code them into `Nat` injectively.

For `k = (a,u,u',b,p)` and `alpha = (d,s,e,t,z)`,

```text
b(k)^-1 alpha = ( lambda(u)^-1 d,  s lambda(u'),  r(jq b)^-1 e,  t r(p),  z k ),
zeta(b(k)^-1 alpha) = ( s lambda(u') lambda(u)^-1 d ,  t r(p jq(b)^-1) e ).     (Z)
```

**(HC2): `zeta` is exact for `L`.** Let `k in L`. Then `pi u = pi u'`, so
`lambda(u') lambda(u)^-1 d = sigma(pi(u') pi(u)^-1) d = d` a.e. Also `p = jq(b)`, so the
second entry of (Z) is `t e`. Hence `zeta` is invariant a.e. Now let `k notin L`. If
`pi u != pi u'`, then `h = pi(u') pi(u)^-1 != 1`, and a.e. `lambda(u')lambda(u)^-1 d =
sigma(h) d != d`. Since `s` is a bijection, the first entry of (Z) differs from `s(d)`.
If `p != jq(b)`, then for large `n`, `c = r(p jq(b)^-1) != 1`, and `t c e != t e` for
every `e`. In both cases `zeta` changes a.e.

**(HC1): `omega` is exact for `F`.** Let `k = (f, w_f, 1, f, 1)`. By (Z) and the
definition, `b(k)^-1` changes `(d, e)` to `(lambda(w_f)^-1 d, r(jq f)^-1 e)` and fixes
`s` and `t`. The first of these equals `sigma(iota q f)^-1 d` a.e. Because
`(iota q f, jq f)^-1 in Q''`, the color `gamma` is unchanged a.e., by (R). The last
coordinate goes to `z k F_n = z F_n`, since `k in F <= F_n`. So `omega` is invariant
a.e. If `k notin F`, then `k notin F_n` for large `n`. Then `z k F_n != z F_n` for
every `z`, since `z k F_n = z F_n` iff `k in F_n`. So `omega` changes everywhere.

**(HC3): `R` decides `FL`.** By (Z), with `s, t` read off `omega(alpha)`,

```text
( s^-1 zeta_1(b(k)^-1 alpha),  t^-1 zeta_2(b(k)^-1 alpha) )
   = ( lambda(u')lambda(u)^-1 d,  r(p jq(b)^-1) e )
   = ( sigma(pi(u')pi(u)^-1) d,  r(p jq(b)^-1) e )     a.e.
   = (sigma x r)( kappa(k)^-1 ) (d,e)                    a.e.
```

So `(omega(alpha), zeta(b(k)^-1 alpha)) in R` iff
`gamma((sigma x r)(kappa(k)^-1)(d,e)) = gamma(d,e)`. By (R) this holds a.e. if
`kappa(k)^-1 in Q''`, and fails a.e. otherwise. By (Q3) that is exactly `k in FL`
versus `k notin FL`. The measure on `A` is a product, and the event depends only on
`(d,e)` (after fixing `s,t`), so the a.e. statements on `D x C` transfer to `A`.

So (HC) holds for `(K, L, F)` with representatives `b_n`. The Theorem of
[[hub-incidence-color-code-makes-edge-coset-action-sofic]] gives that
`Gamma_e ↷ Gamma_e/S'` is sofic, where `S' = < F, v F v^-1 >`. The compiler's edge
`S_e = < F, F^v >` is conjugate to `S'` by a power of `v`
(`v^-1 S' v = < v^-1 F v, F >`), so the two coset actions are isomorphic `Gamma_e`-sets.

## 4. (HQ) implies (RSH)

**Chain.** `P = F_2 x F_2` is residually finite and countable. Choose finite quotients
`r_n : P -> C_n` with `ker r_{n+1} <= ker r_n` and `∩ ker r_n = 1`. Put
`J_n = j^-1(ker r_n)`, a finite-index normal subgroup of `Q`, decreasing, with
`∩ J_n = 1`. Put `R_n = r_n j(Q) <= C_n`.

**One-color codes.** By (HQ) and the section "From orbit charts to one color" of
[[mikhailova-one-color-code-proof]] (valid for every transitive action), for each `n`
there are a free ultrafilter `V_n`, a homomorphism
`phi^(n) : H -> prod_(V_n) Sym(B_(n,i))` and colorings `delta_(n,i)`. For each fixed
`g in H`, the proportion of `beta` with `delta(phi(g)^-1 beta) != delta(beta)` tends
along `V_n` to `0` if `g in iota(J_n)`, and to `1` otherwise.

**Transversal and decoding.** Choose a right transversal `T_n` of `R_n` in `C_n`, and for
each `e in C_n` write `e = r_n j(q_e) tau(e)` with `tau(e) in T_n`, where `q_e in Q` is a
fixed choice from a finite set `E_n` of representatives of `Q/J_n`. For
`c in C_n` and `e in C_n`,

```text
tau(c e) = tau(e)   iff   c in R_n,                                     (T)
```

because `R_n c e = R_n e` iff `c e in R_n e` iff `c in R_n`. If `c = r_n j(q)`, then
`q_{c e} = q q_e n'` for some `n' in J_n`. For fixed `q`, the element `n'` ranges over the
finite set `N_n(q) = E_n^-1 q^-1 E_n ∩ J_n`.

**Finite windows.** Enumerate `H = {h_1, h_2, ...}` and `Q = {q_1, q_2, ...}`. Let `W_n <= H`
be the set of words of length at most `6` in:

- `h_1, ..., h_n`;
- `iota(E_n)` and `iota(q_1), ..., iota(q_n)`;
- `iota(N_n(q))` for `q in {q_1, ..., q_n} ∪ E_n`.

Let `epsilon_n = 1/(n (|W_n| + |E_n| + 1)^3)`. Choose an index `i` in the `V_n`-large set
on which:

- `phi^(n)_i` is `epsilon_n`-multiplicative on `W_n x W_n`;
- `delta_(n,i)` has invariance proportion `>= 1 - epsilon_n` on `W_n ∩ iota(J_n)`;
- `delta_(n,i)` has displacement proportion `>= 1 - epsilon_n` on `W_n \ iota(J_n)`.

Finitely many conditions hold on a `V_n`-large set, so such an `i` exists. Write
`phi_n, delta_n, B_n` for the chosen data, and set `D_n = B_n`, `sigma_n = phi_n`.

**`sigma_n` is a sofic approximation.** Fix `h, h'`. For large `n`, `h, h', hh' in W_n`,
so multiplicativity holds up to `epsilon_n -> 0`. Fix `h != 1`. Since `∩ iota(J_n) = 1`
and the `J_n` decrease, `h notin iota(J_n)` for large `n`. Then `delta_n` is displaced by
`h` on a proportion `>= 1 - epsilon_n` of points, and such points are moved. So
`sigma_n(h)` is free a.e. In particular `H` is sofic. This is item 1 of the Theorem,
first half.

**The color.** On `D_n x C_n` define

```text
gamma_n(beta, e) = ( delta_n( phi_n(iota q_e)^-1 beta ),  tau(e) ).
```

**Invariance on `Q''`.** Fix `q in Q`, say `q = q_i`, and let `n >= i`. The element
`(iota q, jq)` acts by `(beta, e) -> (phi_n(iota q) beta, r_n j(q) e)`. By (T), `tau` is
unchanged. With `q_{new} = q q_e n'`, `n' in N_n(q)`, the first entry becomes

```text
delta_n( phi_n(iota q_new)^-1 phi_n(iota q) beta ).
```

For `beta` outside a set of proportion `<= 3 |E_n|^2 |N_n(q)| epsilon_n`, multiplicativity
on `W_n` gives

```text
phi_n(iota q_new)^-1 phi_n(iota q) beta = phi_n(iota n')^-1 phi_n(iota q_e)^-1 beta,
```

because `q_new^-1 q = n'^-1 q_e^-1`. Put `beta' = phi_n(iota q_e)^-1 beta`, a bijective
change of variable for fixed `e`. Since `iota(n') in W_n ∩ iota(J_n)`, we get
`delta_n(phi_n(iota n')^-1 beta') = delta_n(beta')` outside proportion `epsilon_n`. The
total bad proportion is `O(|W_n|^3 epsilon_n) -> 0`. So `gamma_n` is invariant a.e.

**Displacement off `Q''`.** Fix `(h, x) notin Q''`, say `h = h_i`, and take `n >= i`
large. There are two cases.

- *Case `r_n(x) notin R_n`.* By (T), `tau` changes for every `e`.
- *Case `r_n(x) in R_n`.* Choose `q in E_n` with `r_n j(q) = r_n(x)` and put
  `h' = h iota(q)^-1`. Then `h' notin iota(J_n)` for large `n`:
  - if `h notin iota(Q)`, then `h' notin iota(Q)`;
  - if `h = iota(q_0)`, then `x != j(q_0)` because `(h,x) notin Q''`. So
    `r_n(x j(q_0)^-1) != 1` for large `n`, that is `r_n j(q) != r_n j(q_0)`, and
    `q_0 q^-1 notin J_n`.

  Now `(h, r_n x) = (h', 1)(iota q, r_n j q)`. The factor `(iota q, r_n jq)` leaves
  `gamma_n` invariant outside a proportion `O(|W_n|^3 epsilon_n)`. The invariance argument
  above applies verbatim to `q in E_n`, because `iota(N_n(q)) <= W_n`. Let
  `alpha' = (iota q, r_n jq).alpha`, a measure-preserving change of variables. Up to the
  multiplicativity errors on `W_n`, `gamma_n((h,x).alpha) != gamma_n(alpha)` iff
  `gamma_n((h',1).alpha') != gamma_n(alpha')`. Write `alpha' = (beta, e)`. The element
  `(h',1)` fixes `e`, and with `beta' = phi_n(iota q_e)^-1 beta` the first entries compare
  `delta_n(phi_n(g) beta')` with `delta_n(beta')`, where
  `g = iota(q_e)^-1 h' iota(q_e) = iota(q_e)^-1 h iota(q)^-1 iota(q_e)`. This is a word of
  length `4` in the generators of `W_n`, so `g in W_n`. Since `J_n` is normal in `Q`, `g`
  lies outside `iota(J_n)` iff `h'` does. So `delta_n` is displaced outside proportion
  `epsilon_n`.

In both cases `gamma_n` changes outside a proportion `O(|W_n|^3 epsilon_n) -> 0`.
Invariance on `Q''` was proved for each fixed `q = q_i`. Together these give (R) for every
fixed `(h,x)`.

So `gamma_n` satisfies (R), and (RSH) holds with `sigma_n, r_n, gamma_n`.

## 5. Assembly

- Section 4 gives (RSH), and with it a sofic approximation of `H_e`.
- [[free-cover-left-right-action-over-sofic-group-is-sofic]] makes the two-sided action
  `F(X_e) x F(X_e) ↷ H_e` sofic. By (R3) of
  [[compiler-rope-edge-is-not-co-amenable]], `Gamma_e` is sofic. This is item 1.
- Section 3 gives (HC_e), and hence item 2.
- [[envelope-coset-action-sofic-once-edge-coset-action-sofic]] (its Consequence: `R_e` is
  sofic when `Gamma_e` and `Gamma_e ↷ Gamma_e/S_e` are) gives item 3. QED.

**Chain remark.** Only the `J_n` of Section 4 were used, which proves the last sentence of
the Theorem.

## 6. Calibration

If `H = P` and `iota = j`, then `iota(J_n) = j(Q) ∩ ker r_n` is separable in `P`, so
(HQ) holds by (C1) of [[separating-sofic-quotient-sets-make-an-action-sofic]], and the
construction specializes to a finite-quotient model. That is consistent: then the rope's
lamps sit over a residually finite hub. The construction never uses that `H` is residually
finite or that `iota(Q)` is separable; it uses only the transitive coset models of `H`.
