# Fibre masses of an amenable subgroup: a Følner Cauchy–Schwarz bound

September 16, 2026 (frontier swarm lane `hi-fron-fpbs-benjamini-schramm-univers`,
working under `fpbs-amenable-wq-normal-relative-subcriticality`). Nothing here is
refereed or formally verified.

## 0. Summary

Let `H` be an amenable subgroup of a finitely generated group `Gamma`, and fix
a Cayley graph of `Gamma` and a parameter `p`. The expected number of points of
`H` in the cluster of a vertex `g` is at most the geometric mean of the relative
susceptibilities of `H` and of `g^(-1) H g` (Theorem A). The proof pairs a
Følner set `F` of `H` with its right translate `F g`, and applies Cauchy–Schwarz
for the positive semidefinite kernel `tau_p`.

For normal `H` this gives `sigma_p(q) <= sigma_p(1) = chi^H_p` for every coset
`q` (Corollary B). It also shows that `sigma_p` is a positive definite function
on `Gamma/H` whenever `chi^H_p < infinity` (Corollary C).

* **Two assertions now have proofs.** Section 4.4 of
  `research/artifacts/fpbs/docs/relative-susceptibility-reduction.md` and the
  Attempts of `fpbs-amenable-wq-normal-relative-subcriticality` asserted this
  inequality with the reason "pushforward of a positive-definite function".
* **A bound that had been withdrawn holds again.** The 2026-09-12 correction to
  Theorem 4.3, Step 3, of
  `research/artifacts/fpbs/docs/fibre-summed-hyperbolic-quotient-criterion.md`
  withdrew the bound `b_j <= |S_Q(j)| (chi^H_p)^2` as "never proved". For
  amenable normal `H` it holds (Corollary E). The corrected proof there does not
  need it.

Two further results. Relative susceptibility is a commensurability invariant
up to constants among amenable subgroups (Corollary D). And there is an
operator-level Simon–Lieb certificate for `p_c < p_(2->2)`, recorded in Section 6
because it explains where certificates of this kind stop.

None of this closes the hole. Section 5 says precisely why.

## 1. Setting and notation

* `Gamma` is a finitely generated group, `S` a finite symmetric generating set,
  and `G = Cay(Gamma,S)` has edges `{x, xs}`. Left multiplication is a graph
  automorphism, and `o` is the identity.
* `tau_p(x,y) = P_p(x <-> y)` for Bernoulli(`p`) bond percolation, with
  `tau_p(x,x) = 1`. Put `phi_p(g) = tau_p(o,g)`. Then
  `tau_p(x,y) = phi_p(x^(-1) y)` and `phi_p(g^(-1)) = phi_p(g)`.
* For `A ⊆ Gamma` put `chi^A_p = sum_(a in A) phi_p(a) = E_p|K_o ∩ A|`, a value
  in `[0, infinity]`.
* For `H <= Gamma` and `g in Gamma`, invariance and symmetry give
  `E_p|K_g ∩ H| = sum_(h in H) phi_p(g^(-1) h) = chi^(g^(-1)H)_p = chi^(Hg)_p`.
* For normal `H` with quotient `Q = Gamma/H`, write `Gamma_q` for the coset `q`
  and `sigma_p(q) = chi^(Gamma_q)_p = E_p|K_o ∩ Gamma_q|`, the fibre mass. So
  `sigma_p(1) = chi^H_p`, the relative susceptibility.

## 2. The connection kernel is positive semidefinite

**Lemma 2.1.** For every `p` and every finitely supported `a : Gamma -> C`,
`sum_(x,y) conj(a_x) a_y tau_p(x,y) >= 0`. Hence, for finitely supported real
`u`, `v`, writing `<u, tau v> = sum_(x,y) u_x tau_p(x,y) v_y`,

```text
|<u, tau v>| <= <u, tau u>^(1/2) <v, tau v>^(1/2).
```

*Proof.* `1{x <-> y} = sum_C 1_C(x) 1_C(y)`, summed over the clusters `C`. Only
finitely many clusters meet the support of `a`, so
`sum_(x,y) conj(a_x) a_y 1{x <-> y} = sum_C |sum_(x in C) a_x|^2 >= 0` pointwise.
Take expectations. The Cauchy–Schwarz inequality holds for any positive
semidefinite symmetric bilinear form. QED.

## 3. Theorem A

**Theorem A.** Let `H <= Gamma` be amenable, `g in Gamma` and `p in [0,1]`.
Then

```text
E_p|K_g ∩ H| = chi^(Hg)_p <= ( chi^H_p · chi^(g^(-1) H g)_p )^(1/2).
```

*Proof.*

**Step 1: Følner sets.** `H` is countable and amenable, so there are finite
nonempty `F_n ⊆ H` with `|F_n m \ F_n| / |F_n| -> 0` for every `m in H`. If `E_n`
are left Følner sets, take `F_n = E_n^(-1)`. For `m in H` put

```text
c_n(m) = #{(h,k) in F_n x F_n : h^(-1) k = m} = |F_n ∩ F_n m^(-1)|.
```

This counts the pairs with `k = hm`, that is `h in F_n ∩ F_n m^(-1)`. Right
multiplication by `m` maps `F_n \ F_n m^(-1)` bijectively onto `F_n m \ F_n`, so

```text
c_n(m) <= |F_n|   and   c_n(m)/|F_n| = 1 - |F_n m \ F_n|/|F_n| -> 1.
```

**Step 2: three pair sums.** Put `u_n = 1_(F_n)` and `v_n = 1_(F_n g)`. Right
multiplication by `g` is injective, so `|F_n g| = |F_n|`. Grouping pairs
`(h,k) in F_n x F_n` by `m = h^(-1) k in H` gives three sums:

```text
<u_n, tau v_n> = sum_(h,k) phi_p(h^(-1) k g)         = sum_(m in H) c_n(m) phi_p(m g),
<u_n, tau u_n> = sum_(h,k) phi_p(h^(-1) k)           = sum_(m in H) c_n(m) phi_p(m),
<v_n, tau v_n> = sum_(h,k) phi_p(g^(-1) h^(-1) k g)  = sum_(m in H) c_n(m) phi_p(g^(-1) m g).
```

Since `c_n <= |F_n|` and `m -> g^(-1) m g` is a bijection `H -> g^(-1) H g`,

```text
<u_n, tau u_n> <= |F_n| chi^H_p,     <v_n, tau v_n> <= |F_n| chi^(g^(-1)Hg)_p.
```

**Step 3: Fatou.** If the right side of the theorem is infinite there is
nothing to prove. Otherwise Step 1, Fatou's lemma and Lemma 2.1 give

```text
chi^(Hg)_p = sum_(m in H) lim_n (c_n(m)/|F_n|) phi_p(m g)
          <= liminf_n <u_n, tau v_n> / |F_n|
          <= liminf_n (<u_n, tau u_n> <v_n, tau v_n>)^(1/2) / |F_n|
          <= (chi^H_p chi^(g^(-1)Hg)_p)^(1/2).
```

QED.

**Remarks.**

1. **What the proof uses.** Only that `phi_p >= 0` is a positive definite
   function on `Gamma`, together with amenability of `H`. The same inequality
   therefore holds for site percolation, for random-cluster measures, and for
   any invariant percolation whose connection function is positive definite
   (every invariant partition gives one, by the argument of Lemma 2.1).
2. **No parameter restriction.** Theorem A holds for every `p`. Above `p_u` both
   sides are infinite for infinite `H`, because `tau_p >= theta(p)^2`.
3. **Orientation.** The pairing needs sets that are asymptotically invariant
   under right multiplication by elements of `H`; inverting left Følner sets
   supplies them. The sets need not be invariant under conjugation by `g`, which
   a twisted lift of a function on `Gamma/H` would require. Normality enters
   only through `g^(-1) H g`.

## 4. Consequences

**Corollary B (the subgroup carries the largest fibre mass).** Let `H` be an
amenable normal subgroup and `Q = Gamma/H`. For every `p` and every `q in Q`,

```text
sigma_p(q) = sigma_p(q^(-1)) <= sigma_p(1) = chi^H_p.
```

So `sup_q sigma_p(q) = chi^H_p`. Equivalently, among all vertices `g`, the
identity maximises `E_p|K_g ∩ H|`.

*Proof.* Normality gives `g^(-1) H g = H` and `Hg = gH = Gamma_q` for `q = gH`,
so Theorem A reads `sigma_p(q) <= chi^H_p`. Symmetry of `phi_p` maps
`Gamma_q` onto `Gamma_(q^(-1))` by inversion. QED.

**Corollary C (positive definiteness on the quotient).** Let `H` be amenable
and normal, with `chi^H_p < infinity`. Then `sigma_p` is a positive definite
function on `Q`: for finitely supported `a : Q -> C`,

```text
sum_(q,q') conj(a_q) a_(q') sigma_p(q^(-1) q') >= 0.
```

*Proof.*

1. **Lift.** Fix a section `s : Q -> Gamma` and Følner sets `F_n` as in Step 1.
   Put `A_n = sum_q a_q 1_(F_n s(q))`. The sets `F_n s(q)` lie in distinct
   cosets, so they are disjoint.
2. **Group the pairs.** For `x = h s(q)` and `y = k s(q')` with `h, k in F_n`,
   write `m = h^(-1) k`. Then `x^(-1) y = c_q(m) g_(q q')`, where
   `c_q(m) = s(q)^(-1) m s(q) in H` and `g_(q q') = s(q)^(-1) s(q')` lies in the
   coset `q^(-1) q'`. Grouping by `m` as in Step 2,

   ```text
   0 <= <A_n, tau A_n> / |F_n|
      = sum_(q,q') conj(a_q) a_(q') sum_(m in H) (c_n(m)/|F_n|) phi_p(c_q(m) g_(q q')).
   ```

   The inequality is Lemma 2.1.
3. **Pass to the limit.** For fixed `(q,q')` the inner sum is dominated by
   `sum_(m in H) phi_p(c_q(m) g_(q q')) = sigma_p(q^(-1) q')`, because `c_q` is a
   bijection of `H`. By Corollary B this is at most `chi^H_p < infinity`, so
   dominated convergence gives the limit `sigma_p(q^(-1) q')`.
4. **Conclude.** The outer sum is finite, and a limit of nonnegative numbers is
   nonnegative. QED.

By the GNS construction, `sigma_p(q) = <pi_p(q) xi_p, xi_p>` for a unitary
representation `pi_p` of `Q` and a vector with `||xi_p||^2 = chi^H_p`. The
fibre-summed operator `S_p = lambda_Q(sigma_p)` of
`fpbs-fibre-summed-connectivity-operator` is the regular convolution by this
positive definite function.

**Corollary D (commensurability invariance).** Let `H <= Gamma` be amenable
and `L <= H` of finite index, and let `L_0` be the normal core of `L` in `H`.
Then for every `p`,

```text
chi^(L_0)_p <= chi^L_p <= chi^H_p <= [H : L_0] chi^(L_0)_p.
```

Hence if amenable `H, H' <= Gamma` are commensurable, `chi^H_p < infinity` if
and only if `chi^(H')_p < infinity`. In particular, for a commensurated amenable
`H` (for example `<a>` in `BS(m,n)`), `chi^H_p < infinity` implies
`E_p|K_g ∩ H| < infinity` for every `g`.

*Proof.* The first two inequalities are monotonicity. Write `H` as the disjoint
union of right cosets `L_0 c_i`, with `c_i in H` and `i <= [H:L_0]`. `L_0` is
amenable and normal in `H`, so `c_i^(-1) L_0 c_i = L_0`. Theorem A in `Gamma`
for `L_0` and `g = c_i` gives `chi^(L_0 c_i)_p <= chi^(L_0)_p`; sum over `i`.
For commensurable `H`, `H'`, apply this to `H ∩ H'` inside each. For
commensurated `H`, `H` and `g^(-1) H g` are commensurable; apply Theorem A. QED.

The last inequality is not elementary. Harris–FKG bounds `tau_p(o, c m)` below,
not above, and `tau_p(o, m^(-1) c m)` is not bounded below uniformly in `m`
unless `c` is central.

**Corollary E (sphere bubbles and fibre bubbles).** Let `H` be amenable and
normal. Fix a word length on `Q`, and put `m_R(p) = sum_(|q|=R) sigma_p(q)`,
`b_R(p) = sum_(|q|=R) sigma_p(q)^2` and `B^H_p = sum_q sigma_p(q)^2`. Then

```text
b_R(p) <= chi^H_p m_R(p) <= |S_Q(R)| (chi^H_p)^2,     B^H_p <= chi^H_p chi_p.
```

*Proof.* Use `sigma_p^2 <= (sup sigma_p) sigma_p`, then Corollary B. QED.

This is the bound that the pre-correction Step 3 of Theorem 4.3 in
`fibre-summed-hyperbolic-quotient-criterion.md` used. It is now proved for
amenable normal `H`. No proof is known here for nonamenable normal `N`.

## 5. What this does not give

### 5.1 Openness of finite relative susceptibility above `p_c`

Section 4.4 of `relative-susceptibility-reduction.md` cites the sprinkling
inequality `T_(p') <= sum_k [eps T_p A]^k T_p`, with `eps = (p'-p)/(1-p)` and
`A` the adjacency operator. The citation there is to arXiv:1804.10191,
Lemma 2.4; I have not re-verified it.

**The fibre-summed row.** `T_p` maps functions constant on cosets to functions
constant on cosets:

```text
(T_p f∘pi)(x) = sum_(q') f(q') sigma_p(pi(x)^(-1) q') = (S_p f)(pi(x)).
```

So summing the `(o,H)` row gives an exact fibre-summed expansion,

```text
chi^H_(p') <= chi^H_p + sum_(k>=1) eps^k <sigma_p, A_Q (S_p A_Q)^(k-1) sigma_p>_(l^2(Q)),
```

where `(A_Q f)(q) = sum_(s in S) f(q pi(s))`. Already the `k = 1` term is
`<sigma_p, A_Q sigma_p> <= |S| B^H_p`.

**Where it stops.** Openness needs the fibre bubble `B^H_p` and the operator
norm `||S_p||` at a parameter `p >= p_c`. Corollary B bounds every entry of
`sigma_p` by `chi^H_p`, but Corollary E only gives `B^H_p <= chi^H_p chi_p`, and
`chi_p = infinity` for `p >= p_c`. So the gap in Section 4.4 is exactly as
stated there: the diagonal controls the entries, not the quadratic coset sum.

### 5.2 The sandwich between L2 and the hole

Let `H` be amenable and normal. By `fpbs-fibre-summed-connectivity-operator`
and Corollary B,

```text
chi^H_p = sigma_p(1) <= sup_q sigma_p(q) <= ||lambda_Q(sigma_p)|| = ||T_p||_(2->2).
```

So `p_c < p_(2->2)` gives the hole at `G`, and the hole at `G` gives
`p_c < p_u` (Theorem 3.1 of `relative-susceptibility-reduction.md`). Since
`p_(2->2) <= p_u`, the hole is strictly weaker than the L2 condition at `G` only
when `p_(2->2)(G) < p_u(G)`.

Hutchcroft and Pan, arXiv:2412.15895 (submitted 2024-12-20; abstract fetched
2026-09-16), prove that `p_(2->2)` coincides with `p_u` for:
* `T x Z^d`;
* products of trees with arbitrary infinite amenable Cayley graphs;
* lamplighters on trees.

The abstract calls these the first nonamenable examples with this property.
Every one of them lies in the class treated here. On these graphs, any proof
of the hole proves `p_c < p_(2->2)`.

**Question Q.** Is `p_(2->2)(G) = p_u(G)` for every Cayley graph `G` of a
nonamenable group with an infinite amenable normal subgroup?

A positive answer would make the hole equivalent, graph by graph, to the L2
condition on this class. Any non-L2 route to the hole must then exploit a graph
with `p_(2->2) < p_u`, and no such graph in the class is known. Trees have
`p_(2->2) < p_u`, but trees are not in the class.

### 5.3 Positive definiteness carries no decay

`sigma_p` is positive definite on `Q` with `sigma_p(1) = chi^H_p` (Corollary C).
A nonnegative positive definite function can have finite diagonal and unbounded
convolution operator: the constant function `1` on `Q` is an example. So
Corollary C cannot upgrade the hole to L2. It also takes `chi^H_p < infinity`
as input, so it cannot produce the hole either.

## 6. Remark: an operator-level Simon–Lieb certificate

This is a known-type argument, recorded to show where certificates of this kind
stop. The closest repo nodes are `fpbs-sphere-cut-fibre-tails-decay-exponentially`
and `fpbs-sphere-fibre-operator-iff-critical-fibre-l2`, which do the same over
fibre-saturated spheres.

**Proposition F.** Let `W ∋ o` be finite, and define

```text
tau^W_p(o,x) = P_p(o <-> x using only edges with both endpoints in W),
mu_(W,p)(y)  = p sum_((x,s) in W x S : xs = y) tau^W_p(o,x)   for y not in W,
```

with `mu_(W,p)(y) = 0` for `y in W`. If `p_1 >= p_c` and
`||lambda_Gamma(mu_(W,p_1))||_(2->2) < 1`, then

```text
||T_(p_c)||_(2->2) <= E_(p_1)|K^W_o| / (1 - ||lambda_Gamma(mu_(W,p_1))||),
```

and hence `p_c < p_(2->2) <= p_u`, by the openness that the sprinkling inequality
of Section 5.1 gives.

*Proof.*

1. **Simon–Lieb.** Condition on the cluster `C` of `o` inside `W`. Every edge
   from `C` to `W \ C` is closed. So `o <-> z` with `z` outside `C` needs an open
   edge `{x, xs}` with `x in C` and `xs` not in `W`, followed by `xs <-> z` off
   `C`. That edge and the off-`C` event are independent of `{C = A}`. For every
   `z` this gives
   `tau_p(o,z) <= tau^W_p(o,z) + sum_y mu_(W,p)(y) tau_p(y,z)`.
2. **Operator form.** By invariance this is the entrywise kernel inequality
   `T_p <= T^W_p + R_mu T_p`, with `(R_mu f)(w) = sum_t mu(t) f(wt)`. Inversion
   `f -> f(.^(-1))` conjugates `R_mu` to `lambda_Gamma(mu)`, so the norms agree.
3. **Norm bound below `p_c`.** For `p < p_c`, `T_p` is bounded, since its row
   sums are `chi_p < infinity`. Nonnegative kernels attain their norm on
   nonnegative vectors, so `||T_p|| <= ||T^W_p|| + ||R_mu|| ||T_p||`. Also
   `||T^W_p|| <= E_p|K^W_o|` by Schur's test.
4. **Monotonicity.** `mu_(W,p)` and `E_p|K^W_o|` are nondecreasing in `p`. So
   for `p < p_c <= p_1`, `||T_p|| <= M`, with `M` the right side of the display.
5. **Limit.** `tau_p(x,y)` is left-continuous in `p`, as a supremum of
   finite-volume connection probabilities. So `<f, T_(p_c) g> <= M ||f|| ||g||`
   for finitely supported nonnegative `f`, `g`. QED.

**Where it stops.**

1. `||mu_(W,p)||_1 = phi_p(W)`, the Duminil-Copin–Tassion quantity. By their
   characterisation `p_c = sup{p : phi_p(W) < 1 for some finite W ∋ o}`
   (arXiv:1502.03050; not re-fetched here) and continuity in `p`,
   `phi_(p_1)(W) >= 1` for `p_1 >= p_c`. So the certificate needs the Kesten
   ratio `||lambda(mu)|| / ||mu||_1` below `1/phi_(p_1)(W)`.
2. Its conclusion is L2, which is stronger than the hole. The converse,
   L2 implying some finite certificate, is not proved here.
3. Using it on a concrete graph needs a rigorous upper bound `p_1` on `p_c` and
   a rigorous spectral-norm bound. That is the numerical wall already recorded
   for the sphere fibre operators.

## 7. Open points

1. **Is amenability needed in Corollary B?** For a nonamenable normal `N`,
   e.g. `N ◁ F_d` with `rho_Q > rho_T` as in
   `research/artifacts/fpbs-tree-relative-cogrowth-2026-09-16.md`, is
   `sigma_p(q) <= chi^N_p`? The Følner pairing has no substitute. The lift
   argument gives positive definiteness of fibre sums only for kernels of the
   form `f * f^*` with `f` finitely supported, and pointwise limits do not
   commute with the infinite coset sums in the needed direction.
2. **Question Q** of Section 5.2.
3. **The fibre bubble.** Openness (Section 5.1) needs the fibre bubble
   `B^H_p = ||sigma_p||^2_(l^2(Q))` and `||S_p||` at some `p >= p_c`. A proof that
   `B^H_(p_c) < infinity` without L2 would still leave `||S_p||`.
