---
rg: 2
id: linear-view-unique-verifiers-collapse-proof
kind: route
title: Agreement sets of affine maps are subspaces, so exact triples carry all the weight above 1/p and read only the outer quotient relation
target: linear-view-unique-verifiers-collapse-to-quotient-coarsening
requires: []
artifacts:
  - experiments/linear-view-collapse-2026-09-17/check_collapse.py
---

Notation is as in the target claim. For a triple `t = (w, w', sigma)` on the
edge `e = (a,b)`, write `h_w` for the coordinate of `h in H_e` that `w` reads,
which is the coordinate of its owner. Put `f(h) = rho_w(h_w)` and
`g(h) = rho_(w')(h_(w'))`. Both are affine maps `H_e -> F_p^k`. The accepted set
is `S_t = { h in H_e : sigma(f(h)) = g(h) }`, and its density is
`d_t = |S_t| / |H_e|`. So `c = sum_e mu_e E_(t ~ tau_e) d_t`, and `t` is exact iff
`d_t = 1`. For an affine map `rho`, `ker rho` is the kernel of its linear part,
and `rho-bar : A/K -> F_p^k` is the induced injection.

## Lemma 1 (rigidity threshold)

**(a) Affine `sigma`.** The map `h -> sigma(f(h)) - g(h)` is affine on `H_e`, and
`S_t` is the preimage of `0`. So `S_t` is empty or a coset of the kernel of the
linear part, and `d_t` is `0` or `p^(-j)`, where `j` is the rank of the linear
part. In particular, `d_t > 1/p` forces `j = 0` and hence `d_t = 1`.

**Weight bound.** Every non-exact triple has `d_t <= 1/p`. Hence
`c <= w_ex + (1 - w_ex)/p`, which rearranges to `w_ex >= (pc-1)/(p-1)`.

The bound is attained by a mixture of weight `w` of exact triples with triples of
density `1/p`, because then `c = w + (1-w)/p`.

**(b) Arbitrary bijection `sigma` (Lemma 1').** Let `K_f, K_g <= L(H_e)` be the
kernels of the linear parts of `f` and `g` on the direction space of `H_e`.

1. Partition `H_e` into the fibres `h + K_f` of `f`.
2. On one fibre `f` is constant, say equal to `y`. So the accepted part of that
   fibre is `{ k in K_f : g(h+k) = sigma(y) }`.
3. The restriction of `g` to `h + K_f` is affine, and its linear kernel is
   `K_f cap K_g`. So the accepted part is empty or a coset of `K_f cap K_g`.
   Its fraction of the fibre is at most `1/[K_f : K_f cap K_g]`.
4. Summing over fibres gives `d_t <= 1/[K_f : K_f cap K_g]`.

The same argument with `sigma^-1` and the roles of `f, g` swapped gives
`d_t <= 1/[K_g : K_f cap K_g]`. These indices are powers of `p`. So `d_t > 1/p`
forces both indices to be `1`, that is, `K_f = K_g`. This proves (1) of the
claim. Check (L1)/(L2) of the script tests both parts.

## Lemma 2 (exact triples are induced by `Phi`)

Let `t` be exact, and let `K = ker rho_w` and `K' = ker rho_(w')`. Define

```text
R_t = { (h_w + K, h_(w') + K') : h in H_e }  <=  A_(o(w))/K  x  A_(o(w'))/K'.
```

`R_t` depends only on `H_e`, on which coordinates the two views read, and on
`K, K'`. It does not depend on `sigma` or on the offsets of the views.

**Cross case, `o(w) != o(w')`.**

1. Exactness says `sigma(rho-bar_w(u)) = rho-bar_(w')(u')` for every
   `(u, u') in R_t`.
2. The maps `rho-bar_(w')` and `sigma` are injective. So `R_t` lies in the graph
   of the partial map `psi = rho-bar_(w')^-1 o sigma o rho-bar_w`, which is
   defined where `sigma(rho-bar_w(u))` lies in `Im rho_(w')`.
3. The projection of `H_e` onto `A_(o(w))` is onto, so the first projection of
   `R_t` is all of `A_(o(w))/K`. So `psi` is defined everywhere, and
   `R_t = graph psi`: each `u` occurs in some pair, and that pair must be
   `(u, psi(u))`.
4. The second projection of `H_e` is onto as well, so `psi` is onto.
5. `psi` is a composition of injections, so it is injective.

Hence `beta_t := psi` is a bijection whose graph is `R_t`. So `beta_t` is
determined by `R_t` alone. `R_t` is the image of the affine space `H_e` under an
affine map, so it is an affine subspace, and `beta_t` is affine.

**Intra-owner case, `o(w) = o(w') = z`.** As `h` ranges over `H_e`, the common
coordinate `h_w = h_(w')` ranges over all of `A_z`. So exactness says
`sigma o rho_w = rho_(w')` on `A_z`.

* Composing with the bijection `sigma` does not change the kernel of the linear
  part. So `K = K'`.
* `R_t` is the diagonal of `A_z/K`, so `beta_t = id`.

Check (NF) of the script tests that `beta_t` is a well-defined bijection.

## Theorem 1 (collapse)

`Can = Can(Phi, V)` has vertices `(z, K)` and labels `A_z/K`. Each exact triple
`t` of `tau_e` gives an edge from `(o(w), K)` to `(o(w'), K')`. Its constraint is
`beta_t` and its weight is `mu_e tau_e(t) / w_ex`. Triples with the same data
`(e, o(w), K, o(w'), K')` give the same `beta_t`, by Lemma 2.

**Soundness transfer.**

1. Let `lambda` be an optimal labeling of `Can`, and set
   `F(w) = rho-bar_w(lambda(o(w), K_w))`.
2. Take an exact triple `t` whose `Can` edge `lambda` satisfies. Let
   `u = lambda(o(w), K)`, so that `beta_t(u) = lambda(o(w'), K')`.
3. By step 2 of Lemma 2, `rho-bar_(w')(beta_t(u)) = sigma(rho-bar_w(u))`. This
   says `F(w') = sigma(F(w))`, so `V(Phi)` accepts `t`.
4. Summing over the satisfied edges of `Can` gives
   `val(V(Phi)) >= w_ex val(Can)`.
5. Lemma 1 gives `w_ex >= (pc-1)/(p-1)`.

If `w_ex = 0`, the statement is vacuous.

**Completeness transfer.**

1. Let `x` satisfy outer weight `1 - eta`, meaning `(x_a, x_b) in H_e` on edges
   of total `mu`-weight `1 - eta`. Set `lambda(z, K) = x_z + K`.
2. On a satisfied edge `e`, each exact triple has `(x_a + K, x_b + K') in R_t`,
   which is the graph of `beta_t`. So `lambda` satisfies the edge.
3. The triples on unsatisfied edges have total weight at most `eta` before
   normalization.
4. Hence `val(Can) >= 1 - eta/w_ex >= 1 - eta (p-1)/(pc-1)`, for `c > 1/p`.

This proves (3). Check (NF) of the script tests the inequality by brute force on
400 instances.

## Corollary 4 (equivalence)

**Forward direction.** Suppose an explicit polynomial-size verifier `V(Phi)` has
oblivious completeness `c >= c_0 > 1/p` and satisfies:

* YES: `val(Phi) >= 1 - eta` implies `val(V(Phi)) >= c_G`;
* NO: `val(Phi) <= s_Phi` implies `val(V(Phi)) <= s`.

Exactness of a triple is decided by linear algebra: evaluate `sigma o f - g` on
an affine basis of `H_e`. The kernels and the relations `R_t` are computed the
same way. So `Phi -> Can(Phi, V)` runs in polynomial time. Theorem 1 then gives:

* YES: `val(Can) >= 1 - eta (p-1)/(pc-1)`;
* NO: `val(Can) <= val(V(Phi))/w_ex <= s (p-1)/(pc-1)`.

This uses only the oblivious `c`, not `c_G`.

Vertices of `Can` can have different alphabet sizes `p^d`. An edge joins only
vertices of equal size, because `beta_t` is a bijection. To get one alphabet
`F_p^D`, replace each `beta_t` by `beta_t x id` on `F_p^d x F_p^(D-d)`.

* A labeling of `Can` extended by a constant padding satisfies the same edges.
* Projecting a padded labeling onto the first factor satisfies at least as many.

So the value is unchanged.

**Converse.** `Can(Phi, V)` is itself an affine-view verifier:

* the views are the quotient maps `A_z -> A_z/K`, identified linearly with
  `F_p^d` and padded;
* the triples are the exact triples, with `sigma` the affine bijection
  `beta_t x id`.

Every triple is exact, so `c = 1`, and its own `Can` is itself. So "an
affine-view verifier with `c > 1/p` proves near-1 Gap-UG from `Phi`" and "a
quotient coarsening of `Phi` (a choice of kernels on edge endpoints for which
`R_t` is a bijection graph) proves it" are equivalent. This proves (4).

## Corollary 5 (branch blindness)

Let `H_e = { (x_a, x_b) : T x_a + T' x_b in b + <c> }` with `c != 0`, and let `t`
be an exact cross triple with `w` on `a` and `w'` on `b`.

1. If `(x_a, x_b) in H_e`, then `(x_a + T^-1 c, x_b) in H_e`, since the constraint
   value moves by `c`.
2. Both `(x_a + K, x_b + K')` and `(x_a + T^-1 c + K, x_b + K')` lie in `R_t`, the
   graph of the bijection `beta_t`.
3. The second coordinate determines the first, so `T^-1 c in K`.

Symmetrically, `T'^-1 c in K'`. So `|A_a/K| <= p^(l-1)`.

Moreover, `H_e` is the union of the branches
`H^s = { T x_a + T' x_b = b + s c }`. Each branch is the translate of `H^0` by
`(s T^-1 c, 0)`, which vanishes modulo `K`. So every branch has the same image
`R_t` in the quotients. Each branch also has onto projections. So the constraint
of `Can` is the same whichever branch replaces `H_e`. Intra-owner triples
contribute `beta = id` and read nothing about `e`. This proves (5). Check (NF)
tests `T^-1 c in K` and `T'^-1 c in K'` on 252 exact cross triples (seed 7).

## Tightness

The split verifier behind `unique-games-hard-at-completeness-one-half` works as
follows (for `p = 2`):

* the views are identity views `rho_z = id` on `A_z = F_2^l`;
* each 2-to-2 edge carries the two branch triples `sigma_s(x_a) = T'^-1(b + s c + T x_a)`,
  `s in {0, 1}`, with weight `1/2` each.

Each branch is half of `H_e`, so every triple has density `1/2`. So `c = 1/2` and
`w_ex = 0`. That claim proves the verifier sound. So no bound `w_ex >= f(c) > 0`
can hold at `c = 1/2`, and the threshold `1/p` of Lemma 1 cannot be lowered for
`p = 2`. This proves (6).

## Verification

`nice -n 10 timeout 1200 python3 experiments/linear-view-collapse-2026-09-17/check_collapse.py [seed]`
exits `0` for seeds `12345` and `7`. It checks:

* (L1)/(L2) on 3000 random affine configurations;
* (NF) on 400 random composed instances, with outer 2-to-2 and projection games
  and random affine views: the weight bound, equal kernels at intermediate
  density, well-definedness of `beta`, branch blindness, and the brute-force
  collapse inequality.
