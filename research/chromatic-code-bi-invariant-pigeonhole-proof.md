---
rg: 2
id: chromatic-code-bi-invariant-pigeonhole-proof
kind: route
title: Colour the certificate words by a finite net of any totally bounded bi-invariant target
target: chromatic-codes-kill-marks-in-every-bi-invariant-approximation
requires: []
---

Direct proof.  No imported theorem is used.  The three certificate
hypotheses are quoted verbatim from their established nodes (listed in the
claim), and only their hypotheses are used, not their conclusions.

## 0. Two facts about bi-invariant metrics

Let `d` be a bi-invariant metric on a group `K` and write `|g|=d(g,1)`.

- (M1) `|g^(-1)|=|g|` and `|x g x^(-1)|=|g|` for all `x`.
- (M2) `|gh|<=|g|+|h|`.  More generally, `d(ab,cd)<=d(a,c)+d(b,d)`.

Both follow from `d(xgy,xhy)=d(g,h)`.  For instance,
`d(ab,cd)<=d(ab,cb)+d(cb,cd)=d(a,c)+d(b,d)`.

**Area lemma.**  Suppose a free word `q` is a product of at most `A`
conjugates of elements of `R union R^(-1)`.  Then for every tuple `sigma`,

```text
|q(sigma)| <= A Def_R(sigma).
```

Evaluation at `sigma` is a homomorphism from the free group, so
`q(sigma)=prod g_k(sigma) r_k(sigma)^(eps_k) g_k(sigma)^(-1)`.  Apply (M2),
then (M1).  The lengths of the conjugators never enter.

## 1. (BI1) for the commutator code

Fix a target `(K,d)`, a tuple `sigma`, and `eps=Def_R(sigma)`.  Write
`C_v=c_v(sigma)`, `H_v=h_v(sigma)`, `A_v=a_v(sigma)`, `Z=z(sigma)`.

`(CCC1)` states that `[c_v,h_v](a_v z a_v^(-1))^(-1)` has area at most
`A_Delta`, so the area lemma gives

```text
d([C_v,H_v], A_v Z A_v^(-1)) = |[C_v,H_v](A_v Z A_v^(-1))^(-1)| <= A_Delta eps.   (1)
```

`(CCC2)` gives, on every oriented edge `(v,w)`,

```text
|[C_w,H_v]| <= A_0 eps.                                               (2)
```

Fix `delta>0`.  By total boundedness, `K` is covered by finitely many sets
`B_1,...,B_N`, each of `d`-diameter less than `delta`.  Colour each vertex
`v` by the least `i` with `C_v in B_i`.  This is a colouring with at most
`N` colours, and the graph has infinite chromatic number.  So some edge is
monochromatic, and since `(CCC2)` holds for both orientations we may write
it as `(v,w)` with

```text
d(C_v,C_w) < delta.
```

The commutator is 2-Lipschitz in its first variable.  By (M1)-(M2),

```text
d([C_v,H],[C_w,H]) = d(C_v H C_v^(-1), C_w H C_w^(-1))
                  <= d(C_v H C_v^(-1), C_v H C_w^(-1)) + d(C_v H C_w^(-1), C_w H C_w^(-1))
                  = d(C_v^(-1),C_w^(-1)) + d(C_v,C_w) = 2 d(C_v,C_w).
```

Here the final factor `H^(-1)` of both commutators is cancelled by right
invariance, and `d(g^(-1),h^(-1))=d(h,g)` by bi-invariance.  So

```text
|Z| = |A_v Z A_v^(-1)|
   <= d(A_v Z A_v^(-1),[C_v,H_v]) + d([C_v,H_v],[C_w,H_v]) + |[C_w,H_v]|
   <= (A_Delta + A_0) eps + 2 delta.
```

Since `delta>0` was arbitrary, `|z(sigma)|<=(A_Delta+A_0)Def_R(sigma)`.

If `K` is finite, take `delta` smaller than the least nonzero distance.  The
cover is then by singletons, the monochromatic edge is an exact collision
`C_v=C_w`, and the `2 delta` term never appears.  No Lipschitz estimate is
needed at all.

The same computation works for the other convention `[c,h]=c^(-1)h^(-1)ch`.
Only the two-sided cancellation changes.

## 2. (BI1) for the conjugacy-difference code

`(CDC2)` states that `b_v^(-1) b_w a_(v,w) z^(-1) a_(v,w)^(-1)` has area at
most `A`.  Put `B_v=b_v(sigma)` and `D=a_(v,w)(sigma)`.  Colour `v` by a net
cell containing `B_v`, as in Section 1.  This gives an edge with
`d(B_v,B_w)<delta`, hence `|B_v^(-1)B_w|<delta`.  By right invariance,
`d(x,yx)=|y|`, so

```text
|Z| = |D Z^(-1) D^(-1)|
   <= d(D Z^(-1) D^(-1), B_v^(-1)B_w D Z^(-1) D^(-1)) + |B_v^(-1)B_w D Z^(-1) D^(-1)|
   <  delta + A eps.
```

Let `delta->0` to get `|z(sigma)|<=A Def_R(sigma)`.

## 3. (BI1) for the Carmichael section

Here the graphs `Lambda_n` are finite and `chi(Lambda_n)->infinity`, and
`u_v` is the free word `h_v z h_v^(-1)`.  Given `delta`, choose `n` with
`chi(Lambda_n)>N`, the size of a `delta`-net partition of `K`.  Colour by
`U_v=u_v(sigma)`.  This gives an edge `vy` with `d(U_v,U_y)<delta`.  (The edge endpoint is
called `y` here, not `z` as in the quoted node, to avoid a clash with the
mark.)

By (M2), replacing the two factors `U_y` by `U_v` gives

```text
d((U_vU_y)^2, U_v^4) < 2 delta.
```

The area lemma, applied to `(BHC2)-(BHC3)`, gives

```text
|U_v^3| <= L eps,      |(U_vU_y)^2| <= L eps.
```

So

```text
|U_v| = |U_v^4 U_v^(-3)| <= |U_v^4| + |U_v^3| <= 2L eps + 2 delta.
```

Finally `|z(sigma)|=|h_v(sigma) z(sigma) h_v(sigma)^(-1)|=|U_v|` by (M1).
Let `delta->0`.

## 4. (BI2): local almost-homomorphisms

Let `F`, `phi_n` be as in (BI2), and put

```text
eta_n = max_(g,h in F) d_n(phi_n(gh), phi_n(g)phi_n(h)) -> 0.
```

Only pairs with `gh in F` are used below: `1*1`, `s*s^(-1)`, and
prefix-times-letter.  So the variant definitions that require
almost-multiplicativity only when `gh in F` are also covered.

Set `sigma_n(s)=phi_n(s)` for `s in S`, and drop the index `n`.

- (a) From `d(phi(1),phi(1)phi(1))<=eta`, left cancellation gives
  `|phi(1)|<=eta`.
- (b) From `d(phi(1),phi(s)phi(s^(-1)))<=eta` and (a),
  `|phi(s)phi(s^(-1))|<=2eta`.  So `d(phi(s^(-1)),phi(s)^(-1))<=2eta`.
  Thus for every letter `y in S union S^(-1)`, `d(phi(y), y(sigma))<=2eta`.
- (c) Let `w=y_1...y_l` be a word whose prefix images `g_j` all lie in `F`,
  with `w_j` its prefix of length `j`.  Then
  `d(phi(g_j), w_j(sigma))`
  `<= d(phi(g_j), phi(g_(j-1))phi(y_j)) + d(phi(g_(j-1))phi(y_j), w_(j-1)(sigma) y_j(sigma))`
  `<= eta + d(phi(g_(j-1)), w_(j-1)(sigma)) + 2eta`,
  using (M2) in the last step.  Starting from (a), this gives
  `d(phi(g_l), w(sigma)) <= (3l+1) eta`.
- (d) Each relator `r` has image `1`, so
  `|r(sigma)| <= (3|r|+1)eta + |phi(1)| <= (3|r|+2)eta`.  Hence
  `Def_R(sigma_n) <= (3 rho+2) eta_n`, where `rho` is the largest relator
  length.
- (e) By (c) and (BI1),

  ```text
  |phi_n(z)| <= (3|z|+1) eta_n + |z(sigma_n)| <= (3|z|+1+C(3 rho+2)) eta_n -> 0.
  ```

  This is `(BI2)`.  The targets `K_n` may be different for different `n`,
  and they may be arbitrary finite groups.  No uniformity in `n` is needed,
  because the net in Sections 1-3 is chosen after the target.

## 5. (BI3): metric ultraproducts

Let `(K_n,d_n)` be targets whose diameters are uniformly bounded, and let

```text
K_U = prod K_n / N_U,      N_U = {(x_n) : lim_U d_n(x_n,1)=0}.
```

Bi-invariance makes `N_U` a normal subgroup.  Let `pi:Gamma->K_U` be a
homomorphism, and lift `pi(s)` to sequences `sigma_n(s)`.  Evaluation
commutes with the quotient.  So `r(sigma_n)` represents `pi(r)=1` for each
of the finitely many relators, and hence `lim_U Def_R(sigma_n)=0`.  By
(BI1), `lim_U |z(sigma_n)|=0`.  Since `z(sigma_n)` represents `pi(z)`, we get
`pi(z)=1`.

Instances.

- Normalized Hamming metrics on `Sym(n)` give the sofic radical.
- Normalized rank metrics `rank(A-B)/n` on `GL_n(F_q)` give the finite-field
  linear-sofic radical.  These metrics are bi-invariant, because
  `rank(XAY-XBY)=rank(A-B)` for invertible `X,Y`.
- Arbitrary bi-invariant metrics on finite groups give the weakly sofic
  radical.
- Normalized Hilbert--Schmidt distance on `U(n)`, a compact bi-invariant
  metric group, gives the hyperlinear radical.

The MF radical is the established operator-norm case for the two codes,
`infinite-chromatic-commutator-code-kills-mf-mark` and
`bounded-area-conjugacy-difference-code-kills-mf-mark`.

For the Carmichael section, apply (BI1) to `(U(d_n), operator norm)` along
coordinate unitary lifts of a corona homomorphism, exactly as in the last
paragraph of `infinite-chromatic-commutator-code-proof`.  The lifts have
operator-norm defect tending to `0`, hence so does `z`.

The complex rank metric on `GL_n(C)` is bi-invariant but not totally
bounded: at every scale below `1/n` it is discrete on an uncountable set.
So complex linear soficity is **not** covered, and the pigeonhole genuinely
fails there.

## 6. (BI4) and (BI5)

**Weak soficity.**  Glebsky--Rivera weak soficity (J. Algebra 320 (2008),
Definition 4.1) gives, for a group `G`, the following.  For every finite
`F subset G` and every `eps>0` there are a finite group `H` with a
bi-invariant metric and a map `phi:G->H`, `eps`-multiplicative on `F`,
with `d(phi(g),1)>=alpha` for every `g in F` other than `1`.  Here
`alpha>0` does not depend on `eps`.

Only this consequence is used.  It holds whether `alpha` is uniform or is
allowed to depend on `F`, and whatever the normalization of the metric.  So
the argument is robust to the variants of the definition in the literature.

Suppose `z!=1` in `Gamma` and `Gamma` is weakly sofic.  Take `F` as in
(BI2); it contains the image of `z`.  Taking `eps=1/n` gives maps `phi_n`
with `eta_n->0` and `d_n(phi_n(z),1)>=alpha`.  This contradicts (BI2).

**Hyperlinearity.**  A hyperlinear `Gamma` embeds in a metric ultraproduct
of `(U(n), normalized HS)`.  By (BI3) the embedding kills `z`, so `z=1`.

Hence a certificate at a nontrivial `z` in a finitely presented `Gamma`
exhibits a countable, explicitly presented group that is neither weakly
sofic nor hyperlinear.  This is the content of the roots
`non-weakly-sofic-group-exists` and `non-hyperlinear-group`.

**(BI5)** is the contrapositive of (BI2) and (BI3).  If `Gamma` has maps as
in (BI2) with `limsup d_n(phi_n(z),1)>0`, or an ultraproduct homomorphism
not killing `z`, then no certificate exists at `z`.  In the Carmichael case,
this means `max Area((u_vu_y)^2)` or `max Area(u_v^3)` is unbounded along
every family with `chi->infinity`.  In the code cases, `A_Delta` or `A_0` is
unbounded on every infinite-chromatic graph.

## 7. What the proof isolates

- **The invariant.**  The only invariant used is the cost bound of the area
  lemma.  Distance to `1` in a bi-invariant metric is subadditive and
  conjugation-invariant, so a relation of bounded area is charged
  independently of its conjugators.
- **The one target-dependent step.**  Only the pigeonhole depends on the
  target, and it needs just finitely many colours at each fixed scale.
  - These are the two features shared by every finite group, by `U(n)` with
    either norm, and by every compact group with a bi-invariant metric.
  - So no chromatic certificate can separate MF from hyperlinear, sofic or
    weakly sofic approximation.  Whatever mark it kills, it kills in all of
    them at once.

**Remark (finite quotients, not used).**  For an exact homomorphism `q` from
the free group to a finite group `Q`, Section 1 gives an exact collision.
It shows that `q(z)` is a product of at most `C` conjugates of elements
`q(r)^(+-1)` with `r in R`, in one of at most `(2|R|)^C` orders of factor
types.  Conjugates can be reordered at the cost of re-conjugating.  So only
the multiset of relator types varies with `Q`, and it ranges over a finite
set.

This is a bounded-width statement of the kind in the Glebsky--Rivera word
certificate, but with a `Q`-dependent multiset.  Whether it can be made to
match their fixed list exactly is not needed, because (BI4) is proved
directly from the metric definition.
