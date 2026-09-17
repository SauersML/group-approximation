---
rg: 2
id: low-degree-view-unique-verifiers-collapse-proof
kind: route
title: Low-degree nonzero functions have dense support, so near-1 completeness pins the weight on exact triples, which read only level-set partitions of the outer relation
target: low-degree-view-unique-verifiers-collapse
requires:
  - low-degree-view-collapse-survives-non-affine-sigma
artifacts:
  - experiments/low-degree-view-collapse-2026-09-17/check_low_degree_collapse.py
---

The notation is that of the target claim. Items 1-6 below are self-contained and
were confirmed by all three referees (2026-09-17). The route requires
`low-degree-view-collapse-survives-non-affine-sigma` only for the claim's
Consequence paragraph, whose list of killed views (Hadamard, Grassmann, quadratic,
Reed--Muller) silently assumes affine `sigma`. Every function
`F_p^m -> F_p` has a unique *reduced* polynomial representative, with every
individual degree at most `p - 1`. Its degree is the reduced degree.
Precomposing with an affine map does not raise it: substitute and reduce with
`x^p = x`, which never increases the degree. So `deg t` does not depend on the
parametrization `phi`.

## Lemma 1 (density lemma)

**Claim.** If `f : F_p^m -> F_p` is nonzero with reduced degree `<= D`, then
`|supp f| >= p^(m-D)`.

**Proof.** Induct on `m`.

* **Base, `m = 0`.** `f` is a nonzero constant, and `|supp f| = 1 >= p^(-D)`.
* **Step.** Write `f = sum_(j=0)^(r) x_m^j g_j(x_1, ..., x_(m-1))` with `g_r != 0`
  and `r <= p-1`. Here `g_r` has reduced degree `<= D - r`, because the monomials
  of `f` have degree `<= D`. Fix `x'` with `g_r(x') != 0`. Then `f(x', .)` is a
  nonzero univariate polynomial of degree `r <= p-1`, so it has at most `r` roots
  and at least `p - r` nonzero values. By induction,
  ```text
  |supp f| >= (p - r) |supp g_r| >= (p - r) p^(m-1-D+r) = p^(m-D) (p - r) p^(r-1) >= p^(m-D),
  ```
  since `(p - r) p^(r-1) >= 1` for `0 <= r <= p-1`. (At `r = 0` it equals `1`.
  For `r >= 1`, `p - r >= 1` and `p^(r-1) >= 1`.)

**Tightness at `p = 2`.** `x_1 ... x_D` has support `2^(m-D)`. Check (DZ) of the
script tests the bound exhaustively on 656 random reduced polynomials over `F_2^5`
and `F_3^3`, and tests the tightness.

**Degree bounds.** Suppose the coordinates of `rho_w, rho_(w')` have degree `<= d`.

* An affine `sigma` keeps `sigma o rho_w` of degree `<= d`.
* Every coordinate of an arbitrary `sigma : F_p^k -> F_p^k` has reduced degree
  `<= k(p-1)`. Substituting polynomials of degree `<= d` and reducing gives degree
  `<= k(p-1)d`.
* Subtracting `rho_(w')` and restricting to the affine subspace `H_e` does not
  raise the degree.

## Lemma 2 (rigidity threshold)

**Rejection floor.** Let `t` be non-exact on `e`. Then `Q_t o phi` is not
identically zero, so some coordinate `q` of it is nonzero with degree `<= deg t`.
`t` rejects `h = phi(u)` whenever `q(u) != 0`, since `Q_t(h) != 0` means
`sigma(rho_w(h_w)) != rho_(w')(h_(w'))`. By Lemma 1 this happens on at least a
`p^(-deg t)` fraction of `F_p^m`, which is also a fraction of `H_e`, because
`phi` is a bijection.

**Weight bound.**

1. Write `d_t` for the acceptance density of `t`. Then
   `c = sum_e mu_e E_(t ~ tau_e) d_t`.
2. Exact triples have `d_t = 1`. Non-exact ones have `d_t <= 1 - p^(-D(V))`.
3. Hence `c <= w_ex + (1 - w_ex)(1 - p^(-D))`.
4. This rearranges to `1 - c >= (1 - w_ex) p^(-D)`, that is,
   `w_ex >= 1 - (1-c) p^D`.

**Attainment.** A same-owner triple with `rho_w = 0`, `rho_(w') = x_1 ... x_D`
(`k = 1`) and `sigma = id` accepts exactly where the monomial vanishes. That is a
`1 - 2^(-D)` fraction. Mixing such triples with exact ones gives equality in
step 3.

Check (R) of the script tests the rejection floor with the measured `deg t` on
4444 triples (seed 20260917) and 4750 triples (seed 7). The views have degree
`<= 3` and the `sigma` are arbitrary. It also tests the weight bound on every
instance. The 93 and 112 non-exact triples with density above `1/2` show that the
affine threshold `1/p` fails for non-affine views, while this bound holds.

## Lemma 3 (exact triples induce partition bijections)

Let `rho-bar_w : A_(o(w))/P_w -> F_p^k` be the injection induced by `rho_w` on
its level sets.

**Cross case.** Let `t = (w, w', sigma)` be exact with `o(w) = a`, `o(w') = b`.
Define `R_t = { (class of h_a in P_w, class of h_b in P_(w')) : h in H_e }`.

1. By exactness, `sigma(rho-bar_w(C)) = rho-bar_(w')(C')` for all `(C, C') in R_t`.
2. `sigma` and `rho-bar_(w')` are injective. So `C'` is determined by `C`, and
   `R_t` lies in the graph of the partial map
   `psi = rho-bar_(w')^-1 o sigma o rho-bar_w`.
3. `H_e` projects onto `A_a`, so every class `C` occurs, `psi` is total, and
   `R_t = graph psi`.
4. `H_e` projects onto `A_b`, so `psi` is onto.
5. `psi` is a composite of injections, so it is injective.

Set `beta_t = psi`. It is a bijection with graph `R_t`, and `R_t` is computed from
`H_e`, `P_w` and `P_(w')` alone. Step 1 gives
`sigma o rho-bar_w = rho-bar_(w') o beta_t`.

**Same-owner case.** Let `o(w) = o(w') = z`. As `h` ranges over `H_e`, `h_z`
ranges over all of `A_z`. So `sigma o rho_w = rho_(w')` on `A_z`. Since `sigma` is
a bijection, `rho_w` and `rho_(w')` have the same level sets, so `P_w = P_(w')`
and `beta_t = id`.

Check (P) of the script tests that `beta_t` is a well-defined bijection onto the
classes on 1054 and 1111 exact triples. These are planted exact cross triples
with polynomial views, plus random ones.

## Theorem (collapse), items (3) and (5)

`Can_part` has vertices `(z, P)`, one for each partition realized by a view owned
by `z`. Its labels are the classes of `P`. Each exact triple `t` gives an edge
from `(o(w), P_w)` to `(o(w'), P_(w'))`, with constraint `beta_t` and weight
`mu_e tau_e(t) / w_ex`. Two exact triples with the same `(e, o(w), P_w, o(w'), P_(w'))`
have the same `beta_t`, by Lemma 3.

**Soundness transfer.**

1. Let `lambda` label `Can_part`, and set `F(w) = rho-bar_w(lambda(o(w), P_w))`.
2. Suppose the `Can_part` edge of an exact triple `t` is satisfied, that is,
   `lambda(o(w'), P_(w')) = beta_t(lambda(o(w), P_w))`.
3. Then `F(w') = rho-bar_(w')(beta_t(u)) = sigma(rho-bar_w(u)) = sigma(F(w))` with
   `u = lambda(o(w), P_w)`. So `V(Phi)` accepts `t`.
4. Summing over the satisfied edges gives `val(V(Phi)) >= w_ex val(Can_part)`.

**Completeness transfer.**

1. Let `x` satisfy the outer edges of weight `1 - eta`. Set
   `lambda(z, P) = class of x_z in P`.
2. On a satisfied edge, `(x_a, x_b) in H_e`, so each exact triple's pair of classes
   lies in `R_t = graph beta_t`, and the edge is satisfied.
3. The exact triples on unsatisfied edges weigh at most `eta` before
   normalization.
4. Hence `val(Can_part) >= (w_ex - eta)/w_ex`.

Check (COL) of the script brute-forces `val(V(Phi))` and `val(Can_part)` on 580
and 621 instances and tests both transfers.

**Reduction, item (5).**

* **Local size.** The label spaces have constant size, `p^l` with `l = l(eps)` as
  in the 2-to-2 theorem. So exactness, the partitions and the `beta_t` are
  computed by brute force over each `H_e`, in constant time per triple.
* **Alphabets.** Vertices of `Can_part` joined by an edge have equally many
  classes (each `beta_t` is a bijection), and every class count is at most
  `N = p^l`. The output is a unique game in label-cover form: per-vertex
  alphabets of size at most `N`, equal along edges, with bijection constraints.
  Item (5) is asserted for this form of Gap-UG. No dummy padding is used: naive
  padding (extending `beta_t` by the identity on dummy labels) can raise the
  value, because an all-dummy labeling satisfies every padded edge.
* **Parameters.** By Lemma 2, `w_ex >= 1 - theta`. So YES gives
  `val(Can_part) >= 1 - eta/(1-theta)`. NO gives
  `val(Can_part) <= val(V(Phi))/w_ex <= s/(1-theta)`.

## Item (4) (branch blindness)

Let `H_e = { T x_a + T' x_b in b + <c> }`, `c != 0`, and let `t` be exact with `w`
on `a` and `w'` on `b`.

1. For each `x_a`, both `(x_a, y)` and `(x_a, y + T'^-1 c)` lie in `H_e`, where
   `y = T'^-1(b + T x_a)`, and every `x_b` occurs this way.
2. Exactness gives `rho_(w')(y) = sigma(rho_w(x_a)) = rho_(w')(y + T'^-1 c)`.
3. Symmetrically, `rho_w(x + T^-1 c) = rho_w(x)`.

So the classes of `P_w` and `P_(w')` are unions of branch cosets. The branch
`H^s` is `H^0 + (s T^-1 c, 0)`, a translation that preserves every class of
`P_w`. So all branches have the same image `R_t`. Each branch has onto
projections, since `T, T'` are invertible. So `beta_t`, and hence `Can_part`, is
the same whichever branch replaces `H_e`. Check (P) tests both invariances on the
837 and 890 exact cross triples.

## Item (6) (necessary degree)

`val(V(Phi)) >= w_ex val(Can_part) >= w_ex lambda`, so `w_ex <= s/lambda`. By
Lemma 2, `1 - s/lambda <= 1 - w_ex <= eps p^D`, which gives the stated bound.

## Verification

`nice -n 10 timeout 1200 python3 experiments/low-degree-view-collapse-2026-09-17/check_low_degree_collapse.py [seed]`
exits `0` for seeds `20260917` (default) and `7`, in under 10 seconds each.
