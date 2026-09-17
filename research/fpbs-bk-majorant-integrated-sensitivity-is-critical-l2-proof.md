---
rg: 2
id: fpbs-bk-majorant-integrated-sensitivity-is-critical-l2-proof
kind: route
title: FKG insertion bounds diagonal kernel powers by the majorant, even trace powers bound finite sections, and uniqueness makes every supercritical sum diverge
target: fpbs-bk-majorant-integrated-sensitivity-is-critical-l2
requires:
  - fpbs-cluster-count-trichotomy
---

Complete written proof. No computation is used. Notation as in the claim.

**Standard imports** (textbook statements for Bernoulli bond percolation on a
finite edge set, as in G. Grimmett, *Percolation*, 2nd ed., Springer 1999,
Sections 2.2--2.4, recalled; BK is used the same way in the ESTABLISHED
`fpbs-critical-l2-equivalent-to-dyadic-projection-estimate-proof`):

- **Harris-FKG.** Increasing events `A,B` satisfy `P_p(A cap B) >= P_p(A)P_p(B)`.
  By monotone limits this also holds for increasing events on an infinite
  graph.
- **Russo's formula.** For an increasing event `A` depending on finitely many
  edges, `d/dp P_p(A) = sum_e P_p(e is pivotal for A)`.
- **BK inequality.** For increasing events `A,B` on a finite edge set,
  `P_p(A o B) <= P_p(A) P_p(B)`, where `A o B` is disjoint occurrence.

Part (3) also uses `fpbs-cluster-count-trichotomy` (ESTABLISHED, imported):
for `p>p_u` there is a unique infinite cluster a.s.

Throughout, `G` is `Gamma`-invariant: `tau_p(gx,gy)=tau_p(x,y)`, and
`tau_p(x,y)=tau_p(y,x)`. Every kernel is nonnegative, so the entries of
products are well defined in `[0,infinity]`, products are associative, and
products are monotone in each factor entrywise (Tonelli).

## Step 1. Two FKG insertion bounds

Fix `p in (0,1]`.

**(1a)** For all `x,y` and `s in S`, `tau_p(x,ys) >= p tau_p(x,y)`.
Indeed `{x<->ys}` contains `{x<->y} cap {edge (y,ys) open}`, an intersection
of two increasing events, and Harris-FKG applies. Averaging over `s` gives
`(T_p P)(x,y) >= p tau_p(x,y)`, and by symmetry `(P T_p)(x,y) >= p tau_p(x,y)`.
So, entrywise, `P T_p >= p T_p` and

```text
T_p (P T_p)^k >= p^k T_p^(k+1)          (k >= 0).                   (1.1)
```

**(1b)** For all `z,x`, `tau_p(z,x) >= p^|x| tau_p(z,o)`, where `|x|` is the
word length. The event `{z<->x}` contains the intersection of `{z<->o}` with
the event that a fixed geodesic path from `o` to `x` is open, and Harris-FKG
applies. Hence for any kernel `L>=0`, `(L T_p)(o,x) >= p^|x| (L T_p)(o,o)`.

## Step 2. Diagonal powers from the majorant

Take `p=p_c`, `T=T_(p_c)`, and suppose `M_n(delta)<infinity`. Since
`P^n(o,x)>0` only for `|x|<=n` and `sum_x P^n(o,x)=1`, (1b) applies with
`L=T(PT)^(k-1)P` for `k>=1`, and with `L=I` for `k=0`. Then (1.1) gives

```text
A_n^(k) >= p_c^n [T(PT)^k](o,o) >= p_c^(n+k) T^(k+1)(o,o).
```

Hence `T^(k+1)(o,o) <= K_0 (d delta p_c)^(-k)`, where
`K_0 = p_c^(-n) M_n(delta) < infinity`.

## Step 3. Operator norm from diagonal powers

**Lemma.** For a symmetric `Gamma`-invariant kernel `K>=0` on `Gamma` with
`K(o,o)>0` (for `K=T_p`, `K(o,o)=1`),
`||K||_(2->2) = limsup_m (K^m(o,o))^(1/m)` in `[0,infinity]`.

*Proof of `<=`.* For finite `F`, let `K_F=1_F K 1_F`. If some entry of `K`
`K(o,z)` is infinite, then for even `m>=2`,
`K^m(o,o) >= K(o,z)K(z,o)K(o,o)^(m-2) = infinity`, and there is nothing to
prove. Otherwise `K_F` is a real symmetric `|F| x |F|` matrix with real
eigenvalues `mu_i`, and for even `m`,

```text
||K_F||^m = max_i |mu_i|^m <= sum_i mu_i^m = tr(K_F^m) = sum_(x in F) K_F^m(x,x)
          <= sum_(x in F) K^m(x,x) = |F| K^m(o,o).
```

The last two steps use entrywise monotonicity `K_F^m <= K^m` and invariance.
Letting `m -> infinity` along even integers gives
`||K_F|| <= limsup_m (K^m(o,o))^(1/m) =: r`. For finitely supported
`f,g` with support in `F`, `|<Kf,g>| <= <K_F|f|,|g|> <= r ||f|| ||g||`.
So `K` defines a bounded operator with `||K|| <= r`.

*Proof of `>=`.* If `||K||=M<infinity`, then
`K^m(o,o) = <K^m delta_o, delta_o> <= M^m`. ∎

Applying the Lemma to `T` with Step 2 gives
`||T_(p_c)||_(2->2) <= limsup_k (K_0 (d delta p_c)^(-k))^(1/(k+1)) = 1/(d delta p_c)`.
This proves part (1), including the displayed inequality
`p_c^(k+n) T^(k+1)(o,o) <= A_n^(k)`.

**Radius independent of `n`.** Step 2 gives `A_n^(k) >= p_c^n A_0^(k)`.
Symmetrically, `tau(z,o) >= p_c^|x| tau(z,x)` by (1b) applied to the
symmetric kernel, so `A_0^(k) >= p_c^n A_n^(k)`. Hence
`limsup_k (A_n^(k))^(1/k)` is the same for all `n`, and so is the radius
`delta_*` of `M_n`.

## Step 4. Critical l2 gives the majorant (part 2)

Assume `||T||=M<infinity`.

**(4a) Series bound.** For bounded nonnegative kernels, kernel products are
operator compositions. With `P^n(x,o)=P^n(o,x)`,

```text
A_n^(k) = [T (PT)^k P^n](o,o) = <T (PT)^k P^n delta_o, delta_o> <= M^(k+1) rho^n.
```

So `M_n(delta) <= M rho^n/(1-d delta M)` for `d delta M<1`. Together with
part (1), this gives `1/(dM) <= delta_* <= 1/(d p_c M)`. If `M=infinity`,
part (1) gives `M_n(delta)=infinity` for every `delta>0`, so `delta_*=0`.

**(4b) Truncated Russo-BK inequality.** Let `B_R` be the ball of radius `R`
about `o` and `E_R` the edges with both endpoints in `B_R`. For
`x,y in B_R`, let `tau^R_p(x,y)` be the probability that `x,y` are joined by
an open path in `E_R`, with kernel `T^R_p` on `B_R`. It is a polynomial in
`p`. Let `P_R(u,v)=1/d` if `u,v in B_R` are adjacent, and `0` otherwise.

For `x != y`, suppose `e={u,v} in E_R` is pivotal for `{x<->y in E_R}`.
Then with `e` closed, the open clusters of `x` and `y` in `E_R\{e}` are
disjoint and contain different endpoints of `e`. Hence the configuration
lies in `{x<->u} o {v<->y}` or in `{x<->v} o {u<->y}`, the events taken in
`E_R\{e}`. BK and monotonicity in the edge set give
`P(e pivotal) <= tau^R(x,u)tau^R(v,y) + tau^R(x,v)tau^R(u,y)`. Summing over
`e in E_R` is summing over ordered adjacent pairs in `B_R`, so by Russo's
formula

```text
d/dp tau^R_p(x,y) <= d (T^R_p P_R T^R_p)(x,y),                       (4.1)
```

which also holds trivially when `x=y`, since then `tau^R=1`.

**(4c) The comparison solution.** Put `T_0=T^R_(p_c)`. Since `T_0 <= T`
entrywise, `||T_0|| <= M`, and `||P_R|| <= 1`. For `d delta M<1` define
`Y(delta)=sum_k (d delta)^k T_0 (P_R T_0)^k`. This is a norm-convergent
series of finite matrices, smooth in `delta`. Termwise,

```text
Y' = sum_k k d (d delta)^(k-1) T_0 (P_R T_0)^k,
d Y P_R Y = d sum_(i,j) (d delta)^(i+j) T_0 (P_R T_0)^(i+j+1) = sum_m d (m+1) (d delta)^m T_0 (P_R T_0)^(m+1),
```

so `Y' = d Y P_R Y` and `Y(0)=T_0`.

**(4d) Positivity of the difference.** Let `X(delta)=T^R_(p_c+delta)` and
`Z=Y-X`, so `Z(0)=0`. By (4.1),
`Z' >= d(Y P_R Y - X P_R X) = d(Z P_R Y + X P_R Z) =: A(delta) Z`, where
`A(delta)` is a linear map on `B_R x B_R` matrices, continuous in `delta`,
that maps entrywise nonnegative matrices to nonnegative ones, because
`X,Y,P_R>=0`. Put `g = Z' - A Z >= 0`. The linear equation
`Z' = A Z + g`, `Z(0)=0`, has the unique solution
`Z(delta)=int_0^delta U(delta,s) g(s) ds`, where `U` is the Dyson series
`U(delta,s)=sum_j int_(s<s_1<...<s_j<delta) A(s_j)...A(s_1) ds_1...ds_j`.
Each term preserves nonnegativity, so `Z>=0`, that is `X <= Y`.

**(4e) Removing the truncation.** Entrywise `Y(delta) <= sum_k (d delta)^k T(PT)^k`,
since `T_0<=T` and `P_R<=P`. As `R -> infinity`,
`tau^R_p(o,x)` increases to `tau_p(o,x)` (an increasing union of events). So
`tau_(p_c+delta)(o,x) <= sum_k (d delta)^k [T(PT)^k](o,x)`. Pairing with
`P^n(o,x)` gives `a_n(p_c+delta) <= M_n(delta)`. This proves part (2).

## Step 5. Vacuity under uniqueness (part 3)

Let `s` have a unique infinite cluster, so `theta(s)>0`. On
`{x<->infinity} cap {y<->infinity}` both vertices lie in the unique infinite
cluster, so Harris-FKG gives `tau_s(x,y) >= theta(s)^2` for all `x,y`.

Let `Q` be a finite product of kernels from `{I,P,T_q}`. Each such kernel
has row sums `>=1` (`P` has row sums `1`, and `tau_q(b,b)=1`), so `Q` does
too. Consider an entry of `L T_s Q T_(s') R`, with `L,R` again such
products. Choose `a` with `L(x,a)>0` and `e` with `R(e,y)>0`; they exist
because row and column sums are positive. Then

```text
(L T_s Q T_(s') R)(x,y) >= L(x,a) R(e,y) theta(s)^2 theta(s')^2 sum_b sum_c Q(b,c)
                        >= L(x,a) R(e,y) theta(s)^2 theta(s')^2 sum_(b in Gamma) 1 = infinity.
```

In particular every entry of `T_s P T_s` is `+infinity`.

Now consider Picard iteration of the integrated inequality
`tau_q <= T + d int_(p_c)^q T_s P T_s ds`. This inequality is (4.1)
integrated and passed to `R -> infinity` by monotone convergence. The
iteration replaces one factor `T_s` by the right-hand side at parameter `s`.
Every term that still contains a supercritical factor contains it inside a
block `T_(s_1) P T_(s_2)` with `s_1,s_2>p_c`, integrated over a set of
positive measure. Under `p_c=p_u`, `fpbs-cluster-count-trichotomy` gives
uniqueness at every `s>p_c`. So each such integrand is `+infinity` on a
positive-measure set, and the term is `+infinity`. This proves part (3). ∎
