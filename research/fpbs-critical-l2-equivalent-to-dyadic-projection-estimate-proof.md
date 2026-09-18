---
rg: 2
id: fpbs-critical-l2-equivalent-to-dyadic-projection-estimate-proof
kind: route
title: A ghost vertex in a large cluster is a third BK arm, so large-cluster connectivity costs one magnetization factor
target: fpbs-critical-l2-equivalent-to-dyadic-projection-estimate
requires:
  - fpbs-triangle-condition-gives-mean-field-magnetization
  - fpbs-dyadic-projections-bound-connectivity
---

Complete written proof. No computation is used. Notation as in the claim;
`P` is the joint law of critical bond percolation `omega` and an independent
ghost set `Gh`, each vertex green independently with probability `1-e^(-h)`,
so that `P(K_x cap Gh != empty | omega) = 1-exp(-h|K_x|)` (equal to `1` when
`K_x` is infinite) and, by transitivity, `P(z <-> Gh) = M_h` for every `z`.

**Step 1 (volume indicator by a ghost).** For `n>=1` and `h=1/n`, the function
`s -> 1-exp(-s/n)` is nondecreasing on `[0,infinity]` and equals `1-e^(-1)` at
`s=n`. Hence `1{|K|>=n} <= (1-exp(-|K|/n))/(1-e^(-1))`, and taking
expectations on `{x<->y}`,

    T^(>=n)(x,y) <= (e/(e-1)) P(x<->y, K_x cap Gh != empty).        (1)

**Step 2 (three disjoint witnesses).** Suppose `x<->y` and some green `w`
lies in `K_x`. Choose a self-avoiding open path `pi` from `x` to `y` and an
open path `gamma` from `w` to `x`. Let `z` be the first vertex of `gamma`
(starting from `w`) lying on `pi`; it exists since `x` is on `pi`. Then

* `pi[x,z]` witnesses `{x<->z}`,
* `pi[z,y]` witnesses `{z<->y}`,
* `gamma[w,z]` together with the colour coordinate of `w` witnesses `{z<->Gh}`.

The two pieces of `pi` share no edge because `pi` is self-avoiding, and
`gamma[w,z]` meets `pi` only at `z`, so it shares no edge with either piece;
the third witness is the only one using a colour coordinate. Degenerate cases
(`z=x`, `z=y`, `z=w`) use the empty witness of a sure event. So

    {x<->y, K_x cap Gh != empty} subset union_z {x<->z} o {z<->y} o {z<->Gh}.

**Step 3 (BK in infinite volume).** For a ball `B_R` let the same three events
be required inside `B_R`. These are increasing events on the finite product
space of edge states and vertex colours of `B_R`; the inclusion of Step 2 holds
inside `B_R` with paths in `B_R`, and the left side increases to the full
event as `R -> infinity`. By the van den Berg-Kesten inequality applied twice
(`A o B o C subset A o (B o C)`) and a union bound,

    P(x<->y in B_R, some green w <-> x in B_R)
       <= sum_{z in B_R} tau(x,z) tau(z,y) M_h.

Letting `R -> infinity` (monotone convergence) and combining with (1),

    T^(>=n)(x,y) <= (e/(e-1)) M_(1/n) (T^2)(x,y).                 (2)

This is item 1 of the claim.

**Step 4 (operator norms).** For nonnegative kernels `0<=K<=L` entrywise,
`|<f,Kg>| <= <|f|,K|g|> <= <|f|,L|g|>`, so `||K|| <= ||L||`. If `||T||<infinity`,
the kernel `sum_z tau(x,z)tau(z,y)` is the kernel of the operator `T^2` (Tonelli,
all terms nonnegative) and `||T^2|| <= ||T||^2`. Hence

    ||T^(>=n)|| <= (e/(e-1)) M_(1/n) ||T||^2.                     (3)

**Step 5 (triangle condition and magnetization).** If `||T||<infinity` then
`nabla_{p_c}(o) = (T^3)(o,o) = <delta_o, T^3 delta_o> <= ||T||^3 < infinity`.
By `fpbs-triangle-condition-gives-mean-field-magnetization` there is `C_0`
with `M_h <= C_0 sqrt(h)` for `h in (0,1]`. With (3):
`||T^(>=n)|| <= C ||T||^2 n^(-1/2)`, `C=(e/(e-1))C_0`.

**Step 6 (shells).** Entrywise,
`2^k Q_k(x,y) = E[1{x<->y, 2^k<=|K_x|<2^(k+1)} 2^k/|K_x|] <= T^(>=2^k)(x,y)`.
By Step 4, `||Q_k|| <= 2^(-k)||T^(>=2^k)|| <= C||T||^2 2^(-3k/2)`, and
`sum_k 2^k||Q_k|| <= C||T||^2 sum_k 2^(-k/2) <= 4C||T||^2`. This is item 2.
Without Step 5, `sum_k 2^k||Q_k|| <= (e/(e-1))||T||^2 sum_k M_(2^-k)`, and
`sum_{k>=0} min(1, 2^(-k)m) <= log_2(1+m)+3` for every `m>=1`, while
`1-e^(-t) <= min(1,t)`; this gives the logarithmic-moment form.

**Step 7 (equivalence).** Q3 with `eta=1/2` implies Q2 by summing a geometric
series. Q2 implies `||T||<infinity` by `fpbs-dyadic-projections-bound-connectivity`
(for finitely supported `f`, `<f,Tf> = E sum_C |f(C)|^2 <= sum_k 2^(k+1)<f,Q_k f>`
when all critical clusters are a.s. finite, which holds on nonamenable Cayley
graphs by Benjamini-Lyons-Peres-Schramm and is the standing assumption of that
claim). `||T||<infinity` implies Q3 with `eta=1/2` by Step 6.
This is item 3.

**Step 8 (sharpness).** `||Q_j|| >= <delta_o,Q_j delta_o> = E[1{shell j}/|K_o|]
>= 2^(-j-1) P(shell j)`. Summing over `j>=k` gives
`sum_(j>=k) 2^j||Q_j|| >= P(2^k<=|K_o|<infinity)/2`, and when critical clusters
are finite this is `P(|K_o|>=2^k)/2 >= (c/2) 2^(-k/2)` by the unconditional
lower bound in `fpbs-triangle-condition-gives-mean-field-magnetization`.
This is item 4.

**Calibration.** On regular trees of degree at least three,
`fpbs-regular-tree-dyadic-three-halves` gives `||Q_N|| ≍ N^(-3/2)`, matching
Steps 6 and 8 exactly, although no branching structure is used here. On the
FIID model of `fpbs-fiid-finite-clusters-do-not-imply-dyadic-summability` the
connectivity operator is unbounded (infinite susceptibility along vertical
intervals), so the theorem does not apply there, as it must not: Step 2 needs
the independent product structure for BK, which that factor of iid lacks.
