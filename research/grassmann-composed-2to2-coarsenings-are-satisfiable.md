---
rg: 2
id: grassmann-composed-2to2-coarsenings-are-satisfiable
kind: claim
title: On every folded DKKMS Grassmann instance the branch-blind quotient coarsening is perfectly satisfiable by one gauge labelling, so every affine-view unique verifier over these 2-to-1 and 2-to-2 games has value at least 2c-1 on NO instances as well
distinct_from:
  linear-view-unique-verifiers-collapse-to-quotient-coarsening: that reduces any affine-view verifier over any linear outer game to the coarsening Can and leaves open whether Can of hard 2-to-2 instances is hard; this evaluates Can on the actual hard family, the folded Dinur--Khot--Kindler--Minzer--Safra instances, and shows it has value 1 on every instance, so that door is closed for this family.
  low-degree-view-unique-verifiers-collapse: that concerns views of bounded algebraic degree and the partition coarsening Can_part; this concerns affine views only and computes the value of Can exactly on one instance family. Can_part for non-affine views is not covered.
  unique-games-hard-at-completeness-one-half: that is the split reduction reaching completeness 1/2; this shows that no affine-view unique verifier over the same outer instances gets past 2c - 1 <= s, so reaching completeness above 1/2 with small soundness needs non-affine views or a different outer family.
artifacts:
  - experiments/dkkms-coarsening-2026-09-17/check_dkkms_coarsening.py
---

**ESTABLISHED.** Route: `grassmann-composed-2to2-coarsenings-are-satisfiable-proof`.

*The instances.* These are the folded instances of Dinur--Khot--Kindler--Minzer--Safra,
"Towards a proof of the 2-to-1 Games Conjecture?" (ECCC TR16-198, Section 4.2).
Khot--Minzer--Safra (FOCS 2018) completed their soundness analysis, and this
gives `two-to-two-games-theorem`. A regular 3LIN instance has equations `e` with
right-hand sides `b_e`. `U` ranges over legitimate `k`-tuples of equations.
`X_U` is the set of vectors supported on the variables of `U`,
`H_U = Span(x_e : e in U)`, and `h_U : H_U -> F_2` is `h_U(x_e) = b_e`. The
A-vertices are `(U, L)` with `L in Gr(X_U, l)` and `L meet H_U = {0}`. They are
grouped into folding classes `C(U_0, L_0) = {(U,L) : L + H_U + H_U0 = L_0 + H_U + H_U0}`.
Each class `C` carries a fixed representative `R_C`, and its label is a linear
`sigma : R_C -> F_2`, unfolded to a member `(U, L)` as the `(H_U, h_U)`-extension
restricted to `L`. B-vertices `(V, L')` have `L' in Gr(X_V, l-1)` with labels on
`L'`.

*Agreement games.* An **agreement edge** joins two vertices, each an A-class
through a member `(U_i, L_i)` or a B-vertex, and names a common subspace
`W <= L_1 meet L_2`. For a B-vertex, `L_i = L'` and `W <= L'`. It accepts iff the
two unfolded labels agree on `W`. So `H_e = { (sigma_1, sigma_2) : u_1(sigma_1) = u_2(sigma_2) }`,
where `u_i(sigma)(x) = sigma(r_i x) + h_(U_i)(x - r_i x)`, `x in W`, and
`r_i x` is the `R_(C_i)`-component of `x` in `R_(C_i) + H_(U_i)`. Every constraint
of the folded 2-to-1 game `G_folded` is of this form (`W = L'`). So is every
derived 2-to-2 constraint, where two members sharing a B-vertex must agree on
`L'`. So is any agreement test of higher codimension on the same vertex set.
Call any such linear outer game `Phi` a **DKKMS agreement game**.

1. **Exact triples see one subspace.** On an agreement edge, a pair of affine
   views with kernels `Ann(M_1)` and `Ann(M_2)`, `M_i <= R_(C_i)` (or `<= L'`), is
   exact iff there is `N <= W` with `M_1 = r_1(N)` and `M_2 = r_2(N)`. The induced
   bijection is `beta(sigma_1|M_1) = sigma_2|M_2` subject to
   `u_1(sigma_1)|N = u_2(sigma_2)|N`.
2. **Gauge labelling.** For a vertex `z`, a subspace `M <= R_z` of dimension `m`,
   and any member `(U, L)` of `z`, let `Q` be the DKKMS folding class of `(U, M)`
   at dimension `m`, and `R_Q` its representative from DKKMS Lemma 4.1. Put
   ```text
   F*(z, M)(r) = h_U( r - pi_Q(r) ),     r in M,
   ```
   where `r = pi_Q(r) + (r - pi_Q(r))` is the decomposition in `R_Q + H_U`. Then
   `F*(z, M)` is linear, and it does not depend on the member `U` used.
3. **Perfect satisfiability.** `F*` satisfies every exact triple of every
   DKKMS agreement game. So for every affine-view unique verifier `V`,
   ```text
   val( Can(Phi, V) ) = 1     on every 3LIN input, satisfiable or not.
   ```
4. **Class kill.** By `linear-view-unique-verifiers-collapse-to-quotient-coarsening`
   (item 3, `p = 2`), every affine-view unique verifier with oblivious completeness
   `c` satisfies `val(V(Phi)) >= w_ex >= 2c - 1` on **every** instance. A reduction
   from a DKKMS agreement game to `Gap-UG(c, s)` through such a verifier needs
   `s >= 2c - 1`, that is `c <= (1 + s)/2`. With `s -> 0` its oblivious
   completeness cannot exceed `1/2 + o(1)`, which is the known split bound.

**Where the soundness goes.** The honest labelling of a class `C` is one linear
functional on the `l`-dimensional `R_C`. The coarsening only asks for its
restrictions to the subspaces `M` that exact triples read, and it never links
two different `M <= R_C` at the same vertex. Same-owner exact triples need equal
kernels. So the Grassmann consistency across the codimension-1 subspaces of one
`L`, which is what the Khot--Minzer--Safra expansion theorem controls, is exactly
what `Can` forgets. The 3LIN right-hand sides enter only through the folding
offsets `h_U`. These are a coboundary on each dimension-`m` folding class: all
offsets are measured against one representative `R_Q`, which DKKMS Lemma 4.1
provides, and the representative is valid for every member at once. So no cycle
of `Can` carries a twist, even on unsatisfiable inputs.

**Consequence for `unique-games-conjecture`.** Door (P1) of the affine-view
collapse asks whether the branch-blind coarsening of hard 2-to-2 instances is
hard. For the only known hard family, the folded DKKMS Grassmann instances, and
for every agreement test on its vertex set, the answer is no. The coarsening has
value 1 on NO instances. So every Hadamard, Grassmann or subspace-encoding unique
verifier composed on top of these instances dies at the collapse step, with
soundness at least `2c - 1`. The invariant is the gauge `F*`, and it exists
because folding offsets are coboundaries on folding classes. Only these routes
survive:
- views that are not affine in the outer label (door P2, or
  `low-degree-view-collapse-survives-non-affine-sigma` and `Can_part`);
- outer games whose linear constraints are not agreement edges on the DKKMS
  vertex set, so that exact triples can link two subspaces of one label space;
- verifiers whose completeness is not oblivious on `H_e`, which the collapse
  theorem does not cover.

This neither proves nor refutes UGC.

## Attempts

- **Twist search (2026-09-17).** The first worry was that folding across blocks
  re-expresses vectors modulo different `H_U` along a cycle
  `U -> V -> U' -> V' -> U`, and that the sums of right-hand sides could make
  `Can` a frustrated 3LIN-type unique game. The completeness proof of DKKMS
  (Section 5.1) does need the assignment to satisfy the equations inside the
  singled-out set `I(C)`. That is because an `l`-dimensional label must be
  consistent on all of `L`. At dimension `m` with a single subspace per `Can`
  vertex, the offsets telescope to the fixed representative `R_Q`, so there is
  no twist.
- **Brute-force check.**
  `experiments/dkkms-coarsening-2026-09-17/check_dkkms_coarsening.py` builds
  unsatisfiable 3LIN instances (an odd even cover plus random equations), with
  `k = 2`, all legitimate `U`, all `(U, L)` at every dimension `<= l`, union-find
  folding classes, and random derived 2-to-2 edges. It checks the following:
  - DKKMS Lemma 4.1 at every dimension;
  - `R_Q meet (H_U + H_U') = {0}`;
  - the exactness characterisation of item 1, by enumerating `H_e`;
  - that `F*` is independent of `U` and satisfies every exact triple;
  - a control, in which the zero labelling violates some exact triples.

  The default run is seed 20260917, `l = 2`: 1800 edges and 1800 exact triples,
  with 0 failures. The second run is `--seed 7 --l 3 --bvertices 60 --pairs 4`:
  240 edges and 960 exact triples at `m = 1, 2`, with 0 failures. In both runs
  the zero labelling fails on 160 and 12 triples respectively.
