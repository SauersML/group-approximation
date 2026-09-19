---
rg: 2
id: fpbs-tree-product-thin-section-subgroups-have-tilt-gap
kind: claim
title: On a tree times any Cayley graph, every subgroup whose tree-direction sections grow slower than the branching number is dominated by an end-tilted susceptibility and has a relative gap, and on the tree itself the tilts certify exactly the subgroups with a gap
distinct_from:
  fpbs-percolation-schreier-kesten-gap: that conjectures p_c < p_c(I;G) for every infinite non-co-amenable subgroup of every Cayley graph; this proves it on tree products for every subgroup of section growth below q, a class containing non-normal, non-amenable, non-fibre subgroups such as the diagonal of F_d x F_d and J x K with J non-co-amenable in F_d, with the explicit lower bound p_c(I;G) >= p_c(G,Gamma_xi,lambda).
  fpbs-percolation-kesten-normal-gap: that conjectures the gap for every normal subgroup with nonamenable quotient; this proves it on T x H for the normal subgroups N_1 x K with N_1 normal in F_d and F_d/N_1 nonamenable, and K normal in H_grp arbitrary.
  fpbs-tree-subgroup-relative-gap-iff-not-co-amenable: that decides the gap on the tree itself through the explicit two-point function p^|x| and the cogrowth series; this works on T x H for arbitrary H, where no two-point function is explicit, and uses that node only to evaluate section growth and to calibrate the method on the tree.
  fpbs-tree-product-relative-threshold-is-heaviness-threshold: that computes p_c(N;G) = p_h for the fibre N = {1} x H_grp; this bounds p_c(I;G) from below by tilted thresholds for subgroups that are not contained in any fibre and are not normal, and uses neither heaviness nor slabs.
  fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility: that identifies the fibre-summed operator norm along N with chi_(p,1/2); this uses chi_(p,lambda), for every lambda in (0,1), only as a dominating sum for the susceptibility of other subgroups, through the radial symmetry of tau_p in the tree coordinate.
  fpbs-hutchcroft-nonunimodular-pc-below-pt: that is the imported inequality p_c < p_c(G,Gamma,lambda) <= p_t; this transfers it to relative thresholds of a class of subgroups.
artifacts:
  - experiments/fpbs-tilt-sections-2026-09-17/check_tilt_sections.py
  - experiments/fpbs-tilt-sections-2026-09-17/output.txt
---

**ESTABLISHED.** Proof route:
`fpbs-tree-product-thin-section-subgroups-have-tilt-gap-proof`.

**Setting.** This is the setting of
`fpbs-tree-product-relative-threshold-is-heaviness-threshold`, with `H`
allowed to be finite or trivial.

- `T = Cay(Lambda,S_Lambda)` is the `k`-regular tree, `k >= 3`, `q = k - 1`.
  `S_m` is the sphere of radius `m` about `1` in `Lambda`.
- `H = Cay(H_grp,S_H)` is any Cayley graph of a finitely generated group.
- `G = T x H` is the Cartesian product, the Cayley graph of `Lambda x H_grp`
  with generating set `S_Lambda ⊔ S_H`, and `o = (1,1)`.
- `xi` is an end of `T`, and `Gamma_xi = Aut_xi(T) x H_grp`. Hutchcroft's
  tilted threshold is `p_c(G,Gamma_xi,lambda)`, his tiltability threshold is
  `p_t = p_c(G,Gamma_xi,1/2)`, and `chi_(p,lambda)` is the tilted
  susceptibility. The definitions are verbatim in
  `fpbs-hutchcroft-nonunimodular-pc-below-pt-citation`.
- For `I <= Lambda x H_grp` and `h in H_grp`, the **section** over `h` is
  `I_h = {y in Lambda : (y,h) in I}`. The **tree section** is
  `J(I) = I_1`. Each nonempty `I_h` is a left coset of `J(I)`.
- The **section growth** of `I` is

  ```text
  beta(I) = limsup_(m -> infinity) ( sup_(h in H_grp) #(I_h ∩ S_m) )^(1/m)   in [0, q].
  ```

  For `J <= Lambda`, `alpha(J) = limsup_t #(J ∩ S_t)^(1/t)` is its growth in
  `T`. Always `beta(I) >= alpha(J(I))`.
- `chi^I_p = E_p|K_o ∩ I|`. `p_c(I;G)` denotes either
  `sup{p : chi^I_p < infinity}` or Hutchcroft–Pan's threshold for some
  cluster to meet `I` infinitely often. Both are bounded below in the same
  way.

**Theorem.**

1. **Domination.** Let `lambda in (0,1)` and `M = max(lambda, 1-lambda)`.
   Suppose `C = sup_(h,m) #(I_h ∩ S_m) q^(-Mm) < infinity`. Then

   ```text
   chi^I_p <= C chi_(p,lambda)        for every p in [0,1].
   ```

   At `lambda = 1/2` the hypothesis can be weakened to
   `C' = sup_(h,m) #(I_h ∩ S_m) / ((m+1) q^(m/2)) < infinity`, and then
   `chi^I_p <= (q/(q-1)) C' chi_(p,1/2)`.
2. **Gap.** Let `I` be infinite with `beta(I) < q`. Then for every
   `lambda in (0,1)` with `q^(max(lambda,1-lambda)) > beta(I)`,

   ```text
   p_c(G) < p_c(G,Gamma_xi,lambda) <= p_c(I;G).
   ```

   If `beta(I) < sqrt q`, or `C' < infinity`, this gives `p_c(I;G) >= p_t`.
3. **Computing `beta`.**
   - (a) If `J(I)` is finite or virtually cyclic, then
     `sup_(h,m) #(I_h ∩ S_m)` is finite. In fact it is at most `3r` when
     `J(I)` has an infinite cyclic subgroup of index `r`. So `beta(I) <= 1`,
     and `C' < infinity`.
   - (b) If `J(I)` is infinite and has finite index in the projection
     `pi_1(I)` of `I` to `Lambda`, then `beta(I) = alpha(J(I))`. This holds
     for example when `I = J x K` with `J` infinite.
4. **Calibration on the tree** (`H` trivial, `Lambda = F_d` with a free
   basis, `q = 2d - 1`, `J <= F_d` infinite).
   - `p_c(T,Aut_xi T,lambda) = q^(-max(lambda,1-lambda))`, and so
     `p_t = 1/sqrt q`.
   - With `p_c(J;T)` the susceptibility threshold, `p_c(J;T) = 1/alpha(J)`,
     and `p_c(J;T) >= p_c(T,Aut_xi T,lambda)` iff
     `alpha(J) <= q^(max(lambda,1-lambda))`.
   - Some `lambda in (0,1)` certifies `J` iff `alpha(J) < q`. By
     `fpbs-tree-subgroup-relative-gap-iff-not-co-amenable`, that is exactly
     when `J` has a relative gap.

   So on the tree the tilt family loses nothing. The half tilt alone, which
   gives the bound `p_t`, is sharp at `alpha(J) = sqrt q`.

**Instances.** Each instance is an infinite subgroup with `p_c(I;G) > p_c(G)`.

- **The diagonal `D` of `F_d x F_d`**, `d >= 2`, in the standard Cayley graph
  `T_(2d) x T_(2d)`.
  - `J(D) = {1}`, so `p_c(D;G) >= p_t`.
  - `D` is not normal.
  - `D` is not co-amenable. The map `D(g,h) -> g^(-1) h` identifies right
    cosets with `F_d`, and turns right multiplication by `(1,s)` into right
    translation by `s`.
- **Graphs of homomorphisms** `{(psi(h),h) : h in H_0}`, for any infinite
  `H_0 <= H_grp` and any homomorphism `psi: H_0 -> Lambda`. Here `J = {1}`.
- **Every virtually cyclic subgroup** of `Lambda x H_grp`, in particular every
  infinite cyclic subgroup. This is the "cyclic subgroups" special case of
  `fpbs-percolation-schreier-kesten-gap` on every tree product.
- **`J x K`** for any `J <= F_d = Lambda` that is not co-amenable in `F_d`, and
  any `K <= H_grp`. By item 3 of the tree node, `alpha(J) < q`. Examples:
  - `<a,b> x {1}` in `F_3 x Z`, where `alpha = 3` lies in `(sqrt 5, 5)`. The
    half-tilt hypothesis fails for it, since `#(J ∩ S_m) = 4 * 3^(m-1)`. Any
    `lambda` with `q^(1-lambda) > 3` catches it.
  - `<a> x H_grp`, which is not normal.
- **Normal instances of the Kesten gap.** Take `N_1 x K` with `N_1` normal in
  `F_d`, `F_d/N_1` nonamenable, and `K` normal in `H_grp`. This is normal
  with nonamenable quotient `(F_d/N_1) x (H_grp/K)`. These are instances of
  `fpbs-percolation-kesten-normal-gap` on `T x H` that are not the fibre
  `{1} x H_grp`.

**Where the method stops (named invariant).** The invariant is the section
growth `beta(I)`. For `lambda in (0,1)`, the end-tilt comparison of Step 3
of the route needs `#(I_h ∩ S_m) <= C S_lambda(m)`. Since
`S_lambda(m) <= (m+1) q^(m max(lambda,1-lambda))`, the comparison fails for
every such `lambda` exactly when `beta(I) = q`. Outside `(0,1)` the tilted
threshold is no longer strictly above `p_c` by the import.

- The residual class on `T x H` is the subgroups with full section growth,
  for example `Lambda x K`, or the other factor `Lambda x {1}` when `H_grp` is
  nonamenable.
- When `H` has no tree factor, these are left to the open
  `fpbs-percolation-schreier-kesten-gap` and
  `fpbs-percolation-kesten-normal-gap`. The tree-end tilt only sees the tree
  direction.

**What this does and does not advance.**

- *Why it is new on the board.* Before this node, the board had the gap on a
  non-tree graph only for fibres and for amenable wq-normal subgroups, both
  through `p_h` and `p_u`. This node gives it for subgroups that are none of
  normal, co-amenable, contained in a fibre, or amenable. `F_2 x F_2` is the
  named test group of the product lane
  (`fpbs-relative-threshold-is-quotient-l2-threshold`). No literature search
  beyond the board was made.
- *Why it does not advance the goal.* `T x H` already has `p_c < p_u` by
  Hutchcroft.
- *Why it matters.* It is a complete calibration of tilt domination. It
  passes the tree test with no loss, and it names the one invariant,
  `beta(I) = q`, at which it fails on products.
