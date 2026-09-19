---
rg: 2
id: fpbs-l2-gap-transfers-to-kesten-normal-gap
kind: claim
title: An l2 gap with fixed constants on the amenable-kernel quotients Gamma/N_j of a residually amenable normal subgroup N gives chi^N at most M on Gamma, so high-girth groups have a quantitative percolation Kesten gap and the uniform l2 route contains the Kesten route
distinct_from:
  fpbs-percolation-kesten-normal-gap: that conjectures the qualitative gap along every normal N with nonamenable quotient; this proves it, with explicit margin eta/(4(2k-1)) and bound chi^N at most 1+3/eta^2, for every residually amenable N in a marked group of girth at least L(eta) with rho(Gamma/N) at most 1-eta, and shows the uniform l2 conjecture implies the quantitative form on all residually amenable pairs.
  fpbs-l2-gap-class-closed-under-local-limits: that transplants a fixed-constant l2 bound from approximants to the limit's own operator, and in part 4 shows amenable approximants give no margin; this transplants it instead to the relative susceptibility along a nonamenable normal subgroup of the limit, through nonamenable approximants whose kernels are amenable, which the operator norm of the limit cannot bound.
  fpbs-amenable-kernel-l2-gap-forces-fibre-bubble: that bounds critical fibre bubbles on one graph with amenable kernel; this passes from amenable kernels N/N_j on the approximants to a nonamenable kernel N on the limit.
  fpbs-kesten-margin-collapses-near-lamplighter: that shows the Kesten margin is not ball-local when rho_Q tends to 1; this proves a margin depending only on k and a bound for rho_Q, which the lamplighter data satisfy.
  fpbs-pu-open-certificates-pinned-at-pc: that uses the derived series of F_2 as a tower of amenable groups with rho tending to 1; this uses the derived series of the kernel N, so every approximant keeps the quotient Gamma/N and the spectral bound rho at most rho(Gamma/N).
  fpbs-high-girth-uniform-l2-patch: that bounds ||T^G|| on high-girth groups; this converts that bound into the relative gap along nonamenable normal subgroups, which ||T^G|| does not control.
  fpbs-bk-majorant-kesten-gap-is-quotient-critical-l2: that relates the relative threshold to an l2 operator on the quotient; this uses l2 bounds on the Cayley graphs of intermediate quotients Gamma/N_j and no quotient operator.
artifacts:
  - experiments/fpbs-kesten-transfer-2026-09-17/tree_calibration.py
  - experiments/fpbs-kesten-transfer-2026-09-17/output.txt
---

**ESTABLISHED.** Proof route: `fpbs-l2-gap-transfers-to-kesten-normal-gap-proof`.

**Setting.**
- `(Gamma; s_1,...,s_k)` is a `k`-marked group, and `G = Cay(Gamma,S)` is its
  simple Cayley graph.
- `T^G_p` is the two-point operator with kernel `tau_p(x,y) = P_p(x <-> y)`.
- For a subset `A` of `Gamma`, `chi^A_p = E_p|K_e ∩ A| = sum_(a in A) tau_p(e,a)`.
- `p_c(N;G) = sup{p : chi^N_p < infinity}`.
- For `N ◁ Gamma` with `Q = Gamma/N`, `rho_Q = ||lambda_Q(pi_* mu)||`, where
  `mu` is uniform on the edge labels of `G` and `pi : Gamma -> Q`.
- `X_(k,eta)`, `L(eta)`, `M(eta) = 1 + 3/eta^2` and
  `delta(k,eta) = eta/(4(2k-1))` are as in `fpbs-high-girth-uniform-l2-patch`.

**Definition.** A normal subgroup `N ◁ Gamma` is **residually amenable in
`Gamma`** if there are subgroups `N_1 >= N_2 >= ...` with:
- each `N_j` normal in `Gamma` and contained in `N`;
- each `N/N_j` amenable;
- `∩_j N_j = {e}`.

Examples:
- **(a) `N` residually solvable.** Take `N_j = N^(j)`, the derived series.
  This covers every normal subgroup of a residually solvable group, for
  example of free groups, surface groups and right-angled Artin groups.
- **(b) `N` finitely generated and residually finite.** Take `N_j` to be the
  intersection of all subgroups of index at most `j` in `N`. This is
  characteristic in `N` and of finite index.

**Theorem.**

1. **Transfer lemma.** Let `N ◁ Gamma` be residually amenable in `Gamma`, with
   tower `(N_j)`. Put `G_j = Cay(Gamma/N_j)`, marked by the images of the
   `s_i`. Suppose that for infinitely many `j`
   `||T^(G_j)_(p_c(G_j)+delta)|| <= M`. Then

   ```text
   chi^N_q(G) <= M   for every q <= p_c(G) + delta,     so   p_c(N;G) >= p_c(G) + delta.
   ```

2. **Spectral control of the tower.** Let `rho_Q <= 1 - eta`. Then for all
   large `j`:
   - `G_j` lies in `X_(k,eta)`;
   - `G_j -> G` locally: for each `R`, once `j` is large enough, a word of
     length at most `R` is trivial in `G_j` iff it is trivial in `Gamma`.
     For every `j`, a word lies in `N/N_j` iff it lies in `N`.

3. **Corollary A (unconditional; high girth).** Let `Gamma` have no
   nontrivial reduced word of length less than `L(eta)` equal to `e`. Let
   `N ◁ Gamma` be residually amenable in `Gamma`, with `rho_Q <= 1 - eta`. Then

   ```text
   chi^N_q(G) <= 1 + 3/eta^2   for all q <= p_c(G) + eta/(4(2k-1)),
   p_c(N;G) - p_c(G) >= eta/(4(2k-1)).
   ```

   So the percolation Kesten normal gap holds, quantitatively, on every such
   pair. `N` itself may be nonamenable, in which case `||T^G||` does not bound
   `chi^N`.

4. **Corollary B (the uniform route contains a uniform Kesten law).**
   - If `||T^H_(p_c(H)+delta)|| <= M` for every `H` in `X_(k,eta)`, which is
     `fpbs-uniform-l2-gap-marked-groups` at `(k,eta)`, then every pair
     `(Gamma,N)` with `N` residually amenable in `Gamma` and
     `rho_Q <= 1 - eta` satisfies `chi^N <= M` on `[0, p_c + delta]`.
   - The same holds piece by piece. If the relator cylinder `Z_(k,eta,w)` has
     constants `(M_w, delta_w)`, the conclusion holds for every such pair
     with `w = e` in `Gamma`. The reason is that `w = e` in `Gamma` implies
     `w = e` in every `G_j`.

5. **Corollary C (falsifiers).** Suppose a family of such pairs `(Gamma_n, N_n)`
   has `rho_Q <= 1 - eta` and `p_c(N_n;Gamma_n) - p_c(Gamma_n) -> 0`, or
   `chi^(N_n)` unbounded at `p_c(Gamma_n) + delta` for every `delta > 0`.
   Then the family refutes `fpbs-uniform-l2-gap-marked-groups` at `(k,eta)`.
   If all the `Gamma_n` satisfy `w = e`, it refutes the cylinder
   `fpbs-uniform-l2-gap-short-relator-cylinders` at `(k,eta,w)`. A single pair
   with `p_c(N;G) = p_c(G)` refutes it at `eta = 1 - rho_Q`.

**Mechanism.** On `G_j` the kernel `A_j = N/N_j` is amenable. Compressing
`T^(G_j)_q` to `l^2(A_j)` gives convolution by the nonnegative function
`tau_q(e,.)` restricted to `A_j`. By Følner averaging its norm is its `l^1`
norm `chi^(A_j)_q`, so `chi^(A_j)_q <= ||T^(G_j)_q||`.

Two facts carry the bound to `Gamma`:
- `chi^(A_j)` agrees with `chi^N` on every finite window of radius and path
  length, once `j` is large;
- the spectral radius of `G_j` is at most `rho_Q`, because `G_j` covers `Q`.

The derived series of `N`, not of `Gamma`, is essential. It keeps the
quotient `Q`, and with it the spectral bound, on every approximant.

**Examples for Corollary A.**
- *Trees.* For `Gamma = F_k`, every normal subgroup is free, hence residually
  solvable. The corollary predicts
  `chi^N_s <= 1 + 3/eta^2` at `s = 1/(2k-1) + eta/(4(2k-1))` for all `N` with
  `rho_Q <= 1 - eta`. Grigorchuk's cogrowth formula together with
  `p_n(e) <= rho_Q^n` checks this independently, uniformly over all such
  `Q`, for `k = 2,3,4,6,10,50` and `eta` from `1e-6` up to the tree bound.
  - The worst ratio `chi/M` is `0.23`.
  - The exact tree margin exceeds `delta` by a factor of at least
    `4(q+1)/(q-1) > 4`.

  See `artifacts`. So the constants are consistent with the exact tree theory
  and are not sharp.
- *Surface groups (illustration).* Let `Gamma_g = pi_1(Sigma_g)` with its
  standard `2g` generators. Its Cayley graph is the 1-skeleton of the
  `{4g,4g}` tessellation, whose girth is `4g`.
  - Surface groups are residually free (Baumslag), so every normal subgroup
    is residually solvable.
  - Take `N` to be the kernel of `a_i, b_i -> x_i` onto `F_g`. Then `N` is
    free of infinite rank, hence nonamenable, and
    `rho_Q = sqrt(2g-1)/g <= 1/2` for `g >= 8`.
  - So for `g >= max(8, L(1/2)/4)`,
    `p_c(N;Gamma_g) >= p_c(Gamma_g) + 1/(8(4g-1))`.

  The same applies to every normal `N` of such `Gamma_g` with
  `rho_Q <= 1/2`. These are one-ended groups outside the tree and tree-product
  classes, where the board previously had no Kesten gap along a nonamenable
  normal subgroup.

**What it does and does not advance.**
- *Uniform-l2 route* (`fpbs-universal-uniform-l2-gap-route`). By Corollary B,
  any proof of `fpbs-uniform-l2-gap-short-relator-cylinders` must contain a
  uniform Kesten law for residually amenable pairs on that cylinder. On the
  class of residually solvable groups, the uniform-l2 route therefore
  contains the quantitative form of `fpbs-percolation-kesten-normal-gap`.
  The reason is that `rho_Q < 1` for nonamenable `Q`, so `eta = 1 - rho_Q`
  works.

  This gives the uniform route a new necessary prerequisite that can fail on
  its own: `fpbs-uniform-kesten-law-residually-amenable-pairs`. Corollary C
  names what would refute the route.
- *Kesten route.* Corollary A is new unconditional evidence for
  `fpbs-percolation-kesten-normal-gap`: a quantitative gap on every
  high-girth pair with a residually amenable kernel.
- *Not advanced.* The flagship itself is not advanced. On the groups of
  Corollary A, `p_c < p_u` was already known from the patch. The
  lamplighter collapse (`fpbs-kesten-margin-collapses-near-lamplighter`) has
  `rho_Q -> 1`, so it is consistent with Corollary B. No counterexample to
  the uniform conjecture follows.
