---
rg: 2
id: fpbs-isolated-pairs-defeat-amenable-kernel-approximation
kind: claim
title: V x V lies in the Kesten half (alpha), but every marking of it is isolated, and both of its Kesten witnesses V x 1 and 1 x V are limits of no amenable-kernel pairs, so every approximation or transfer argument for the percolation Kesten gap is vacuous there
distinct_from:
  fpbs-l2-gap-transfers-to-kesten-normal-gap: that proves the gap for residually amenable N from l2 bounds on the amenable-kernel quotients Gamma/N_j; this extends it to every limit of amenable-kernel pairs, and shows that the class of such limits misses explicit pairs of the Kesten half (alpha), where the tower in its Step 2 cannot exist.
  fpbs-l2-gap-baire-dichotomy: that records, in its refutation note, that finitely presented simple groups are isolated marked groups, which are normally co-amenable and so lie in the half (beta); this shows that the half (alpha) itself contains isolated groups, and that their witness pairs are isolated as marked pairs.
  fpbs-kesten-margin-collapses-near-lamplighter: that kills local and uniform-margin certificates through approximants whose Kesten margin tends to 0; this kills approximation arguments at pairs that have no proper approximants at all, whatever the margins are.
  fpbs-soft-collapse-kills-relative-gap-proofs: that kills proofs using only Bernoulli facts at p <= p_c together with soft supercritical inputs; this kills proofs that pass through other marked pairs by local convergence, and puts no restriction on the percolation input at the pair itself.
  seeds-never-survive-marked-approximation: that proves isolation relative to a pattern for finitely presented groups carrying a seed; this proves isolation of the marked pairs (V x V, V x 1) and uses simplicity of V, not seeds.
  fpbs-percolation-kesten-normal-gap: that is the open gap; this does not decide it at V x V, and shows only which methods cannot decide it there.
---

**ESTABLISHED (class-killing obstruction).** Proof route:
`fpbs-isolated-pairs-defeat-amenable-kernel-approximation-proof`.

**Setting.**
- A marked pair `(Gamma, N)` is a pair `R ⊆ M` of normal subgroups of the
  free group `F_k`, with `Gamma = F_k/R` and `N = M/R ◁ Gamma`.
- Pairs converge when both coordinates converge locally. That is, for each
  `n`, eventually `R_j ∩ B_n = R ∩ B_n` and `M_j ∩ B_n = M ∩ B_n`, where
  `B_n` is the ball of radius `n` in `F_k`.
- The pair is **amenable-kernel approximable (AA)** if there are normal
  subgroups `R_j ⊆ M` of `F_k` with `M/R_j` amenable and `R_j -> R`. Then
  `Gamma_j = F_k/R_j` covers `Q = Gamma/N` with amenable kernel and converges
  to `Gamma`.
- Every residually amenable `N` in the sense of
  `fpbs-l2-gap-transfers-to-kesten-normal-gap` is AA.
- `V` is Thompson's group (`thompson-v-finitely-presented-infinite-simple`).

**Theorem.**

1. **The transfer lemma holds on the whole AA class.** Items 1, 3 and 4
   (the transfer lemma, Corollary A and Corollary B) of
   `fpbs-l2-gap-transfers-to-kesten-normal-gap` hold verbatim for every AA
   pair `(Gamma, N)`.

2. **Kernel obstruction.** Let `C` be a class of groups closed under
   subgroups. Suppose `(Gamma, N)` is a limit of marked pairs
   `(Gamma_j, N_j)` with every `N_j` in `C`. Then every finitely generated
   subgroup `H <= N`, with any finite marking, is a local limit of marked
   groups in `C`.

   If moreover `H` is finitely presented and infinite simple, then `H` lies
   in `C`. So if `N` contains a finitely presented, infinite, simple,
   nonamenable subgroup, then `(Gamma, N)` is not AA. It is not even a limit of
   pairs with amenable kernels.

3. **`V x V` is in the Kesten half and is isolated.** Let `Gamma = V x V`.
   - Its normal subgroups are exactly `1`, `V x 1`, `1 x V` and `Gamma`.
   - So `Gamma` lies in the half (alpha) of `fpbs-bs-via-percolation-kesten-split`,
     with exactly two witnesses, `N = V x 1` and `N = 1 x V`. Each witness has
     quotient `V`, which is nonamenable.
   - For every finite marking `S`, the marked group `(Gamma,S)` is isolated
     in the space of marked groups. Each witness pair `(Gamma, N)` is isolated
     among marked pairs. Every sequence of marked pairs converging to it is
     eventually equal to it.
   - Neither witness pair is AA.

4. **What dies (the invariant and the step).** The invariant is isolation of
   the witness pair. Equivalently, it is the presence of the finitely
   presented, infinite, simple, nonamenable subgroup `V` inside the kernel.

   Consider any argument that proves the gap `p_c(G) < p_c(N;G)`, or a bound
   `chi^N <= M` on `[0, p_c + delta]`, at `(Gamma, N)` in the following way:
   it first establishes a property at other marked pairs `(Gamma_j, N_j)`,
   and then passes it to `(Gamma, N)` along a convergent sequence. The passage
   may use:
   - local convergence of balls;
   - lower semicontinuity of `chi^N` or of `p_c`, or Easo–Hutchcroft locality;
   - compactness of `X_(k,eta)`;
   - Baire category;
   - transplanting from finite models;
   - Følner compression on amenable kernels.

   At `(V x V, V x 1)` every such argument collapses to the same statement at
   `(V x V, V x 1)` itself. The step where it dies is the construction of the
   approximants, Step 2 of `fpbs-l2-gap-transfers-to-kesten-normal-gap-proof`.
   There is no tower `N_j` with `N/N_j` amenable. More generally, no sequence
   of pairs with amenable kernels converges to the pair, and every
   convergent sequence of pairs is eventually constant. In particular:
   - Corollary B, the transfer route
     `fpbs-uniform-kesten-law-from-uniform-l2`, and the uniform Kesten law
     `fpbs-uniform-kesten-law-residually-amenable-pairs` say nothing at
     `V x V`, even if they are true.
   - No closure argument extends them to `V x V`.
   - The half (alpha) therefore cannot be reached from the AA class by
     approximation. It needs an argument that works at the isolated pair
     itself.

5. **The amenable-subgroup variant reduces to the global l2 gap.** On an
   isolated marked group, Følner compression through approximants certifies
   a relative gap along a subgroup `H` only in two ways:
   - along an amenable `H <= Gamma` itself, where it gives
     `chi^H_q <= ||T^Gamma_q||`, so it needs `p_c(Gamma) < p_(2->2)(Gamma)`;
   - along a finitely generated nonamenable `H`, where it is impossible,
     since no sequence of amenable subgroups converges to `H`.

   `V x V` does have infinite amenable wq-normal subgroups. For `g in V` of
   infinite order, `<g> x 1` is one. So `V x V` also lies in the first half of
   `fpbs-bs-split-by-amenable-wq-normal-subgroup`. There, by
   `fpbs-bs-iff-finite-relative-susceptibility`, `p_c < p_u` is equivalent to
   `chi^(<g> x 1)_p < infinity` for some `p > p_c`. On `V x V`, the only
   compression certificate of that is the l2 gap `p_c < p_(2->2)` on
   `Cay(V x V, S)` itself. That gap already gives `p_c < p_u` by
   `fpbs-hutchcroft-l2-gap-criterion`.

**Scope and calibration.**
- Item 3 extends to `H_1 x H_2` for any two finitely presented, infinite,
  simple, nonamenable groups `H_i`. It also covers Burger–Mozes lattices, once
  such an import is recorded. It is not needed here.
- For `H x F_2` the obstruction does not apply. The witness `1 x F_2` is
  residually solvable, so the transfer lemma is available there. A group in
  (alpha) is out of reach of transfer only when every witness kernel fails AA.
- The claim does not say that the gap fails on `V x V`. It only says that no
  argument routed through other marked pairs can prove it. On the board, no
  node establishes `p_c < p_u` on every Cayley graph of `V x V`.
  `fpbs-expanding-factor-product-strict-thresholds` covers only product
  generating sets with a strongly expanding factor.
