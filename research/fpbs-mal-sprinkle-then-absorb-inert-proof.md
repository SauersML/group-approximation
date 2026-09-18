---
rg: 2
id: fpbs-mal-sprinkle-then-absorb-inert-proof
kind: route
title: Fineness of the random cluster graph from the linear-perimeter cycle count, then an arc lemma against infinitely many edge-disjoint bounded contacts
target: fpbs-mal-sprinkle-then-absorb-inert
requires:
  - fpbs-malnormal-coset-cycles-linear-perimeter
  - fpbs-malnormal-measured-absorption-cap
artifacts:
  - research/artifacts/fpbs-mal-sprinkle-then-absorb-inert-2026-09-17.md
---

Full proof in the artifact (§§1–7). Outline:

1. **Freeness (§1, self-contained).** For `gamma ≠ 1`, choose infinitely many
   `delta_i` so that the pairs `{delta_i, gamma^{-1} delta_i}` are pairwise
   disjoint. The coincidence events are independent, each with probability
   `sum nu(z)^2 < 1`.
2. **Class graph (§2).** The map `g ↦ g^{-1} x` identifies the class graph of
   `S_1` in `F x` with the coset graph, with edge `e(g)` open iff
   `g^{-1} x in B`. Windows `gW` give block independence: any `m` edges are
   all open with probability at most `q^m`.
3. **Property P (§3).** `E N_j(e(g)) <= sum_k A^k k^j q^{k-1-j} < infinity`
   when `A q < 1`. This uses `M(k) <= A^k`, quoted from
   [[fpbs-malnormal-coset-cycles-linear-perimeter]] item 2: "The number `M(k)`
   of simple cycles through a fixed edge `e(g)` with `k` `t`-edges is at most
   `A^k`."
4. **Fineness (§3).** Lifting a simple cluster-graph cycle of length `L` gives
   a simple class-graph cycle with exactly `L` closed edges. So each non-loop
   cluster-graph edge lies on finitely many cycles of length at most `L`.
5. **Main theorem (§5).**
   - Mass transport bounds `∫ |M_K^z| <= K`, so a.e. closed edge is crossed by
     finitely many minimal walks with `kappa <= K`.
   - Greedy selection gives infinitely many edge-disjoint cluster-arcs of
     length at most `K` from `C_1 = [x]` to `C_2 = [phi x]`.
   - If `C_1 ≠ C_2`, Veblen's theorem on `alpha_1 ∪ alpha_j` puts the first
     edge of `alpha_1` on infinitely many distinct cycles of length at most
     `2K`, contradicting fineness.
6. **Chains (§6).** Theorem A of [[fpbs-malnormal-measured-absorption-cap]]
   ("If `S ⊆ E_{a|Lambda}`, then `gamma(x) ∈ Q(Lambda)` for almost every
   `x ∈ D_phi(S)`") with `Lambda = F` malnormal gives labels in `F` on
   `D_phi(S_1)`. Transfinite induction then shows the chain is constant.
7. **Properness (§6, Proposition 7).** The detour probability is at most
   `sum_{k >= 2} A^k q^{k-1} <= 1/3` for `q <= 1/(4 A^2)`.
