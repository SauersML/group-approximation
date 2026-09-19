---
rg: 2
id: fpbs-nonunimodular-level-sets-break-identity-e
kind: claim
title: In every nonunimodular transitive graph the kernel of the modular homomorphism is a normal subgroup with abelian quotient whose level sets have a strict relative threshold gap, so the amenable-quotient identity, Claim E and the diagonal formula all need unimodularity
distinct_from:
  fpbs-relative-threshold-is-quotient-l2-threshold: that is the open Claim E on Cayley graphs; this proves that the same identity, stated verbatim for a transitive automorphism group and a normal subgroup containing the stabilizers, is false on every nonunimodular pair, so no proof of Claim E can avoid unimodularity.
  fpbs-amenable-quotient-normal-relative-threshold-is-pc: that proves p_c(N;G) = p_c for amenable Gamma/N on Cayley graphs; this shows its conclusion fails for the modular kernel of every nonunimodular transitive group, whose quotient is abelian, and locates the failure at Step 5 (mass transport) of its proof.
  fpbs-quotient-l2-threshold-sandwich: that proves the diagonal formula ||sigma||_Q = limsup_m (chi^(N,m))^(1/m) on Cayley graphs; this shows the formula is false on the whole window (p_c, p_t) of every nonunimodular pair, because the fibre kernel satisfies sigma(c^(-1)) = c sigma(c) instead of sigma(c^(-1)) = sigma(c).
  fpbs-tree-product-relative-threshold-is-heaviness-threshold: that computes p_c(N;G) = p_h for the Cayley fibre group N = H of a tree product; this uses the nonunimodular modular kernel, whose orbits are whole horocycle slices, and needs no heaviness input.
  fpbs-hutchcroft-nonunimodular-pc-below-pt: that imports p_c < p_t; this uses it once, to put the level-set relative threshold strictly above p_c on every nonunimodular pair, and needs no import on trees.
  fpbs-percolation-kesten-normal-gap: that asks for a gap along normal subgroups with nonamenable quotient on Cayley graphs; this exhibits gaps with abelian quotient off Cayley graphs, so the Kesten dichotomy "gap iff nonamenable quotient" is a unimodular statement.
  fpbs-boundary-tilted-susceptibility-kernel: that tilts Cayley-graph percolation by boundary Radon-Nikodym cocycles with no subgroup; this uses the graph modular function to build a normal subgroup and a quotient kernel, and tests the quotient identities rather than the worst-pair rate.
---

**ESTABLISHED.** Proof route:
`fpbs-nonunimodular-level-sets-break-identity-e-proof`.

**Setting.** `G = (V,E)` is connected and locally finite, `Gamma ⊆ Aut(G)`
is transitive, and `o in V`. `Delta(x,y) = |Stab_y x| / |Stab_x y|` is
Hutchcroft's modular function, where `|Stab_y x|` is the size of the orbit of
`x` under the stabilizer of `y` (`fpbs-hutchcroft-nonunimodular-pc-below-pt`).
`tau_p`, `chi_p = sum_y tau_p(o,y)`, `chi_(p,lambda)`, `p_t = p_c(G,Gamma,1/2)`
are as in that node. Write `p_T = sup{p : chi_p < infinity}`, so `p_T <= p_c`.

Define the modular homomorphism `delta(gamma) = Delta(o, gamma o)`,
`N_Delta = ker delta`, `D = delta(Gamma) ⊆ (0,infinity)` and `L = N_Delta o`.
For a set `A ⊆ V` put `p_c(A;G) = sup{p : E_p |K_o ∩ A| < infinity}`.
The fibre kernel and the multi-chain susceptibilities are

```text
sigma_p(c) = sum_(y : Delta(o,y) = c) tau_p(o,y)         (c in D),
chi^(L,m)_p = sum_(y in L) T_p^m(o,y) = sigma_p^(*m)(1),
```

with `S_p f(a) = sum_b sigma_p(b/a) f(b)` on `l2(D)`. These are the objects of
`fpbs-quotient-l2-threshold-sandwich`, with `Gamma/N` replaced by
`Gamma/N_Delta = D`. Put `p^(l2)(L) = sup{p : ||S_p|| < infinity}` and
`p^(diag)(L) = sup{p : limsup_m (chi^(L,m)_p)^(1/m) < infinity}`.

**Theorem.** Suppose `Gamma` is nonunimodular.

1. **Structure.** `delta` is a homomorphism, and `Delta(x, gamma x) =
   delta(gamma)` for every `x`. `N_Delta` is normal and contains every vertex
   stabilizer. `Gamma/N_Delta ≅ D` is a nontrivial abelian group, hence
   amenable. The `N_Delta`-orbits are the level sets
   `L_c = {y : Delta(o,y) = c}`, and `L = L_1` is **infinite**.
2. **Twisted symmetry of the fibre kernel.** For every `x` with
   `Delta(o,x) = a`, `sum_(y in L_b) tau_p(x,y) = sigma_p(b/a)`. So `S_p` is
   the quotient kernel, a convolution on `D`. Instead of the Cayley symmetry
   `sigma(c^(-1)) = sigma(c)`, it satisfies
   `sigma_p(c^(-1)) = c sigma_p(c)`. The half tilt
   `s_p(c) = c^(1/2) sigma_p(c)` is symmetric, and `sum_c s_p(c) = chi_(p,1/2)`.
3. **The quotient l2 threshold is blind.** `||S_p|| = chi_p` in
   `[0,infinity]`, so `p^(l2)(L) = p_T <= p_c(G)`.
4. **The chain.**

   ```text
   p^(l2)(L) = p_T <= p_c(G) < p_t <= p^(diag)(L) <= p_c(L;G).
   ```

   The strict inequality is Hutchcroft's `thm:pcpt`. In particular, for every
   `p in (p_c, p_t)`:
   - `E_p |K_o ∩ L| < infinity`, so a.s. every cluster meets every level set
     finitely;
   - `||S_p|| = infinity`, while `limsup_m (chi^(L,m)_p)^(1/m) <= chi_(p,1/2) < infinity`.
5. **Trees, explicitly (no import).** Let `T_k` be the `k`-regular tree,
   `k >= 3`, with `xi` an end, `Gamma = Aut(T_k)_xi`, and `L` the horocycle
   of `o`. Then `D = (k-1)^Z`, and

   ```text
   p^(l2)(L) = p_c(T_k) = 1/(k-1)  <  1/sqrt(k-1) = p_t = p^(diag)(L) = p_c(L;T_k)  <  p_u(T_k) = 1.
   ```

**What this refutes, verbatim off Cayley graphs.** Read with `(Gamma, N)`
a transitive automorphism group and a normal subgroup containing the
stabilizers, each of the following Cayley-graph statements is **false** on
every nonunimodular pair `(G, Gamma, N_Delta)`:

- **C3 / the amenable-quotient identity** (`fpbs-amenable-quotient-normal-relative-threshold-is-pc`):
  amenable `Gamma/N` gives `p_c(N;G) = p_c(G)`. Here `Gamma/N_Delta` is
  abelian but `p_c(L;G) >= p_t > p_c`. Its conclusion also fails. On
  `(p_c, min{p_t, p_u})` no cluster meets `L` infinitely, although this is
  inside the nonuniqueness window. The interval is nonempty because
  `p_c < p_h <= p_u` (`fpbs-hyperbolic-and-nonunimodular-nonuniqueness`), and
  on `T_k` it is `(1/(k-1), 1/sqrt(k-1))`.
- **Claim E and its weak form E'** (`fpbs-relative-threshold-is-quotient-l2-threshold`):
  the pair is literally of **type (ii)** in C1, `p^(l2) < p_c(L;G)` with
  `p^(l2) <= p_c` (and `= p_c` by sharpness, which the chain does not use).
- **The diagonal formula** (sandwich, part 1): `||S_p|| = infinity` while the
  diagonal rate is finite, on the whole window `(p_c, p_t)`.
- **The Kesten dichotomy** "a relative gap iff the quotient is nonamenable".
  The same failure already occurs for random walk. The height of simple
  random walk on `T_k` is a walk on `Z` with drift, so returns to the
  horocycle have rate `2 sqrt(k-1)/k < 1`, although the quotient is `Z`.

**The invariant and the step where every member dies.** The invariant is
the modular function, equivalently the defect `sigma(c^(-1))/sigma(c) = c` of
the fibre kernel. Consider any argument for C3, Claim E (l2 form) or the
diagonal formula that uses only the following:

- Bernoulli percolation tools valid on every transitive graph: BK, Russo,
  FKG, insertion and deletion tolerance, trifurcations, sharpness;
- invariance of the law under `Gamma`;
- the harmonic analysis of `Gamma/N`: Folner sets, weak containment, Fourier
  analysis.

Such an argument, run on `(T_k, Aut(T_k)_xi, N_Delta)`, would prove a false
statement there. So every correct proof must use the **mass-transport
principle with trivial modular function**. In the recorded proofs this
happens exactly at the following two places.

- Step 5 of `fpbs-amenable-quotient-normal-relative-threshold-is-pc-proof`
  ("`Gamma` is unimodular, and ... the mass-transport principle applies").
  On the tree at `p in (1/(k-1), 1/sqrt(k-1))`, the hypothesis reached at the
  end of Step 0 is true: every cluster meets every horocycle finitely. Steps
  1-4 then go through with `Gamma`-invariance in place of left
  multiplication. Trifurcations have positive density, the cells are finite
  unions of horocycles, and each cell cluster is finite. Only Step 5 fails.
- Item (0d) of `fpbs-quotient-l2-threshold-sandwich-proof`, the symmetry
  `sigma(q^(-1)) = sigma(q)` from `x -> x^(-1)`, which feeds its Step 1.

**What survives (open, not claimed).** On Cayley graphs the diagonal formula
makes the following two identities the same statement:

- `E`: `p_c(N;G) = p^(l2)`;
- `E_diag`: `p_c(N;G) = p^(diag)(N;G)`.

Off Cayley graphs they separate, and only `E_diag` survives the test: on
`T_k` the chain collapses to `p_t = p^(diag) = p_c(L;T_k)`. So `E_diag` is
the form of Claim E that can hold for all transitive pairs, and `E` is its
unimodular shadow. A proof of Claim E that goes through multi-chain
susceptibilities, rather than operator norms on `l2(Q)`, is not touched by
this calibration.

Whether `p_c(L;G) = p_t` on every nonunimodular pair is open. By Timar's
slab lemma (`fpbs-timar-infinitely-many-heavy-clusters-percolate-in-a-slab`),
light clusters meet every slab finitely. So a relative sharpness statement
for level sets, which is not on the board, would give `p_c(L;G) >= p_h`.
Hutchcroft notes that `p_t < p_h` can happen, and on such a pair even
`E_diag` would need `p^(diag) > p_t`.
