---
rg: 2
id: bernoulli-bc-splits-into-host-and-cylinder-comparison
kind: claim
title: Baum--Connes at a Bernoulli coefficient is the host's trivial-coefficient conjecture plus one reduced cylinder comparison, which is an isomorphism modulo every finite support level
distinct_from:
  monster-bc-failure-at-measured-coefficient-is-the-module-crux: that poses question (Q), failure of Baum--Connes at a measured dual-module coefficient; this proves that at the Bernoulli coefficient (Q) splits into the host's own trivial-coefficient conjecture and one explicit comparison map on reduced K-theory.
  amenable-kernel-bc-transfer-and-ktop-half-exactness: that transfers Baum--Connes along amenable kernels; this computes the topological side of a Bernoulli coefficient for every host and isolates what remains on the reduced side.
  lueck-surjective-assembly-traces-lie-in-lambda-g: that imports Lück's trace theorem; this applies it to F_p wr_Z G, where the Haar trace becomes a detector for (Q) with target ring Z[1/p].
---

**ESTABLISHED** by `bernoulli-bc-splits-into-host-and-cylinder-comparison-proof`. Full statement and
proofs: `research/artifacts/bc-bernoulli-cylinder-comparison-2026-09-13.md`.

**Setting.** `G` is countable discrete and `Z` a countable `G`-set with finite point stabilizers. `Λ = {0, ..., n}`,
`X = Λ^Z`, `I_k = C_0({x : |supp x| >= k})`, so `I_1 = C_0(X \ {0})`. `S` is the `G`-set of pairs `s = (F, a)`, with
`F ⊆ Z` finite nonempty and `a : F -> Λ \ {0}`, and `C_s = {x : x|_F = a}`. For `n = p - 1`, `C(X) ⋊_r G` is
`C*_r(F_p wr_Z G)`.

**Theorem.**
1. **Host splitting.** `mu_(G, C(X)) = mu_(G, C) ⊕ mu_(G, I_1)`, each half separately. This only uses the fixed point
   `0`, and every module dual has one: the trivial character.
2. **Going-down, for every `G`.** There is a weak K-equivalence `T ∈ KK^G(c_0(S), I_1)`. So
   `K^top_*(G; I_1) ≅ ⊕_([s] ∈ G\S) K_*(C*(G_s))`.
3. **Reduction.** `mu_(G, I_1)` is surjective (resp. injective) iff `T_r = K_*(T ⋊_r G)` is.
4. **Cylinder form (torsion-free `G`).** `T` may be taken to send `delta_s ↦ 1_(C_s)`. Then `mu_(G, I_1)` is an
   isomorphism iff the cylinder classes `[1_(C_s)]`, one per orbit, form a `Z`-basis of `K_0(I_1 ⋊_r G)` and
   `K_1(I_1 ⋊_r G) = 0`.
5. **Tail (torsion-free `G`).** For each `k >= 1`, `T_r` is an isomorphism iff its restriction
   `K_*(c_0(S_(>=k)) ⋊_r G) -> K_*(I_k ⋊_r G)` is.
6. **Group form.** For `p` prime, `n = p - 1` and torsion-free `G`, reduced assembly for `F_p wr_Z G` is surjective
   (resp. injective) iff it is for `G` and `T_r` is surjective (resp. injective).
7. **Trace detector.** For torsion-free `G`, `Λ^(F_p wr_Z G) = Z[1/p]` and `τ[1_(C_s)] = p^(-|F|)`. A projection over
   `C*_r(F_p wr_Z G)` with trace outside `Z[1/p]` refutes surjectivity for `G` or for `T_r`.

**Consequences for `monster-bc-failure-at-measured-coefficient-is-the-module-crux`.**
- At the Bernoulli coefficient over a torsion-free host, (Q) is the host's own trivial-coefficient conjecture or a
  failure of `T_r`: the cylinder projections of the single ideal `C_0((Z/p)^Z \ {0}) ⋊_r G` fail to be a free basis,
  or its `K_1` is nonzero. No module triple is involved.
- A failure of `T_r` persists in `I_k ⋊_r G` for every `k`, so it is carried by configurations of unbounded support.
  The indicator configurations of a monster's embedded expanders are of this kind. The proper finite-support strata are
  always fine.
- The Haar trace is a live detector for (Q) at this coefficient, through Lück's ring `Z[1/p]`. The crux node's
  exclusion of traces concerns separating `ker q_*` from `im i_*` in a module triple. A failure of `T_r` whose classes
  have traces in `Z[1/p]` is invisible to the trace.

**Model tests.**
- `n = 0` gives `S = ∅`, `I_1 = 0` and `mu_(G, C(X)) = mu_G`.
- For `G = Z = Z` and `p = 2`, Pimsner--Voiculescu gives `K_0(I_1 ⋊ Z) = ⊕_([s]) Z` on the cylinder classes and
  `K_1(I_1 ⋊ Z) = 0`. So `T_r` is an isomorphism, as the amenable group `F_2 wr Z` requires.

**Scope.**
- Items 4 and 5 are written only for torsion-free `G`. Item 4 extends to finite point stabilizers, with `R(G_s)`
  summands, and item 6 to every `G`; see Claim W and Corollary R4' of
  `research/artifacts/bc-bernoulli-rank-functionals-torsion-2026-09-13.md`.
- The extension to permutational coefficients `C((Z/p)^(G/H))` with `H` infinite amenable, as in the module-triple
  survivors, is not written.
