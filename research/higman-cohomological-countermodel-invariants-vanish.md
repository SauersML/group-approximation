---
rg: 2
id: higman-cohomological-countermodel-invariants-vanish
kind: claim
title: Every two-cohomology and almost-flat index obstruction vanishes on Higman groups, so no cohomological countermodel to the four-cycle collapse exists
artifacts:
  - research/artifacts/higman-acyclic-cohomology-kill-2026-09-17.md
distinct_from:
  higman-four-cycle-intrinsic-mf-seed: that is the open operator-norm collapse (HMF2)=>(HMF3); this proves that the entire cohomological refutation lane for it is empty, and it neither proves nor refutes the collapse.
  dadarlat-matricial-stability-obstruction: that imports Dadarlat's theorem that nonzero even rational cohomology obstructs stability; this shows its hypothesis, and that of every relative of it, fails for every generalized Higman group.
  laurent-sl4-not-matricially-stable-for-q-at-least-4: that is a successful instance of the delocalized Dadarlat lane (route laurent-sl4-instability-from-delocalized-dadarlat) for a group with torsion; this shows the same lane is empty for Higman groups, because they are torsion-free and their integral two-homology vanishes.
  exel-loring-mark-quantization: that deploys the Exel--Loring pairing against a central mark of an extension; this computes that the pairing group H_2 is zero for every Higman cycle, so no pairing can be nonzero.
  one-small-higman-generator-collapses-the-four-cycle: that is a basin estimate constraining countermodels analytically; this is a topological constraint that holds for every asymptotic representation of every profile.
---

**ESTABLISHED (obstruction; written proof, not Lean-verified).**

For `k >= 1` and `m >= 2`, let

```text
H_k(m) = < g_i, i in Z/k | g_i g_(i+1) g_i^(-1) = g_(i+1)^m >,
```

so that `Hig = H_4(2)`.  Let `X_k(m)` be its presentation 2-complex.

1. **Two-homology vanishes.**  `H_2(X_k(m);Z) = 0` and `H_2(H_k(m);Z) = 0`.
   Also `H_1(H_k(m);Z) = (Z/(m-1))^k`, so `H_1(Hig;Z) = 0`.  Neither statement
   needs asphericity or nontriviality of the group.
2. **The obstruction groups vanish.**  For every real or complex vector space
   `V` with trivial action, `H^2(H_k(m);V) = 0`.  In particular:
   - the Dadarlat--Glebe class `[rho] in H^2(Gamma, Q(R))` (unitary case) or
     `H^2(Gamma, Q(C))` of any asymptotic homomorphism into any sequence of
     unital tracial `C*`-algebras or Banach algebras is zero;
   - every Exel--Loring / Kazhdan winding-number invariant, indexed by
     `x in H_2(Gamma;Z)`, is the zero invariant;
   - the nonstability criteria of Dadarlat--Glebe Theorems 1.1, 1.2(1), 1.4
     and Corollary 1.3 never apply.
3. **For `Hig` itself everything vanishes.**  By Baumslag--Dyer--Heller (cited
   verbatim in the artifact), `X_4(2)` is a classifying space and `Hig` is
   acyclic and torsion-free.  Therefore:
   - `H^(2j)(Hig;Q) = 0` for all `j >= 1`, so Dadarlat's Theorem 1.1 of
     arXiv:2007.12655 does not apply;
   - the only finite-order conjugacy class is `{1}`, so the delocalized
     sectors of `weak-matricial-stability-kills-centralizer-even-cohomology`
     reduce to the `g=1` sector, which vanishes;
   - `K^0(X_4(2)) = Z` (rank) and `K_0(X_4(2)) = Z` (point class), so every
     almost-flat bundle on `BHig` built from a quasi-representation is stably
     trivial, and every index pairing of a quasi-representation of `Hig`
     equals that of the trivial representation of the same dimension.

## Obstruction (class killed)

**Class.**  The class is every refutation of `higman-four-cycle-intrinsic-mf-seed`
that certifies non-collapse through a cohomological or index invariant.  This
includes:

- Voiculescu--Kazhdan central-extension almost-representations;
- Exel--Loring and Bott winding numbers of commutator products;
- Dadarlat almost-flat K-theory and its delocalized form at torsion;
- the Dadarlat--Glebe de la Harpe--Skandalis obstruction class;
- twisted-group-algebra quotients `C*(Gamma, sigma_theta)` with
  `[sigma] != 0`.

For the four-cycle this class also covers every generalized cycle
`H_k(BS(1,m))`.

**Invariant.**  `H_2(H_k(m);Z) = 0` together with `H_1(H_k(m);Q) = 0`.  For
`Hig` the invariant is full integral acyclicity with torsion-freeness.

**Step where every member dies.**  The pairing step.  Each method produces an
element of `H^2(Gamma;V)`, `H^(2j)(Gamma;Q)` or a delocalized sector, or pairs
a quasi-representation against `x in H_2(Gamma;Z)` or `K_0(BGamma)`.  All of
these groups are zero, or equal to the rank summand, for `Hig`.  So the
invariant of any asymptotic representation of any profile agrees with that of
the trivial representation, and it cannot certify distance from it.

**What survives.**  A countermodel to `(HMF3)` must be cohomologically
invisible.  The refutation lanes not touched here are non-index:

- a nontrivial amenable or MF-representable quotient, where TWW makes
  `C*(Q)` quasidiagonal;
- spectral clock and matcher constructions, such as
  `order-four-bs-matcher-builds-higman-opnorm-microstate`;
- saturation or model-theoretic arguments in the corona.

This result does not prove `(HMF3)`.  Vanishing obstructions give no
perturbation theorem, and no current stability theorem converts `H^2 = 0`
into operator-norm stability for a non-amenable group.

**Calibration.**  The same lane succeeds for `SL_4(F_q[t^(+-1)])` in
`laurent-sl4-instability-from-delocalized-dadarlat`, through a torsion
centralizer carrying a torus.  The Higman seed was chosen torsion-free and
lies outside its reach by construction.
