---
rg: 2
id: reduced-amalgam-canonical-trace-is-mf
kind: claim
title: The q=2, d=3 Kun--Thom double has full-norm MF coordinates carrying its canonical trace
refuted_by:
  - kt-full-double-cstar-is-not-mf
distinct_from:
  shulman-symmetric-double-has-no-stable-trace-upgrade: that is the negative source-scope correction, recording that arXiv:2603.13564v2 contains no theorem promoting Hilbert--Schmidt stability of a vertex algebra to MF-ness of a prescribed trace on the double; this node records that the stronger full-norm formulation is actually impossible at the explicit endpoint.
  symmetric-double-weak-mf: that embeds the abstract double group into an auxiliary MF amalgam; it neither embeds the universal full group C-star algebra nor selects the canonical trace, and the present refutation shows that the former strengthening is impossible.
  shulman-amalgam-mf-criterion: that imports Shulman's Theorem 20 corona-embedding criterion for general auxiliary amalgams as a literature fact; this is the now-refuted attempt to apply a full-norm conclusion to the universal algebra of one group double.
  hyperlinear-trace-not-mf-trace: that separates the two trace classes on a different constructed group; this records a direct full-norm obstruction at the explicit Kun--Thom double and leaves its hyperlinearity undecided.
  kt-double-mixed-word-trace-selection: that still-open node asks only for normalized-Hilbert--Schmidt models with the canonical mixed reduced-word traces; this refuted node demanded the strictly stronger asymptotically isometric operator-norm approximation.
artifacts:
  - research/artifacts/hyperlinear-firewall-dossier-2026-08-24.md
  - research/artifacts/shulman-2603-13564-verified.md
---

Fix `q=2`, `d=3`, and `r>=3` in the explicit Kun--Thom Theorem E pair

```text
Gamma = EL_r(F_2[x_1,x_2,x_3]),
G = EL_r(F_2[x_1^(+-1),x_2^(+-1),x_3^(+-1)]) rtimes SL_3(Z),
```

and let

```text
D = G *_Gamma G,        C*(D) = C*(G) *_(C*(Gamma)) C*(G)
```

be the group double and its full amalgam.  Let `tau` be the canonical group
trace on `C*(D)`.

**REFUTED AS STATED.**  The requested maps cannot exist because the claim
includes asymptotic isometry for the **full** norm.  The group `D` inherits a
strict Kazhdan compression from either vertex, so
`kt-full-double-cstar-is-not-mf` proves that `C*(D)` has a proper-isometry
witness and admits no MF embedding.  Asymptotic multiplicativity plus
asymptotic isometry would define exactly such an embedding into the norm
matrix corona.  Trace convergence cannot repair this obstruction.  No
assertion is made here about an unrelated Kun--Thom pair lacking a strict
compressor.

The refuted demand was: there are `d_n -> infinity` and unital
completely positive maps `phi_n : C*(D) -> M_(d_n)(C)` which are
asymptotically multiplicative and asymptotically isometric in **operator
norm**, with

```text
tr_(d_n) o phi_n -> tau   pointwise.                             (RAT1)
```

The operator-norm isometry requirement is what makes the displayed statement
false.  This refutation does not decide whether the canonical trace is MF in
a nonfaithful trace-only convention, whether it is hyperlinear, or whether
`C*_r(D)` is MF.

## Attempts

1. **Shulman Theorem 10 directly.**  The weak-MF proof first replaces
   `C*(G)` by an auxiliary MF completion `A=C*(rho(G))`, and then proves
   `A *_C A` MF.  It is **not** `C*(D)`: the latter is not MF by the refuter
   above.  The injective group homomorphism `D->U(A *_C A)` therefore induces
   a noninjective map on maximal group C-star algebras.  Trace selection was
   not the only missing step; full-norm faithfulness was already impossible.
   `shulman-symmetric-double-has-no-stable-trace-upgrade` separately records
   that the paper also supplies no prescribed trace.

2. **Shulman arXiv:2508.00125, Corollary 35.**  Hyperlinear traces on `B` are
   MF when `B` is homotopy dominated by a Hilbert--Schmidt-stable algebra.
   For `B = A *_C A` the fold and one vertex inclusion show `A` is dominated
   by `B` -- the opposite direction from the hypothesis needed.  Dies on the
   missing homotopy from the fold retraction to the identity of the double.

3. **Weaken the target to "`tau` is a hyperlinear trace".**  Recorded and
   rejected, not parked: `tau` hyperlinear is literally `L(D)` Connes
   embeddable, i.e. `D` hyperlinear, so that version of the statement is a
   restatement of the target of the payoff route and buys nothing.  The
   operator-norm demand in `(RAT1)` is exactly what keeps this a genuine
   strengthening with a machine attached.

4. **Why no formal upgrade exists from (1).**  Norm data does not pin a
   trace at any finite stage.  A rank-one modification

```text
U_n = diag(-1, 1, ..., 1) in U(n),
||U_n - I|| = 2,        ||U_n - I||_2 = 2 / sqrt(n) -> 0,
```

   is maximal in operator norm and invisible in normalized Hilbert--Schmidt
   norm.  So the two topologies separate on exactly the perturbations a
   trace cannot see, and no soft argument turns an MF embedding of the
   algebra into control of `tau`.  This is the reason the hole is real
   rather than bookkeeping.

5. **Exact weaker trace target.**
   `kt-double-hyperlinear-iff-mixed-word-trace-selection` identifies the
   merely hyperlinear endpoint exactly: besides asymptotic vertex models,
   agreement on `Gamma`, and canonical vertex marginals, one must make every
   nontrivial reduced alternating word asymptotically traceless.  The open
   claim `kt-double-mixed-word-trace-selection` asks for exactly those data.
   The present MF-trace claim implies it, but not conversely.  This is a
   finite-window unpacking of the gap, not a reduction of its logical
   strength.
