---
rg: 2
id: reduced-amalgam-canonical-trace-is-mf
kind: claim
title: The canonical trace on the Kun-Thom group double amalgam is an MF trace
distinct_from:
  shulman-symmetric-double-has-no-stable-trace-upgrade: that is the negative source-scope correction, recording that arXiv:2603.13564v2 contains no theorem promoting Hilbert--Schmidt stability of a vertex algebra to MF-ness of a prescribed trace on the double; this is the positive statement that one specific trace on one specific double is MF, i.e. the hole that correction leaves open.
  symmetric-double-weak-mf: that embeds every such group double in an auxiliary MF completion built from a profinite regular vertex model; it neither makes the full group C-star algebra MF nor selects the canonical trace on it.
  shulman-amalgam-mf-criterion: that imports Shulman's Theorem 16 corona-embedding criterion for general amalgams as a literature fact; this is an open question about the trace on one instance, not an import.
  hyperlinear-trace-not-mf-trace: that separates the two trace classes on this repository's constructed group; this asks whether the two coincide on the Kun--Thom double, and is not settled by that separation, which concerns a different group.
  kt-double-mixed-word-trace-selection: that asks only for normalized-Hilbert--Schmidt models with the canonical mixed reduced-word traces; this asks for the strictly stronger operator-norm MF approximation of the canonical trace.
  kt-double-reduced-cstar-is-mf: that asks for a norm-corona embedding of the reduced group C-star algebra; by unique trace it implies the present claim, but the converse is not known because an MF trace need not kill its GNS kernel in operator norm.
  faithful-mf-models-realize-all-mf-traces: that can add asymptotic isometry to an MF-trace model only when the ambient C-star algebra is already MF; MF-ness of the full group C-star algebra here is not known.
artifacts:
  - research/artifacts/hyperlinear-firewall-dossier-2026-08-24.md
  - research/artifacts/shulman-2603-13564-verified.md
  - research/artifacts/kt-double-mf-trace-literature-audit-2026-08-30.md
---

Fix the binary Kun--Thom Theorem E pair

```text
Gamma = EL_r(F_2[x_1,...,x_d]),
G = EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),
r,d >= 3,
```

and let

```text
D = G *_Gamma G,        C*(D) = C*(G) *_(C*(Gamma)) C*(G)
```

be the group double and its full amalgam, and let `tau` be the canonical group
trace on `C*(D)`.

**Claim.**  `tau` is an **MF trace in Shulman's sense**: there are maps
`phi_n:C*(D)->M_(d_n)(C)`, not assumed linear, positive, unital, or
completely positive, such that for every `a,b` and `lambda,mu in C`,

```text
||phi_n(ab)-phi_n(a)phi_n(b)|| -> 0,
||phi_n(lambda a+mu b)-lambda phi_n(a)-mu phi_n(b)|| -> 0,
||phi_n(a*)-phi_n(a)*|| -> 0,
sup_n ||phi_n(a)|| < infinity,
tr_(d_n)(phi_n(a)) -> tau(a).                                  (RAT1)
```

The three defect limits are in **operator norm**.  This is what makes the
claim stronger than hyperlinearity of `D` and puts it in the scope of
Shulman's lifting machinery; see the route
`hyperlinear-nonsofic-from-mf-amalgam-trace` for the payoff.

Requiring the maps in `(RAT1)` to be u.c.p. would instead ask for a
quasidiagonal trace, a strictly stronger notion.  Requiring asymptotic
isometry would additionally prove that the full algebra `C*(D)` is MF.
Neither strengthening is part of the MF-trace definition, and neither is
currently known here.

## Attempts

1. **Shulman Theorem 10 directly.**  The actual application in
   `symmetric-double-weak-mf` starts from an auxiliary profinite regular
   completion `A=C*(rho(G))`, not from the full algebra `C*(G)`, and proves
   that `A *_(C*(rho(Gamma))) A` is MF.  The group `D` embeds in that
   auxiliary amalgam, but this does not identify it with `C*(D)` and selects
   **no trace** on the group.  Even on an MF algebra, arbitrary faithful
   coordinates need not converge to a prescribed trace.  Dies at trace
   selection.  `shulman-symmetric-double-has-no-stable-trace-upgrade`
   records that current arXiv v2 contains no theorem closing this step.

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

6. **Reduced-algebra certificate and the exact CE boundary.**  For this
   binary pair, `kt-q2-reduced-cstar-has-unique-trace` and
   `monotracial-mf-algebra-has-mf-trace` show that
   `kt-double-reduced-cstar-is-mf` would imply `(RAT1)` by pullback along
   `C*(D)->C*_r(D)`.  No converse is known: operator-norm MF-trace models may
   retain their GNS-null ideal on trace-zero, full-operator-norm corners.
   At the Hilbert--Schmidt level, Gao's Appendix Theorem 7.1 gives the exact
   statement

   ```text
   D hyperlinear  <=>  L(Gamma) subset L(G) is RE/C.
   ```

   This is `kt-q2-double-hyperlinear-iff-relative-embeddable`.  Thus the node
   is genuinely open.  It is not equivalent to a general MF-permanence
   theorem for reduced amalgams: reduced MF is a sufficient stronger
   certificate, while the exact known equivalence is the relative-
   embeddability condition for this one nonamenable inclusion.
