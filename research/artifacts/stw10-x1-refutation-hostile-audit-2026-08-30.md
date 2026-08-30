# STW X(1) refutation: hostile audit of the factorization-property chain

*2026-08-30 goal session, second lane's audit of the graph's headline
result: `stw99-problem-x1-fails-on-full-group-algebras` ESTABLISHED —
amenable traces need not be quasidiagonal; the literal group `E`
refutes STW Problem X(1) via `literal-fp-via-folner-rf-core` (the
factorization property) plus the standing
`literal-canonical-trace-hyperlinear-not-quasidiagonal`.*

## The three recorded dangers, each checked

1. **Entry collection is finite per stage.**  The Folner compression
   to an interval `F ⊂ Z` needs trace-vanishing on `~|F|` diagonal
   coefficients `α^{-j}(g)` — infinitely many across the diagonal
   sequence, but FINITELY many for each fixed `F`; the finitely
   generated subgroup `H = H_F` is re-chosen per stage, and one
   finite quotient separates that stage's collection.  No uniformity
   across stages is used anywhere, so the growing collection is
   harmless.

2. **"LEF" naming vs the property used.**  The proof needs f.g.
   subgroups of the telescope kernel `E_T` to be RESIDUALLY FINITE
   (not mere LEF, which would not suffice).  The requires-chain
   (`literal-telescope-core-lef` via the split normal form) carries
   exactly the locally-RF content: f.g. subgroups of `E_T` land in
   level truncations built from linear (hence Mal'cev-RF) pieces and
   finite Clifford data.  The label is historical; the content is
   local residual finiteness.

3. **Relative-(T) transport (this lane's recorded corner).**  The
   HS-multiplicative maps restrict to the Kazhdan base
   `B = Z³ ⋊ SL₃(Z)` and Kirchberg rigidity converts them to honest
   finite-dimensional representations of `B` — which is consistent,
   `B` being residually finite, and yields NO contradiction because
   finite-dimensional representations of `B` never see the mark.  The
   transport corner closes benignly.

## The structural reconciliation (why no contradiction with the no-gos)

This lane proved the mark `w` of `E` is invisible to (i) every
operator-norm corona model (source of non-QD), (ii) every finite
injective COVARIANT von Neumann model
(`literal-group-mark-invisible-to-hyperfinite-representations`), and
(iii) every hyperfinite GNS situation.  The FP construction evades all
three at once: its finite-dimensional data are representations of ONE
finitely generated subgroup `H ≤ E_T` — no `Σ`-covariance, no
norm-multiplicativity, no globally invariant trace — composed with a
non-multiplicative Arveson extension and a Folner compression whose
multiplicativity defect is Hilbert--Schmidt-small but norm-large.
Inside `H`, the mark is residually finite-VISIBLE (`q(w) ≠ e`), which
is exactly what the canonical trace needs.  So the dividing line the
program has been circling is now exact:

```text
the mark survives finite models of subgroups of the kernel;
it dies in any model that is covariant, normal, or norm-multiplicative.
```

Amenability (FP) lives on the first side, quasidiagonality on the
second — and STW Problem X(1) splits along it.

## What X(1)'s refutation does NOT touch

`C*(E)` is non-nuclear (E non-amenable) and the trace is not claimed
faithful-on-an-exact-algebra, so IX(1), VII, and the exact-case heart
X(2) (quasidiagonality of the hyperfinite II₁ factor's trace) are all
unaffected and remain open, as the graph records.
