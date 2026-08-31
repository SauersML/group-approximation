---
X(2) external status memo: ingestion and verification log (2026-08-30)
---

# X(2) external status memo — quarantined ingestion

The user relayed an external research memo (another model's research
pass) on STW Problem X(2), "is the hyperfinite II_1 factor R
quasidiagonal?".  Per house doctrine this file quarantines the input:
nothing below enters the trust surface; the graph nodes citing this
dossier record either verified literature imports or reconnaissance
whose provenance is this memo.

## Verification log (this session, 2026-08-30)

1. **Popa post: VERIFIED.**  Fetched
   `https://sorintpopa.wordpress.com/2026/05/28/q5-is-r-quasidiagonal/`
   ("Q5: Is R quasidiagonal?", W*-News, 2026-05-28).  The post frames
   the problem as open (quoting Brown--Ozawa: "this seems unlikely,
   but a proof would be nice") and gives the formulations imported by
   `popa-projection-formulations-of-x2`: the operator-norm
   finite-rank-projection Folner form, Connes' normalized
   Hilbert--Schmidt Folner form as what hyperfiniteness actually
   supplies, the local-AFD criterion (finite-dimensional `B` with
   support `s`, `||[y,s]|| < eps`, `||sys - E_B(sys)|| < eps`), and
   the suggestion that Voiculescu's Gaussian functor might convert
   Hilbert-norm estimates to operator-norm ones, possibly inside
   `R^omega`.
2. **Oberwolfach problem list: VERIFIED, memo's year WRONG.**  The TIB
   open-access report at
   `https://oa.tib.eu/renate/bitstreams/117dbc67-859d-47d3-8769-5ed7ab4e08e9/download`
   contains verbatim "Problem 16. Is the hyperfinite II1-factor R
   quasidiagonal?  Is it MF?".  The memo dated it 2026; the report's
   bibliography ends around 2015--2017 (TWW Ann. of Math. 185 (2017)
   listed), so it is from that era's C*-algebras workshop.  The
   substantive point survives: the MF variant is posed separately,
   which `hyperfinite-factor-mf` now records.
3. **No claimed resolution found.**  The memo reports a literature
   sweep through August 2026 finding no resolution; consistent with
   the Popa post (2026-05-28) and with STW v2 addenda through April
   2026 still listing X(2).

## Memo content adopted after checking

* **HS-vs-norm projection gap (checked by hand).**  Rank-`n`
  projections `P_n = P_V + e e*`, `Q_n = P_V + f f*` with `dim V = n-1`
  and `e, f` orthonormal, both orthogonal to `V`: then
  `P_n - Q_n = e e* - f f*` has eigenvalues `+-1`, so
  `||P_n - Q_n|| = 1` for every `n`, while
  `||P_n - Q_n||_2 / ||P_n||_2 = sqrt(2/n) -> 0`.  So there is no
  dimension-free upgrade from Connes' normalized-HS Folner condition
  to the operator-norm Folner condition: an asymptotically negligible
  fraction of bad directions is invisible in normalized 2-norm and
  fully visible in norm.  This is the same asymmetry the whole non-MF
  program exploits, now recorded at the projection level of X(2).
* **CAR-core normal form is self-similar, not inductive.**  The
  Morita reduction (`stw10-matrix-core-models-are-corner-amplifications`)
  moves all approximation data into a corner `pRp ~= R`; it produces
  a normal form, not descent.  Already recorded on the X(2) node;
  the memo independently confirms it.
* **Gaussian-functor reconnaissance (memo's, plausibility-checked
  only).**  Second quantization converts an almost-invariant
  Hilbert-space vector into strongly controlled operators, but what it
  naturally produces is a representation of the unitary group U(R)
  attached to `u tensor u-bar`; it does not extend linearly and
  multiplicatively to finite-dimensional C*-models of all of `R`.
  That linearization step is a reformulation of the missing theorem,
  not bookkeeping.  Recorded as an attempt on
  `norm-folner-projections-for-hyperfinite-factor`; not a claim.
* **Negative route unchanged.**  The memo confirms the graph's state:
  the open leaf is one non-MF countable group with a faithful
  character whose GNS closure is hyperfinite
  (`non-mf-subgroup-of-hyperfinite-factor-unitary-group`), with
  Kazhdan, literal-group, Clifford, and finite-packet candidates all
  excluded by landed theorems, and group-shaped subalgebra witnesses
  excluded by `x2-witnesses-are-never-group-shaped`.

## Memo content NOT adopted

* The "Oberwolfach problem session from 2026" dating (corrected above).
* Any suggestion that X(1)'s refutation bears on X(2) — the graph
  already proves the literal-group witness cannot enter (non-injective
  GNS), and the memo agrees.
* The memo's own bottom line — "I did not obtain a valid unconditional
  proof" — is adopted as the honest state of the problem: X(2) remains
  OPEN in both directions after this ingestion.  This dossier sharpens
  the frontier; it closes nothing.
