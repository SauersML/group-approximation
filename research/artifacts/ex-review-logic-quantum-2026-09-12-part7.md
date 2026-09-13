# EX review, logic and quantum: part 7. The SoS completeness-one-half crux (ex-ugc) and hidden labels (ex-kac-quantum-bijection)

Lane `ex-verify-logic-quantum`, 2026-09-13 02:40 CDT.  Index: `ex-review-logic-quantum-2026-09-12.md`.

## 7.0 Verdicts

| item | lane | verdict |
|---|---|---|
| `sos-cannot-refute-unique-games-at-completeness-one-half` | ugc | Correctly OPEN.  **Credit finding:** the source statement exists.  KMS ECCC TR18-006, Appendix B, p. 54, records polynomial-round Lasserre gaps for 2-to-2 Games with perfect completeness, obtained by translating the 3Lin gap through the reduction.  Crux (i) of the Attempts is what KMS assert, informally.  Corrected forward in the node's Literature bullet |
| `hidden-labels-import-cross-context-commutation` (+ `-proof`) | kac-quantum-bijection | PASS |

## 7.1 The SoS claim: what the source says and what remains

**Verbatim**, KMS, *Pseudorandom Sets in Grassmann Graph have Near-Perfect Expansion*, ECCC TR18-006,
Appendix B "Significance of the 2-to-2 Games Theorem", p. 54, under "(Lasserre) Integrality Gaps with
Perfect Completeness":

> "Integrality gap (say up to a polynomial number of rounds of the Lasserre relaxation) for the 2-to-2
> Games problem holds with perfect completeness and soundness ε."

and p. 55:

> "These results are a consequence of the integrality gap known for the 3Lin problem with perfect
> completeness [6, 15] and the fact that the proof of the 2-to-2 Games Theorem is a reduction from 3Lin.
> The integrality gap instance for 3Lin can be 'translated' via the reduction."

Here [6] is Grigoriev, TCS 259 (2001), and [15] is Schoenebeck, FOCS 2008.  The same appendix, p. 55,
states "GapUG(1/2 − ε, ε) is NP-hard", which is `unique-games-hard-at-completeness-one-half`.

**From the 2-to-2 gap to the UG claim (re-derived).**
- Each 2-to-2 constraint `T x_i + T' x_j in {b, b'}` splits into two unique constraints of weight
  `w_c/2` (`unique-games-hard-at-completeness-one-half-proof`).
- In the label-indicator encoding, when `b != b'`, the satisfaction indicator of the 2-to-2 constraint
  is the sum of the two branch indicators.  These are disjoint events under the one-hot constraints,
  and the identity has degree 2.
- A pseudo-expectation is linear and respects the one-hot constraints, so the pseudo-value of the
  split instance is half that of the source.  When `b = b'`, the two copies give the full weight
  `w_c`, which is at least half.
- A degree-`D` pseudo-distribution of pseudo-value `1` for the 2-to-2 instance therefore gives
  pseudo-value `>= 1/2` for the UG instance at the same degree.
- Integral soundness passes as in the NP-hardness proof: `OPT(U') <= OPT(U) <= eps`.

**What this settles, and what it does not.**
- **Crux (i)**, completeness via low-degree identities from the 3Lin equations, is precisely the
  "translation" KMS assert.  The completeness in the gap is *perfect*, because the Grigoriev /
  Schoenebeck pseudo-distribution satisfies every equation.  The `1 - eps` completeness of the
  NP-hardness comes from the outer PCP, not from the translation.
- **Crux (ii)**, soundness on random source instances, is covered by the same sentence.  KMS's
  soundness analysis is a decoding statement that applies to any outer instance of small value.
- **Crux (iii)**, size and degree: the source says only "say up to a polynomial number of rounds".
  No exponent is given.  The node's `c = c(eps)` form is consistent with that.
- **Status.**  The remark is informal and carries no theorem number.  The graph is right to keep
  the node OPEN until the translation is written as a derivation, or a source proves it.
- **Credit.**  The node's Literature bullet, "A bounded web search ... did not locate this
  statement", is superseded.  The 2-to-2 SoS gap is recorded by KMS, and the UG form follows in two
  lines.  So a landed derivation would be a write-up of a stated consequence, not a new result.

**Where a write-up must be careful.**  For a degree bound one needs the Grassmann labels of the outer
questions to be polynomials of degree `O(t + l)` in the 3Lin variables of their `t`-block.  These are
linear functions restricted to `l`-dimensional subspaces.  One also needs every 2-to-2 constraint
between honest labels to hold as a polynomial identity modulo the ideal of the `O(t)` source equations
involved.  The smoothness and zoom steps of the outer PCP must be checked to use only such local
consistency.  This was not done here.

## 7.2 Hidden labels: PASS

- **(H1).**  Block sums `[ell_e = lambda]` equal the neighbour's block sums, by (R3) of the
  rectangular-splitting proof, so they lie in `W*(p_(c'))`.  Shared variables are constant on blocks.
- **(H2).**  The support coset `s_c K~` maps onto a coset of `T = {(k N', k N'')}` because `N_e` is
  normal.
- **(H3).**
  - Goursat makes the coset a disjoint union of full rectangles `C'_j x C''_j`.
  - Each `m_j` has two block-sum expressions, so it lies in `W*(p_c) ∩ W*(p_(c')) ∩ W*(p_(c''))` and
    commutes with all three PVMs.
- **(H4).**  A full rectangle of label pairs lies in `Allowed_c|_(u,w)`, which misses a pattern.  So
  one side is a singleton.
- **(H5).**  On `m`, `X_u m = sum ± m_j in W*(p_(c''))`, hence `[X_u, P_(c'')^b] m = [X_u m, P_(c'')^b] = 0`.
  Symmetrically on `1 - m`.
- **Model test.**  The `M_3` model is perfect, and its symmetries do not commute across contexts.  So
  (HL) is not automatic.
