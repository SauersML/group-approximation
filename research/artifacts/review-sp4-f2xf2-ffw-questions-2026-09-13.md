# Review: Sp4 LLP calibration on F2 x F2 and the finite-index Theorem A fence (2026-09-13)

Independent adversarial review of two commits by session 01UM7nByUPBRzW6q2CVrVhTz:

- `79981c886`, "Calibrate the Sp4 LLP hole on F2 x F2: positive side answers
  FF-W Questions 1.6 and 1.9" (artifact
  `research/artifacts/sp4-llp-decide-2026-09-13.md`);
- `42efd7440`, "Fence ISW Theorem A on every finite-index subgroup of Sp4(Z)"
  (claims `isw-theorem-a-has-no-data-on-sp4-finite-index-subgroups` and
  `sp4-finite-index-fd-projective-multiplier-is-finite`, their two routes, and
  the Chevalley--Eilenberg script).

Neither file changed on main after these commits.

Sources, read locally with `pdftotext -layout` from PDFs fetched on MSI.
Page numbers are printed page numbers, checked against the running heads.

- [FFW] F. Fournier-Facio, R. Willett, arXiv:2603.18456v2 (83 pp., dated
  17 Apr 2026 on the arXiv stamp).
- [ISW] A. Ioana, P. Spaas, M. Wiersma, arXiv:2006.01874 (28 pp.).
- [BMS] Bass--Milnor--Serre, Publ. IHES 33 (1967).
- [Laz] M. Lazard, *Groupes analytiques p-adiques*, Publ. IHES 26 (1965).

## Verdict summary

| # | Claim | Verdict |
|---|---|---|
| V1 | Commit subject of `79981c886`: "positive side answers FF-W Questions 1.6 and 1.9" | **FAIL as worded.** Nothing is answered. |
| V2 | Calibration section 0 of `sp4-llp-decide-2026-09-13.md` (CAL1--CAL3, outcome, subgroup audit) | **PASS** |
| V3 | `sp4-finite-index-fd-projective-multiplier-is-finite` and its Lazard--Whitehead route | **PASS** |
| V4 | `isw-theorem-a-has-no-data-on-sp4-finite-index-subgroups` and its route | **PASS** |

**Bottom line on the printed questions.** Neither commit answers [FFW]
Question 1.6 or Question 1.9, in whole or in part.

- The artifact body is correct and careful. It proves only an implication:
  if `C*(Sp_4(Z))` has the LLP, then the LLP readings of both questions have
  positive answers.
- The commit subject drops the "if" and so overstates the result.
- Commit messages are immutable here (no amend), so this review is the
  correction of record.
- `sp2g-z-full-c-star-algebra-has-llp` stays OPEN. Both questions remain open
  as far as this review can tell (section 4).

## 1. The printed questions, verbatim

[FFW] p. 6, under "Open questions":

> In another direction, the following seems to be a particularly challenging
> group for which the (L)LP is open.
>
> Question 1.6. Does F2 × F2 have the (L)LP?
>
> The group F2 × F2 is known not to have (R)FD thanks to the negative solution
> of the Connes embedding problem [54]: see [155].

[FFW] p. 6:

> Question 1.9. Is there an example of an infinite property (T) group (or just
> a group with property (T) relative to an infinite subgroup) with the (L)LP?

Further [FFW] passages that the artifact quotes; all match verbatim:

- p. 18 (Remark 3.22): "It seems to be open whether the (L)LP is preserved
  under direct products. For example, it is open whether F2 × F2 has the
  (L)LP (Question 1.6); this problem is generally considered difficult, see
  for example the discussion at the end of [155, Section 3]."
  - [155] is N. Ozawa, *About the QWEP conjecture*, Internat. J. Math. 15
    (2004).
- p. 15 (Remark 3.8): "We do not know an example of a group with the LLP that
  has property (T), or even property (T) with respect to an infinite subgroup
  (Question 1.9)."
- p. 17: "Corollary 3.17. The LP and LLP both pass to subgroups."

[FFW] also mentions Question 1.6 on p. 22 (Remark 3.32: dropping amenability
from their amalgam theorem would cover `F2 × F2`) and on p. 40 (RAAGs).
Neither passage changes the status.

## 2. Does the landed argument answer either question as printed?

No.

- **The calibration (CAL1--CAL3) is a correct implication.**
  - Block-diagonal `SL_2(Z) x SL_2(Z) <= Sp_4(Z)` holds for the symplectic
    basis `e1, f1, e2, f2`.
  - The Sanov subgroup is free of rank two and has finite index in `SL_2(Z)`.
  - LLP passes to subgroups: [ISW] Remark 1.2, p. 4, verbatim "if C*(Γ) has
    the LP (respectively, the LLP), then so does C*(Σ)"; and [FFW]
    Corollary 3.17, p. 17.
  - So `C*(Sp_4(Z))` LLP ⟹ `C*(F2 x F2)` LLP.
- **For Question 1.9,** `Sp_4(Z)` is an infinite property (T) group. [ISW]
  Example 1.3(i), p. 4, lists `Sp_2n(R)`, `n >= 2`, and its lattices
  `Sp_2n(Z)`. So LLP for `Sp_4(Z)` would be an infinite (T) group with the
  LLP.
- **Exact scope of what a positive answer on the hole would give.**
  - Question 1.6 would get only its LLP half. The LP for `F2 x F2` would stay
    open.
  - Question 1.9 would get only its LLP reading. `Sp_4(Z)` cannot answer the
    LP reading at all: [ISW] Example 1.3(i) with Corollary E (p. 4) shows that
    `C*(Sp_2n(Z))`, `n >= 2`, fails the LP.
- **Status of the hypothesis.** The hypothesis "`C*(Sp_4(Z))` has the LLP" is
  the OPEN target `sp2g-z-full-c-star-algebra-has-llp`. No part of either
  question is settled.
- **What the artifact actually says.** It reads "A positive answer for
  `Sp_4(Z)` would answer three questions at once", and item 1 reads
  "`C*(F_2 x F_2)` is NOT known to fail LLP." That wording is correct. Only
  the commit subject is wrong.

## 3. Import checks

### 3a. `79981c886` (artifact section 0)

- **[ISW] Corollary B, p. 2:** the quote matches verbatim, including the ring
  generalization.
- **Ring generalization, "Positive characteristic rings give infinite torsion
  abelian subgroups": PASS.**
  - A commutative unital ring has characteristic 0 (it contains `Z`, so the
    group contains `Z^2 ⋊ SL_2(Z)` and `SL_3(Z)`) or characteristic `n > 0`.
  - In the second case `R^2` and the root subgroups of `SL_n(R)` are torsion
    abelian and infinite, since `{2x}` is infinite.
  - Torsion subgroups of `GL_4(Z)` are finite. That is classical and was not
    source-read.
- **The "Moreover" clause of Corollary B was not audited in the artifact.
  Checked here: PASS.**
  - [ISW] section 3.2 (PDF p. 12) builds `A = ⊕_{∆/Σ} Z^2` by co-induction so
    that `A ⋊ ∆` "contains `Z^2 ⋊ Σ` as a subgroup", with `Σ = F_2`, and
    deduces LLP failure through Remark 1.2.
  - Any such group inside `Sp_4(Z)` would therefore contain `Z^2 ⋊ F_2`,
    which `sp4-contains-no-isw-affine-subgroup` excludes.
  - So the artifact's conclusion "no subgroup of `Sp_4(Z)` is currently known
    to fail LLP" is not contradicted by this clause.
- **[ISW] Corollaries D and E (p. 4) and Theorem G (p. 5)** conclude only
  "does not have the LP". Verified verbatim.
- **[FFW] Remark 3.8, p. 15:** the quote is verbatim. The artifact honestly
  flags the Guentner--Higson--Weinberger exactness input as not source-read.
  - The same remark continues: "[57, Theorem 1.6] says in particular that if
    there exists a property (T) group Γ with the LLP such that
    H1(Γ) = 0 ≠ H2(Γ), then there exists a non-hyperlinear group", where [57]
    is A. Dogon, Math. Z. 305 (2023).
  - This is a published cousin of the artifact's third consequence. This
    review does not claim it applies to `Sp_4(Z)`.

### 3b. `42efd7440` (fence)

- **[ISW] Theorem A, p. 2:** hypotheses (1)--(3) match `(NA1')` verbatim.
  - (1): `c_n|Λ` is not a coboundary.
  - (2): `c_n(g,h) → 1` pointwise.
  - (3): a projective representation on a finite-dimensional `H_n` with
    cocycle `c_n`.
  - The remaining hypothesis, relative property (T) of `(Γ', Λ)`, is
    automatic for a finite-index `Γ'` of the Kazhdan group `Sp_4(Z)`.
- **Finite-index return of the LLP.**
  - [FFW] Theorem 3.39 (p. 26) is stated for `1 → K → Γ → Λ → 1` with `Λ`
    amenable. That covers normal finite-index `K`; the non-normal case follows
    through the normal core and subgroup permanence.
  - [ISW] Remark 1.2 (p. 4) states the finite-index case directly: "then so
    does C*(Γ)". PASS.
- **[BMS] p. 129 (PDF p. 72): verbatim match.**
  - "Clearly Γ^ is just the profinite completion of Γ".
  - Kneser's Strong Approximation Theorem: `k` a number field, `G` simply
    connected and almost simple, not of type `E_8`, `G_{k_p}` non-compact for
    some `p ∈ S` ⟹ `G_k` dense in `G(A^S)`.
  - "Theorem 14.1. — The congruence subgroup conjecture is true for
    G = SL_n (n ≥ 3) and for G = Sp_2n (n ≥ 2)."
- **[Laz] V (2.4.9), p. 178 (PDF p. 175): verbatim match.**
  - `G` a complete `p`-valued group of finite rank.
  - `L = Q_p ⊗ Lie Sat Al G`.
  - `M` a `Q_p`-vector space with a complete topological
    `Sat Al G`-module structure.
  - Then `H*_c(G,M)` identifies canonically with `H*(L,M)`.
  - Trivial `M = Q_p` qualifies, since the augmentation extends.
- **[Laz] V (2.4.10)(iii), p. 179:** invariants version. Matches.
- **[Laz] V (2.2.2.2)--(2.2.3.2), pp. 165--166:** quasi-minimal complex, ranks
  `C(r,n)`, and `H^n_c(G,M) = H^n(Hom_A(X_., M))`. Matches.
- **Mathematics re-derived: correct.**
  - *Step 0.*
    - The `SU(d)` renormalization changes `c` by a coboundary and forces
      `c' ∈ μ_d`.
    - `E ≤ ∆ x SU(d)` is residually finite (Malcev on the finitely generated
      linear factor).
    - `N ∩ μ_d = 1` gives `E ≅ ∆ ×_Q E/N`.
    - Injectivity for finite `∆^ab`: `f^k` is a character of finite order,
      and the twisted-product homomorphism kills `inf b` over a finite
      quotient. This tacitly uses normalized cocycles, which is harmless.
  - *Step 2:* the Hochschild--Serre bound from the three `E_2` terms.
  - *Step 3:* the level-one input `sp4-fd-projective-multiplier-is-finite`
    computes ✓ on `research/FRONTIER.md`.
  - *Step 4.*
    - For `v >= 2`, `ω(g) = v_p(g-1) >= 2 > 1/(p-1)` for every prime.
    - The three valuation estimates are right.
    - `H^2_c(K,Q_p) = H^2(sp_4,Q_p) = 0` (Whitehead) ⟹ `H^2(K,Q_p/Z_p)`
      injects into the torsion of the finitely generated `Z_p`-module
      `H^3_c(K,Z_p)`, which is finite.
  - *Closedness route:* `B^2 = δ(T^{Γ'})` is compact in the product topology,
    so `c·B^2` is closed, a constant class limiting to `1` is trivial, and
    restriction to `Λ` contradicts (1).
- **Script `sp4-chevalley-eilenberg-betti-2026-09-12.py`.**
  - The 10-element basis satisfies `X^T J + J X = 0`, as the script asserts.
  - The coboundary formula is the standard Chevalley--Eilenberg one.
  - Betti numbers are exact ranks over `Q`.
  - It is a calibration only; the load-bearing fact is Whitehead's second
    lemma.

## 4. Novelty scan: have the questions been answered since?

Nothing found that answers Question 1.6 or Question 1.9. The scan ran on
2026-09-13.

- **[FFW] itself.** The arXiv listing shows v1 (19 Mar 2026) and v2
  (17 Apr 2026, comment "added appendix about property MD"). There is no v3.
  v2 still lists both questions as open (section 1).
- **D. Enders, T. Shulman, arXiv:2403.12224 (v3, 21 May 2026).**
  - Abstract: "C*(F_n×F_n) is inductive limit of RFD C*-algebras with the
    LP".
  - Also: "for a class of C∗-algebras including C*(F_n×F_n) ... the LLP is
    equivalent to Ext being a group".
  - This is a reformulation of the LLP half of Question 1.6, not an answer.
    Its v1/v2 date from 2024, before [FFW].
- **M. Gould, arXiv:2607.20407 (22 Jul 2026).**
  - Abstract: `C*(G)` fails the LP whenever `G` contains an uncountable
    abelian subgroup, so the LP and the LLP differ for full discrete group
    C*-algebras.
  - It does not mention `F_2 x F_2` or property (T).
- **G. Pisier, arXiv:2507.06177 and arXiv:2507.06105 (2025).** General LP
  and LLP complements; no claim about `F_2 x F_2` or property (T) groups.
- **Web searches found no preprint giving an infinite property (T) group
  with the LLP,** or deciding the LLP for `C*(F_2 x F_2)` or `C*(Sp_4(Z))`:
  - "local lifting property" with "F_2 x F_2";
  - "property (T)" with LLP;
  - `Sp_4(Z)` with LLP;
  - Fournier-Facio--Willett questions.

- **The arXiv API from MSI was unusable.** The compute node has no outbound
  network, and the login node was rate-limited (HTTP 429). So the scan used
  web search and arXiv abstract pages.

The scan is not exhaustive. Read "open" as "open as of this scan".

## 5. Node displays, recomputed

`cairn why` run on MSI against origin/main tip
`5a716fd85` (fresh `git archive`, pinned-artifact errors in unrelated nodes
filtered):

```text
sp4-finite-index-fd-projective-multiplier-is-finite [ESTABLISHED via sp4-finite-index-multiplier-lazard-whitehead-proof]
  sp4-fd-projective-multiplier-is-finite ✓ via sp4-fd-projective-multiplier-finiteness-proof (direct proof)
isw-theorem-a-has-no-data-on-sp4-finite-index-subgroups [ESTABLISHED via isw-theorem-a-no-data-sp4-finite-index-proof]
sp2g-z-full-c-star-algebra-has-llp [OPEN]
  frontier hole: no live routes into it
  live routes waiting on it: non-hyperlinear-from-e3-fibre-llp, non-hyperlinear-from-sp2g-llp,
                             nonhyperlinear-from-sp4-llp-maslov-dichotomy
```

The displays agree with the verdicts above. No `invalidates:` is recommended
for either commit. The only correction is the wording of the `79981c886`
subject, and this review records it.
