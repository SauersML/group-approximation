# EX review 2, dynamics: part 8. ex2-hecke-pair-negative: Harder, the Laurent chamber quotient, central covers

Lane `ex-verify2-dynamics`, wave 2. Tip `4200f08d51` (statuses) and `b6919a710` (blobs). Commits under review:
a563464d7e, 5c0cd66f51, 0055f9362f, ed3c8647c4. None of these nodes had a review.

| node | status at tip | verdict |
|---|---|---|
| `harder-function-field-s-arithmetic-cohomology-vanishing` (+ `-citation`) | established | PASS, verbatim against Invent. Math. 42 (1977), pp. 135–136 |
| `laurent-sl3-real-cohomology-from-chamber-quotient` (+ `-proof`) | established | PASS. Wording GAP in item 3 corrected (§8.2) |
| `laurent-sl3-central-covers-never-witness-instability` (+ `-proof`) | established | PASS. (FP) was framed as a hypothesis read only from an abstract; it is now wired to the established import `laurent-s-arithmetic-finiteness-lengths` (§8.3) |
| edits to `sl3-laurent-f2-is-flexibly-hs-stable`, `sl3-polynomial-covers-have-extra-finite-quotients`, `sl3-polynomial-finite-index-z-extension-center-survives` | all OPEN | attempt and scope text is consistent with the established nodes; nothing fires |

## 8.1 The Harder import: PASS

**Source.** `harder1977.pdf`, the Springer scan on MSI in the lane directory, extracted with `pdftotext` for pages 1–3.
Header: "Inventiones math. 42, 135 - 175 (1977)".

**Setting and Satz (pp. 135–136).** They match the route verbatim, up to OCR: "Sei K/F_q ein Funktionenkörper vom
Transzendenzgrad 1 ... Sei S eine nicht leere, endliche Menge von Stellen ... Sei G_0/F_q eine einfach
zusammenhängende, einfache Chevalley Gruppe ... Sei Γ eine Kongruenzuntergruppe der Gruppe G_0(O)". Then:
- "**Satz.** 1. Die rationalen Kohomologiegruppen H^ν(Γ, Q) verschwinden für ν ≠ 0, r|S|, wobei r = Rang G_0 und |S|
  die Anzahl der Elemente in S ist.
- 2. Ist d = r·|S| so ist die Dimension von H^d(Γ,Q) endlich und gleich der Multiplizität der speziellen Darstellung
  π_sp = ⊗_(v∈S) π_(v,sp) von ∏_(v∈S) G(K_v) im diskreten Spektrum von L²(∏_(v∈S) G(K_v)/Γ)."

**Context sentences, also verbatim.**
- Garland's vanishing theorem for cocompact `p`-adic lattices, and Casselman's removal of the residue-field restriction.
- "Diese S-arithmetischen Gruppen sind nicht kokompakt, sondern haben nur ein endliches Kovolumen".
- "Im Beweis werde ich sehr weitgehend der Argumentation von Borel in [3] folgen".

**Not re-read.** The route's p. 136 sentence on the product of buildings and on Casselman forcing `π_sp` was not
re-read here. It is context only.

**Model tests.**
- *`S = {∞}`, `G_0 = SL_3`.* Item 1 gives `H^1 = 0`, matching (T), and `b_2` finite, matching the table of
  `sl3-polynomial-congruence-subgroups-have-large-b2`. Item 2 there reads `b_2 = ` Steinberg multiplicity at `∞`.
- *Level `t`.* `b_2 = 0`, which agrees with the contractible quotient (cone over the spherical building).

## 8.2 `laurent-sl3-real-cohomology-from-chamber-quotient`: PASS, one wording correction

**Item 1.**
- *Density.* `f` is a unit of `F_q[[t]]`, so `f·F_q[t,1/t]` is dense in `F_q((t))`. The closure of `A(f)` contains every
  `e_ij(λ)`, and these generate `SL_3(F_q((t)))`.
- *One chamber.* Stabilizers in `G_0` are open, so each coset `g·Stab(σ)` meets `A(f)`. `A(f)`-orbits of cells are then
  `G_0`-orbits, which are types for this type-preserving, chamber-transitive action.
- *Stabilizers.* `O_S ∩ F_q[[t]] = F_q[t]` and `O_S/(f) = F_q[t]/(f)` (as `t` is invertible mod `f`), so
  `A(f) ∩ SL_3(F_q[[t]]) = Γ(f)`. Conjugation by `g_i ∈ GL_3(O_S)` preserves `A(f)`, so
  `A(f)_(v_i) = g_iΓ(f)g_i^(−1)`. The chamber group is `Γ(f)` triangular mod `t`, which contains `Γ(tf)`.

**Item 2.**
- *Setup.* Brown VII.7 needs no finiteness of stabilizers. Cells are fixed pointwise, so there is no orientation twist.
- *Rows.* Row 0 is the cochains of a 2-simplex (only `E_2^(0,0) = R`). Row 1 vanishes by (T) of the stabilizers
  (`elementary-groups-over-fg-rings-have-property-t`, established). Rows `q >= 3` vanish because the stabilizers are
  discrete in `SL_3(F_q((1/t)))` and act properly on the 2-dimensional building `X_∞`.
- *Degeneration.* Out of row 2, `d_2` lands in row 1 and `d_(>=3)` in columns `>= 3`. Nothing enters row 2. So
  `E_2 = E_∞`, and the six formulas follow by reading total degrees.
- *Injectivity.* `x ∈ ker d^0` with `x_0 = 0` gives `x_i|_e = 0` on `e = {v_0, v_i}`, hence `x_i = 0` by transfer.

**Item 3.**
- *Harder.* `A(f)` is a congruence subgroup of `SL_3(F_q[t,1/t])`, with `S = {0,∞}` and `r|S| = 4`. Harder gives
  `H^2 = H^3 = 0`, so the four-term sequence is exact, and its alternating dimension count is the `b_4` formula.
- *The `q = 2` values.* `t^2 + 1 = (t+1)^2` is the image of `t^2` under `t ↦ t+1`, so `b_2 = 927`. The irreducible
  quadratic has `1304`.
- **Wording GAP, corrected.** The last sentence said the Soulé-sector table "computes" every term of the `b_4` formula.
  That table lists principal levels only. The edge and chamber groups are parahoric-type levels between `Γ(tf)` and
  `Γ(f)`; the method extends to them with double-coset counts, but those numbers were not computed. The node now says so.

**Item 4 (under (S)).** Every cell stabilizer contains `Γ(t)` with finite index, and `b_2(Γ(t)) = 0`. So row 2 vanishes
and `H^*(A;R) = R`, independently of Harder. It is labelled as conditional on (S).

## 8.3 `laurent-sl3-central-covers-never-witness-instability`: PASS, with (FP) wired to its import

**Item 1.**
- *Vanishing.* Harder with transfer gives `H^(1,2,3)(Δ;Q) = 0`.
- *`H_2` is torsion.* `H^2(Δ;Q) = Hom(H_2(Δ;Z), Q)`, since `Ext(−,Q) = 0`. If this is `0`, every element of `H_2` is
  torsion: otherwise `H_2 ⊗ Q != 0` would carry a nonzero functional.
- *`H^2(Δ;Z)` is finite.* `H^2(Δ;Z) = Ext(H_1(Δ;Z), Z)` is finite, because `H_1` is finite by (T) of `EL_3(F_q[t,1/t])`
  (`function-field-hecke-pair-is-perfect-codense-kazhdan`, item 1, established).

**Item 2.**
- *Pushout.* `N_t` is characteristic in the central `N`. The pushout of `1 → N/N_t → Δ~/N_t → Δ → 1` along a nonzero
  `φ : N/N_t → Q` is central.
- *Splitting.* Its class lies in `H^2(Δ;Q) = 0`, so it splits as a direct product (the section's image is normal
  because `Q` is central).
- *Contradiction.* The composite `Δ~ → Q` is nonzero on `N`, which contradicts (T). So `N` is torsion.
- *Finiteness.* The kernel of a surjection from a finitely generated group onto a finitely presented group is finitely
  normally generated. Central means finitely generated, so `N` is finite.

**Item 3.**
- *Pulled-back models.* `||ρ(n) − 1||_2^2 = 2 − 2Re tr ρ(n)` gives `tr ρ_k(n) → 1`. With `E_k = |N|^(−1)Σ_n ρ_k(n)`,
  `tr E_k → 1`, which is condition (c) of the Kazhdan-cover criterion (PASS, part 1 §1.4).
- *Projective models.* `H_2` is torsion and finitely generated (f.p.), hence finite, so the finite-multiplier theorem
  applies (PASS, part 1 §1.3).
- *Dogon 1.3.* No input, as stated.

**(FP): correction forward.**
- *What was wrong.* The node read only the arXiv abstract of the Rank Theorem and called (FP) a "hypothesis". The title
  and item 3, however, assert the conclusions outright.
- *The existing import.* `laurent-s-arithmetic-finiteness-lengths` (established) already imports the theorem verbatim,
  with "SL_3(F_q[t,1/t]) ... type F_3, finitely presented".
- *Re-read here.* The Rank Theorem of arXiv:1102.0428v1 (Bux–Gramlich–Witzel; `pdftotext` lines 48–50): "Let G be a
  connected non-commutative absolutely almost simple K-isotropic K-group. Then the finiteness length φ(Γ) of the
  S-arithmetic group Γ = G(O_S) is d − 1 where d := Σ_(p∈S) dim(X_p) is the sum of the local ranks of G".
- *The fix.* The route now requires `laurent-s-arithmetic-finiteness-lengths`, and the claim's (FP) paragraph cites
  it. The statement stands as written, now with a proved input.

**Readings.**
- The congruence subgroup property sentence stays a labelled reading. BMS p. 60 says the results apply to function
  fields over finite fields; this was not re-derived for `F_q[t,1/t]`.
- The "non-central kernels generated by relative-(T) elements" bullet is labelled a sketch and is not part of the
  statement.

## 8.4 Firing

- `sl3-laurent-f2-is-flexibly-hs-stable` is OPEN.
- Its attempt bullets are consistent with §§8.2–8.3: no scalar-cocycle or central-cover witness exists, the host is
  finitely presented, and the remaining shape is a non-central Kazhdan cover.
- The two premises of the one-place instability routes stay OPEN. Their new scope bullets correctly say that the
  consequence stops at `SL_3(F_q[t])`: flexible stability does not ascend from infinite-index subgroups.
