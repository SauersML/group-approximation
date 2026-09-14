# sk-rauzy-intermediate: plan (2026-09-14)

Lane sk-rauzy-intermediate. Target: Cornulier, Séminaire Bourbaki 1064, Question 7, beyond dyadic subshifts, i.e. whether [[φ]]′ has uniform exponential growth for Sturmian subshifts. Open node: `topological-full-group-derived-uniform-exponential-growth`.

## 0. Where things stand (read on main)
- **Dyadic case is negative.** Towers of constant height 2^m with bounded induced alphabets give ω([[T]]′) = 1:
  - `dyadic-substitution-derived-full-groups-non-uniform-growth` (PASS twice);
  - the abstract version, Theorem Q′ with hypotheses (H1) and (H2), `dyadic-tower-subshift-full-group-non-uniform-growth` (unreviewed);
  - the Sauer–Schesler import `sauer-schesler-grigorchuk-level-estimates` (PASS, sk-verify-18).
- **Obstruction (sk-sturmian-growth part 2).** A uniform level model with N levels forces [1_X] = N[1_V] in K^0. For Sturmian X_α, K^0 = Z + αZ with unit 1, so N = 1. The Grigorchuk-level engine cannot run on any non-dyadic subshift.

## 1. What the engine really needs (extracted from sk-cornulier-q7 parts 1–2)
Each scale n needs a finitely generated "moving" group H_n and local generators near two far-apart points. Three things must hold:
- **(E1) Uniform action on the local region.** Words of length ≤ r_n act on the fibre region of a point as ONE map, so conjugates of local generators are indexed by inverted-orbit points, and conjugates at the same point agree.
- **(E2) Counting.** Growth of H_n on balls of radius ≤ r_n is exp(o(ℓ)). The inverted orbits of the two special points have size ν(ℓ), with ν(ℓ)·log ℓ = o(ℓ).
  - Only γ(r)^{1/r} → 1 is needed, so power bounds exp(Cℓ^β) are NOT required.
  - Check: P_2 ≤ 20160^{ν}, P_3 ≤ ν!, P_4 ≤ (3^K(2ℓ+1))^{ν}, and each is exp(o(ℓ)) as soon as ν(ℓ) log ℓ = o(ℓ).
- **(E3) Generation.** Transport by H_n plus local 3-cycles over every clopen subset of the fibre base reaches every good 3-cycle σ_U (Cornulier Lemme `eng_cb`).

The dyadic proof gets (E1) from level permutations acting uniformly on a tower base. That is what forces K^0-divisibility (Lemma K).

## 2. The replacement: act on points, not on levels
- **(E1) without towers.** Let H ≤ [[σ]] act on a Cantor space with bounded-displacement generators. Take the fibre region E_n to be a cylinder of radius R_n ≫ r_n around the special point. Every word of length ≤ R_n then acts on E_n as a single power of σ, since elements of [[σ]] are locally constant powers.
  - An element fixing ρ acts as σ^0 = id near ρ (aperiodicity), so conjugates at the same inverted-orbit point agree.
  - Choosing R_n large keeps the finitely many relevant copies of E_n pairwise disjoint.
- **(E3) without Alt(levels).**
  - A local tower of 8 floors over a small clopen E_0 ⊂ E_n gives the sheets.
  - The first return map R to E_0 provides the shift pairs.
  - For a linearly recurrent subshift, R is a subshift with a bounded return-word partition, so Step 2 of the dyadic proof applies verbatim.
  - Transport: for a small good W, some h ∈ H with h(W) ⊂ σE_0 acts as one power on σ^{-1}W ∪ W ∪ σW, so hσ_W h^{-1} = σ_{hW} is local. This uses density of H-orbits.
- **(E2) from Nekrashevych.** V. Nekrashevych, "Palindromic subshifts and simple periodic groups of intermediate growth" (arXiv:1601.01033, read at source on MSI), Prop `pr:uppernu`: for a fragmentation G of a minimal dihedral action with a purely non-Hausdorff singularity and linearly repetitive orbital graphs,
  - ν_ζ(n) ≤ C_1 n e^{−C_2√log n} for ALL points ζ;
  - growth ≤ exp(C_1 n e^{−C_2√log n}) (Thm `th:growth`).

  Then ν(ℓ) log ℓ = o(ℓ) holds. Alt(G,X) is finitely generated, simple, periodic, of intermediate growth, and lies in a fragmentation to which the bounds apply (Thm `th:two`).

## 3. Target theorems
- **Theorem N (engine on points, target).** Let (Y,σ) be an infinite minimal linearly recurrent subshift, and H ≤ [[σ]]′ finitely generated with dense orbits, satisfying (E2) at two points of one H-orbit. Then ω([[σ]]′) = 1.
- **Instance.** Nekrashevych's golden-mean fragmentation G_F sits inside the topological full group of a minimal subshift, per Matte Bon's observation, quoted in arXiv:1601.01033 l.138. Identify that host (Y_F,σ_F) at source: plausibly the "dihedral double" of the Fibonacci subshift, with σ² ≅ T^{−1} on two copies.
  - If Alt(G_F) ≤ [[σ_F]]′, then ω([[σ_F]]′) = 1.
  - That is a NON-dyadic negative answer: Lemma K allows only N | 2 there.
- **Sturmian itself.** This needs an H ≤ [[T_α]]′ of intermediate growth with small inverted orbits. [[T_α]] is a group of piecewise rotations (IET-like). Whether IET-type groups contain intermediate-growth subgroups is, as recalled, an open question (Dahmani–Fujiwara–Guirardel line); check at source before claiming. Record as the precise remaining gap.

## 4. First steps
1. Read Nekrashevych §§2–3 and §7 at source: which host subshift, and does Alt(G_F) lie in its derived full group?
2. Write Theorem N with full generation and counting proofs (part 1), model-tested against the dyadic theorem (H = Grigorchuk truncations must be a special case) and the odometer (must fail: not a subshift).
3. Land the Theorem N claim, the instance claim, and review requests with the verifier.
