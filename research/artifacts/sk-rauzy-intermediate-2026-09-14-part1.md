# sk-rauzy-intermediate part 1: the semi-free clause, the golden-mean host, and where a points-based engine dies (2026-09-14)

Lane sk-rauzy-intermediate. Plan: `research/artifacts/sk-rauzy-intermediate-plan-2026-09-14.md`.
- **Result.** One established claim, unreviewed: the semi-free clause of Cornulier's Question 7 is negative in the dyadic class.
- **Correction.** The plan's guessed host for the golden-mean fragmentation is wrong; the source's host is given below.
- **Attempt.** One recorded attempt.
- **Still OPEN.** Question 7 for Sturmian subshifts, and the torsion-free clause everywhere.

## 1. Corollary SF: no uniform semi-free diameter in the dyadic class
Cornulier, Séminaire Bourbaki 1064 (arXiv:2002.09342), question 7, source l.216 (copy on MSI at `sk/sk-free-8/corn/bou1064.tex`), verbatim:
> A-t-il un diamètre semi-libre (resp. sans torsion) uniforme (c'est-à-dire, existe-t-il un entier $N$ tel que pour tout système générateur, la $N$-boule contient un couple d'éléments engendrant librement un semi-groupe libre (resp. contient un élément sans torsion)?

**Corollary SF.** Let (X,T) be an infinite minimal subshift satisfying (H1) and (H2) at infinitely many scales (`dyadic-tower-subshift-full-group-non-uniform-growth`, PASS-WITH-FIXES sk-verify-19). An example is every primitive constant-length-2 substitution subshift with a non-periodic fixed point. Then for every N ≥ 1 some finite generating set of [[T]]′ has no free-semigroup pair in its N-ball.

*Proof.*
- For a finite generating set S of G, put ω_S = lim_ℓ γ_S(ℓ)^{1/ℓ}.
- Suppose a and b lie in the N-ball of S and freely generate a free semigroup. The 2^k positive words of length k in a, b are pairwise distinct and have S-length ≤ Nk, so γ_S(Nk) ≥ 2^k and ω_S ≥ 2^{1/N}.
- By the theorem, ω(G) = inf_S ω_S = 1. So for each N there is an S with ω_S < 2^{1/N}, and its N-ball contains no such pair. ∎

**Remarks.**
- Nothing about full groups is used. For any finitely generated group, a uniform semi-free diameter implies uniform exponential growth, so every negative growth answer is a negative semi-free answer.
- This corrects the "still open" remarks on the semi-free clause (sk-verify-17 l.106; the open node's Progress) for the dyadic class.
- **The torsion-free clause is not answered.** A negative answer needs, for each N, a generating set whose N-ball consists of torsion elements.
  - The generating sets T_n of the dyadic proof fail: they contain the shift pair σ_n, of infinite order.
  - Replacing σ_n by partial S-translation involutions still leaves infinite-order products at radius 2, namely two involutions generating D_∞.
  - Not attempted further.

Nodes: `dyadic-derived-full-groups-no-uniform-semifree-diameter` and its route `-proof`.

## 2. The golden-mean fragmentation and its host (read at source)
Source: V. Nekrashevych, "Palindromic subshifts and simple periodic groups of intermediate growth", arXiv:1601.01033, TeX on MSI `sk/rauzy/nek/burnside.tex`.
- **Definition of fragmentation (l.552).** A finite group A of homeomorphisms is a fragmentation of the involution a if:
  - h(ζ) ∈ {ζ, a(ζ)} for all h ∈ A;
  - every ζ has some h ∈ A with h(ζ) = a(ζ).

  The sets E_{h,a} = {h = a} and E_{h,1} = {h = id} are closed and a-invariant, and meet in Fix(a). l.128: "we do not require the sets where the action of an element h∈A coincides with the action of a to be open". The pieces 𝒫 are open with closures meeting in Fix(a).
- **Golden-mean example (§7, l.1346–1440).**
  - a(x) = φ−x and b(x) = 1−x on R/Z; ba is the rotation by φ.
  - Cantor model {1,2}^ω with a(1w)=1b(w), a(2w)=2b(w), b(11w)=2w, b(2w)=11w, b(12w)=12b(w).
  - Generators a_i, b_i, c_i, d_i (i = 0,1,2). The pieces are P_i = ∪_k W_{3k+i}, where W_n consists of the sequences starting with (12)^n2 or (12)^n11.
  - Theorem `th:F`: "The group F coincides with its topological full group full(F, X^ω). It is periodic and of intermediate growth. Its derived subgroup [F,F] is simple and has finite index in F."
- **Inverted orbits and growth.** Prop `pr:uppernu` (l.1030ff): for a linearly repetitive fragmentation with a purely non-Hausdorff singularity, the inverted orbits of every point satisfy ν(n) ≤ C_1 n e^{−C_2√log n}. Thm `th:growth` (l.1265): growth ≤ exp(C_1 n e^{−C_2√log n}).
- **Host (Prop `prop:embeddingfull`, l.885, repeating Matte Bon arXiv:1408.0762).**
  - Let w_ζ ∈ (𝒫_A ⊔ 𝒫_B)^Z be the edge-label sequence of the orbital chain of a regular point ζ, and 𝒲 its orbit closure. The shift σ on 𝒲 is minimal (source, via `prop:regularcontainment`).
  - s ∈ A∪B acts by s(w) = σ(w) if π_{w(0)}(s) = 1, by σ^{−1}(w) if π_{w(−1)}(s) = 1, and by w otherwise.
  - This embeds G = ⟨A∪B⟩ in full(⟨σ⟩, 𝒲).

**Consequences recorded (elementary, no node).**
- F ≤ [[σ_𝒲]], so [F,F] ≤ [[σ_𝒲]]′. Thus [[σ_𝒲]]′ contains a finitely generated simple periodic group of intermediate growth.
- ζ′ ↦ w_{ζ′} is equivariant and injective on the orbit of a regular ζ (w_ζ is not periodic, since F is infinite). So `pr:uppernu` bounds inverted orbits at the points w_ζ.
- In the chain the labels alternate between 𝒫_A and 𝒫_B, so V = {w : w(0) ∈ 𝒫_A} is a constant tower of height 2: σV = 𝒲∖V and σ²V = V. So (H1) holds at m = 1.
- **Not computed:** towers of height 4 or more, and so whether Theorem Q′ already applies to 𝒲.

**Correction to the plan (§3, "Instance").**
- The plan guessed the host to be a "dihedral double" 𝒳×{0,1} with σ(ζ,0) = (aζ,1), σ(ζ,1) = (bζ,0), lifting g ∈ F by the parity of its local germ.
- That lift is NOT continuous. At a purely non-Hausdorff singularity ξ, an element h ∈ A acts as a on pieces accumulating at ξ and as id on others (Definition `def:singularities`, l.260–266). So the parity is discontinuous at ξ.
- Matte Bon's 𝒲 splits these points. The plan hedged ("plausibly", "identify at source"); this settles it.

## 3. Attempt: a points-based engine on 𝒲 (sketch; dies at transport)
Let H = [F,F] ≤ [[σ_𝒲]]′ play the role of the Grigorchuk level group of the dyadic proof. The local generators live on 8 floors over a small cylinder E_0 near a point ρ = w_ζ.

**What transfers (sketch).**
- **(E1).** A word of length ≤ R in bounded-cocycle generators acts as one power of σ on every cylinder of radius ≫ R. If it fixes ρ, it is the identity on the cylinder around ρ, by aperiodicity. So conjugates of local generators are indexed by inverted-orbit points, and conjugates at the same point agree.
- **(E2).** With ν(ℓ) ≤ Cℓe^{−C√log ℓ} and growth exp(o(ℓ)), the factors of sk-cornulier-q7 part 2 §5 are all exp(o(ℓ)): P_2 ≤ 20160^ν, P_3 ≤ ν!, P_4 ≤ (3^K(2ℓ+1))^ν.
- **Not checked:**
  - separation, the analog of SS3: supports of conjugates at distinct inverted-orbit points must be disjoint, which forces E_0 to shrink with the scale;
  - Step 2 on the first return map to E_0.

**Where it dies: coherent transport.**
- Dyadic Step 3 moves the support σ^{−1}W ∪ W ∪ σW of a good 3-cycle into the fibre by a uniform level permutation. That permutation acts by the same power of σ on all three pieces.
- An h ∈ H with h(W) ⊂ E_0 may act by different powers on σ^{±1}W, because it reads different pieces at neighbouring vertices. So hσ_Wh^{−1} is a 3-cycle on three pieces at uncontrolled bounded orbit distances, not a local generator.
- Rigid-stabilizer transport, gΛ′_Eg^{−1} = Λ′_{gE}, needs the whole support inside one translate g(E). That forces floor sizes comparable to the displacement of g, which is unbounded.
- Coherent transport is what a uniform level model gives, and Lemma K (sk-sturmian-growth part 2) forbids those with N > 1 on Sturmian X_α.

**Sharpened target.** Generation of [[σ]]′ from boundedly many local elements plus conjugation by an intermediate-growth H, WITHOUT coherent transport. For example, supports adapted to single fragment pieces, in the style of the proof that Alt(G,X) is finitely generated (Nekrashevych, `th:fullgrnek`).

## 4. The Sturmian gap, precisely
- Matte Bon's host for a fragmentation of a Sturmian-based dihedral action is its edge-label subshift 𝒲, not X_α itself. So th:F-type groups are not a priori inside [[T_α]]′.
- **Needed.**
  - A finitely generated H ≤ [[T_α]]′ with exp(o(ℓ)) growth and inverted orbits ν(ℓ)·log ℓ = o(ℓ) at two points of one H-orbit;
  - plus the transport of §3.
- [[T_α]] acts on a Cantor model of the circle by piecewise rotations (IET-like). The status of intermediate-growth subgroups of IET groups was not checked at source: the Dahmani–Fujiwara–Guirardel arXiv id tried (1107.3053) is a different paper.

## 5. Checked vs. not
- **Read at source (MSI):**
  - arXiv:1601.01033 l.51–182, 242–266, 390–430, 552–600, 880–945, 1030–1040, 1265, 1346–1440;
  - bou1064.tex l.212–217;
  - arXiv:1408.0762 abstract and theorem list.
- **Not read:** the proof of `th:F`; `prop:regularcontainment`; Matui's abelianization theorem.
- **Novelty:** bounded to greps of main (only "still open" mentions of the semi-free clause). Corollary SF is elementary; its value is closing a clause recorded as open.
