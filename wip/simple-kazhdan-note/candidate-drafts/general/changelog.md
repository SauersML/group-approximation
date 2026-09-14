# sk-draft-general: changelog against main (revision 1, 5b1890ce6c, 292 lines, md5 8e04b341…)

Draft: `sk/drafts/sk-draft-general/sk-draft-general.tex`, assembled from `partA.tex` + `partB.tex`. It is about 505 lines and 6 pages, 2 more than rev1's 4. MSI pdflatex, 3 passes: 0 errors, 0 overfull boxes, 0 undefined references. There are 2 underfull boxes, both in the bibliography.

Architecture (ROSTER-D): the headline is stated over finitely generated groups for free minimal subshifts with finite models. Z is the main example and needs no hypothesis, and the RF embedding follows at once.

## Front matter
- **Title:** "An infinite simple Kazhdan sofic group" → "Infinite simple Kazhdan groups that are sofic".
- **Macros and environments:** added `\Sym`, `\diag`, and the `proposition` and `question` environments.
- **Abstract:**
  - New lead: for a free minimal Γ-subshift with finite models, EL_n (n ≥ 3) is infinite, f.g., simple, (T) and LEF.
  - Such subshifts exist exactly over residually finite groups, and over Z every infinite minimal subshift qualifies.
  - The Brown/Ozawa/Pestov sentence is verbatim from rev1.
  - New sentence: every f.g. RF group is a subgroup of one of these groups.
  - The Turing-degree sentence is kept.

## Introduction
- Lineage paragraph: verbatim.
- New definitions: a subshift over Γ with `(γx)(h)=x(hγ)`, `L_F(X)`, and "finite models".
- **Theorem 1** is now over Γ, for every n ≥ 3. It replaces rev1's Z theorem and its "same holds for EL_n" sentence.
- **Proposition 2** is new:
  - (a) infinite minimal Z-subshifts are free and have finite models;
  - (b) a free action with finite models forces Γ to be RF;
  - (c) every infinite f.g. RF group has such a subshift.
- New sentence defining `G_X = EL_3(LC(X,F_2)⋊Z)`; it answers the question.
- **Corollary 3** is new: every f.g. RF group is a subgroup of an infinite f.g. simple Kazhdan LEF group.
- Credit paragraph:
  - EJZ, Grigorchuk–Medynets (for Z), Matui and Thom are as in rev1.
  - NEW: a Kerr–Nowak sentence ("studied residually finite actions and their crossed products"), which makes no claim that the definitions are equivalent.
  - NEW: Kionke–Schesler as the version without (T).
- The not-f.p. sentence moves to §5.

## §1 Proof of Theorem 1
- **The ring and property (T):**
  - word length, balls B_w, `u_γ`, and `e_a = e_{x(e)=a}`;
  - generators `e_ij(u_t)`, `e_ij(e_a)`;
  - the proof is written for general n, so rev1's "we write the proof for n=3" remark is gone;
  - the Z conventions appear as the special case u = u_1.
- **Finite models:**
  - the compactness fact F_γ (from freeness);
  - general finite-subshift models φ_Y;
  - nonvanishing through distinct points γy, γ ∈ E;
  - the entrywise LEF map with explicit invertibility.
  - The periodic-word paragraph for Z moves to the proof of Proposition 2(a).
- **Operator algebras** (main decision 17, sk-operator-algebras Option B):
  - L(G) ⊂ 𝓡^ω [Ozawa, Prop. 7.1];
  - L(G)⊗̄𝓡 is McDuff, with G in its unitary group (Brown's formulation);
  - Kirchberg Thm 1.1 gives no factorization property;
  - C*(G) fails the LLP [Ozawa, p. 527];
  - 𝓡 is written `\mathcal R`, so it does not clash with the ring R.
- **Simplicity:** same proof as rev1, written over Γ:
  - small V: `V∩γV=∅` for 0<|γ|≤2w, and `f∘γ` constant for |γ|≤w;
  - `ε_ab = e_{aV}u_{ab^{-1}}`, a,b ∈ B_w, with d = n|B_w|;
  - product formula `f u_a e_V f' u_b ∈ {0, ε_{a,b^{-1}}}`;
  - the level ideal uses translates `u_a e_V u_a^{-1} = e_{aV}`.

## New §2 Subshifts with finite models (proof of Proposition 2)
- **(a)** rev1's periodic-word argument, plus "no periodic points ⇒ free".
- **(b)** sk-general-actions-a Proposition N.
- **(c)** sk-general-actions-a Proposition E, a nested-hole Toeplitz point in {0,1,2}^Γ:
  - finite models through the configurations y_b;
  - minimality through recurrence along cosets;
  - freeness at every point.
- Credit: Cortez–Petite, J. Lond. Math. Soc. (2) 78 (2008) 1–20, doi 10.1112/jlms/jdn002 (Crossref-checked).

## New §3 Residually finite subgroups (proof of Corollary 3)
- From sk-universal-embedding-a:
  - replace Γ by Γ×Z;
  - use Ore's theorem to get Γ ≤ [Δ,Δ] with Δ f.g. RF;
  - Proposition 2(c) and Theorem 1 give the envelope;
  - Whitehead in characteristic 2: `diag(aba^{-1}b^{-1},1) ∈ EL_2`, so `γ ↦ diag(u_γ,1,1)`.
  - It never uses the false map diag(a,a^{-1},1).
- Bibitems (Crossref-checked):
  - Ore, Proc. AMS 2 (1951) 307–314;
  - Kionke–Schesler, J. Comb. Algebra (2024), doi 10.4171/JCA/103 (the volume number was not in the Crossref output, so it is omitted).

## §4 Word problems
- Verbatim from rev1, except the set S → Q, to avoid a clash with the generating set S.

## New §5 Questions (main decision 18, adapted)
- The not-f.p. sentence (moved), with the reason made explicit: infinite simple groups are not RF.
- Q1: an f.p. infinite simple (T) sofic or hyperlinear group; Alekseev–Thom Open problem 6.1.
- Q2: is every f.g. LEF group a subgroup of an infinite simple Kazhdan LEF group? This replaces decision 18's absence of an embedding question; it is the natural question in this architecture.
- Q3: rigidity, "flip conjugate or at least strongly orbit equivalent [GPS]", with the easy direction stated.
- Q2 on Z² SFTs is dropped, per decision 18.
- Bibitems: AlekseevThom (arXiv HTML, as verified by sk-open-5) and GPS (Crossref).

## Origin and authorship
- Verbatim from main rev1 ("Codex (OpenAI) shortened an earlier version, and Claude revised this one").

## Not applied
- **Expanders / marked limits** (decision 6): the referee PASS is still pending.
- **Every F_q:** decisions 7 and 23; the binary unit trick in the simplicity text is F_2-only.
- **Fibonacci example** (decision 16).
- **Rigidity theorems** (decisions 21 and 25).
