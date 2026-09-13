# EX review, second wave, quantum and L²: part 3. Baum–Connes, Kadison–Kaplansky and fixed-price imports read at source; a notation fix in the BGW erratum import

Lane `ex-verify2-quantum-l2`, 2026-09-13. Index: `ex-review2-quantum-l2-2026-09-13.md`.

**Method.**
- **Texts.** Ghostscript `txtwrite` extracts on MSI, in `/scratch.global/sauer354/ex/ex-verify2-quantum-l2/pdf/`:
  - `CE-docmath6.txt`, from EMS Press;
  - `1804.02725v3.txt`, `2508.07938v8.txt` and `Cout.txt`, from arXiv or the author's page;
  - `trc.txt`, from `him-lueck.uni-bonn.de`.
- **Line numbers** refer to those files.

## 3.0 Verdicts

| claim | lane | source | verdict |
|---|---|---|---|
| `amenable-kernel-bc-transfer-and-ktop-half-exactness` | baum-connes | Chabert–Echterhoff, Doc. Math. 6 (2001): Thm 3.3 (l. 705), Cor. 3.4 (l. 713), Cor. 3.5 (l. 729), §4 (l. 1148–1174), Ex. 4.3 (l. 1215) | PASS at source; item 2 PASS as a derivation |
| `bgw-trivial-coefficient-agreement-is-open` (+ `-citation`) | baum-connes | Buss–Echterhoff–Willett arXiv:1804.02725v3: Prop. 2.6 (l. 449), Lemma 4.3 (l. 1107), Prop. 4.4 (l. 1143), Cors. 4.6–4.7 (l. 1195–1206), erratum (l. 1750–1836) | PASS at source after a notation FAIL (3.2), corrected forward in both nodes |
| `lueck-surjective-assembly-traces-lie-in-lambda-g` | kadison-kaplansky | Lück, Invent. Math. 149 (2002), Conj. 0.2 and Thm 0.3 (l. 68–86) | PASS at source; the spectral consequence PASS |
| `zariski-dense-psl-subgroups-are-completely-selfless` | kadison-kaplansky | Ozawa arXiv:2508.07938v8, Thm 14 (l. 780), Prop. 16 (l. 840) | PASS at source; the Zariski-density argument PASS |
| `gaboriau-commensurated-chain-fixed-price-criterion` | lueck | Gaboriau, Invent. Math. 139 (2000), Critères VI.24 (3) (l. 3343–3360) | PASS at source |

## 3.1 Chabert–Echterhoff

- **Theorem 3.3** is verbatim. For discrete `Γ/N`, the compact open subgroups are the finite `F`, and
  `q^-1(F)` is a finite extension of the amenable `N`.
- **Item 1 of the claim** is exactly Cor. 3.5, verbatim: "Suppose further that N satisfies the Haagerup
  property (e.g., if N is amenable). Then, if B is a G-algebra, G satisfies BCC (resp. BCI, resp. BCS)
  for B if and only if G/N satisfies BCC (resp. BCI, resp. BCS) for B ⋊r N." The partial assembly
  bijectivity is Thm 3.3, since preimages of finite subgroups are amenable and satisfy BCC.
- **Items 3–4** match the §4 text verbatim (l. 1148–1174): the Kasparov–Skandalis half-exactness of
  `K^top_*(G; ·)`, and "BCC can only hold for G if G is K-exact".
- **Item 2**, the split abelian case, is correct as a derivation. The Fourier transform gives
  `C*_r(N) ≅ C(N^)`. For `Γ = N ⋊ G` the twisted action is the ordinary one, and
  `C*_r(Γ) ≅ C(N^) ⋊_r G`. Example 4.3 (l. 1215) uses the same identification for `K^n ⋊ SL_n(K)`.

## 3.2 Buss–Echterhoff–Willett erratum: a notation FAIL, corrected forward

- **Erratum text located.**
  - l. 1750: Kubota "pointed these out".
  - l. 1770–1771: "The following lemma is due to Narutaka Ozawa and was communicated to us by Yosuke
    Kubota."
  - l. 1809: "4.4 is correct or not, but Lemma 4.3 is definitely false."
  - l. 1836: "4.4 together with Corollaries 4.5, 4.6, 4.7, and 4.8 are still open."
- **Main text.** Prop. 2.6, Lemma 4.3, Prop. 4.4 and Cors. 4.6–4.7 are where the citation route says.
- **The finding.**
  - Lemma A.1 reads "Suppose that ⋊_µ has the ideal property. Then every short exact sequence of
    G-algebras 0 → I → A → ℂ → 0 descends to a short exact sequence 0 → I ⋊_µ G → A ⋊_µ G → ℂ ⋊_µ G → 0."
  - The extraction prints `C`. The proof opens "Consider the generalized homomorphism ℂ → M(A),
    λ ↦ λ1_{M(A)}", so the quotient is the trivial algebra.
  - Both nodes printed `0 -> I -> A -> C -> 0` in plain text. Read with `C` an arbitrary `G`-algebra, that
    statement is false: the reduced crossed product has the ideal property, and it does not preserve
    short exact sequences over any non-exact group (Kirchberg–Wassermann; context).
- **No graph damage.**
  - The claim's next sentence ("a quotient onto trivial coefficients never witnesses non-exactness")
    shows the intended reading.
  - `k-inexact-module-triple-refutes-trivial-coefficient-bc` applies the lemma only in its trivial model
    (`W = V`, quotient `C*_r(G)`).
  - `split-quotients-give-exact-reduced-crossed-products` describes it as the lemma "for quotients onto
    the trivial algebra".
- **Correction.** Both nodes now print `ℂ` and name the proof's first line.
- **Not re-derived.** The printed proof of Lemma A.1 (multiplier splitting plus an approximate unit).
- **"Is open" claim.** The lane's bounded literature check (one web search, 2026-09-12) is recorded in
  the node. Nothing later was found here either; this review ran no search of its own.

## 3.3 Lück, trace conjecture

- **Conj. 0.2 and Thm 0.3** are verbatim (l. 68–86), including "In particular the modified Trace
  Conjecture 0.2 holds for G, if the assembly map asmb^G : K_0^G(E̲G) → K_0(C*_r(G)) appearing in the
  Baum-Connes Conjecture is surjective."
- **Spectral consequence.**
  - If `a = a^* in M_n(C[G])` and `c notin spec(a)`, then `chi_(-∞,c)` is continuous on `spec(a)`, so
    `chi_(-∞,c)(a)` is a projection of `M_n(C*_r G)` and its trace lies in `Λ^G`.
  - If `0` is isolated in `spec(A^*A)`, then `chi_{0}(A^*A)` is the kernel projection.
  - So under surjective assembly, a kernel dimension outside `Λ^G` forces `0` to accumulate in
    `spec(A^*A)`. Correct.

## 3.4 Ozawa, selflessness

- **Thm 14 and Prop. 16** match the quotes; the extraction garbles the ligatures ("sellfess",
  "satisifes").
- **The `SL_3(Z)` instance** is correct:
  - `PSL(3,R) = SL(3,R)`;
  - a finite-index `Γ` meets each `U_ij(Z)` in an infinite subgroup;
  - infinite subsets of a line are Zariski dense;
  - Zariski closures of subgroups are subgroups;
  - root groups generate `SL_3(R)`.
- **Not re-located.** The §6 sentence defining "completely C*-selfless" (the ligatures defeat grep).

## 3.5 Gaboriau, fixed price

Critères VI.24 (3), verbatim up to lost accents (l. 3352–3360): "Alex Furman m'a suggéré, avec la même
preuve, les énoncés plus généraux suivant : (3) si Γ est une réunion croissante de groupes infinis Γ_n où
Γ_1 est à prix fixe de coût 1, par exemple moyennable, et si Γ_{n+1} est engendré par Γ_n et des éléments
γ ∈ Γ tels que γ^{-1} Γ_n γ ∩ Γ_n soit infini alors Γ est à prix fixe de coût 1." The node's English
statement matches.
