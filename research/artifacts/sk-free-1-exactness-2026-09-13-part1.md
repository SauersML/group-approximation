# sk-free-1: exactness of infinite simple Kazhdan LEF groups, part 1 (2026-09-13)

Lane sk-free-1, a free lane in wave 10. Plan: `research/artifacts/sk-free-1-plan-2026-09-13.md`.

## 1. Theorem E1 (established, unreviewed)
**There exist infinite finitely generated simple Kazhdan LEF groups that are not exact.** Such a group G has no property A, and C*_r(G) is not an exact C*-algebra. G is LEF, so it is hyperlinear, and L(G) embeds in R^ω.

### Proof
1. **Osajda's input.** Let Γ be a finitely generated residually finite non-exact group (Osajda, §3 below).
2. **Γ is LEF.** Take the finite quotients Γ → Γ/N with N ∩ B_r = {1} and N of finite index (residual finiteness applied to the finitely many nontrivial elements of B_r B_r^{-1}). They are injective on B_r and multiplicative, so they are partial models.
3. **Γ lies in a host.** By `lef-groups-embed-in-simple-kazhdan-lef-groups` (reviewed PASS), Γ ≤ G with G = EL_3(LC(2^Δ,F_2) ⋊ (Z/2≀Δ)) infinite, finitely generated, simple, Kazhdan and LEF.
4. **The inclusion is a coarse equivalence onto its image.** Fix finite generating sets S_Γ ⊆ Γ and S_G ⊆ G. The identity (Γ,d_Γ) → (Γ,d_G|_Γ):
   - is uniformly expansive, since d_G(γ,γ′) ≤ C·d_Γ(γ,γ′) with C = max_{s∈S_Γ} |s|_{S_G};
   - is effectively proper: for every R the set {γ : |γ|_{S_G} ≤ R} is finite, so d_Γ is bounded on it.

   So (Γ,d_Γ) is coarsely equivalent to the subspace Γ ⊆ (G,d_G).
5. **Property A.** It is a coarse invariant and passes to subspaces (Willett, §3). If G had property A, so would Γ; it does not, so G has no property A.
6. **Exactness.** For countable discrete groups, property A is equivalent to exactness of the reduced C*-algebra (Guentner–Kaminker, Ozawa; quoted in §3). So G is not exact and C*_r(G) is not exact.
7. **Hyperlinearity.** G is LEF, hence sofic and hyperlinear, so L(G) ⊆ R^ω. ∎

**Variant (routine).** The same argument applies to every countable family of f.g. LEF groups through `countable-lef-groups-embed-in-simple-kazhdan-lef-groups`. The host can contain Osajda's group together with any other countable LEF group.

## 2. What E1 is and is not (bounded novelty check)
- **Without (T):** simple LEF non-exact groups already follow from Kionke–Schesler plus Osajda. Kionke–Schesler (arXiv:2304.09307, abstract l.128, verbatim): "every finitely generated residually finite (amenable) group embeds into a finitely generated (amenable) $\LEF$ simple group."

  E1 adds property (T).
- **Search bounds.**
  - Main was grepped for `exact|osajda|property-a` in ids and bodies: no node on non-exact simple Kazhdan groups.
  - Sources read: the Osajda 2018 intro, Osajda 2014 (arXiv:1406.5015) intro, Willett's notes, and the Kionke–Schesler abstract.
  - Gromov monsters with (T) are not checked. They are not known to be sofic, so E1's LEF clause is not implied by them.
- **Not claimed.**
  - Baum–Connes with coefficients: Osajda's residually finite groups contain D-regular graphs of growing girth (1703.03791 l.424–425), not expanders. The Baum–Connes counterexamples of arXiv:1406.5015 l.221 are the non-RF monster groups. No BC statement is made here.
  - Failure of coarse embeddability into Hilbert space: large-girth graphs without property A can embed coarsely.

## 3. Sources, verbatim (fetched on MSI 2026-09-13)
- **D. Osajda, *Residually finite non-exact groups*,** Geom. Funct. Anal. 28 (2018), no. 2, 509–517, doi 10.1007/s00039-018-0432-4 (Crossref: container, volume, issue and pages confirmed). arXiv:1703.03791, `rfneg_arXiv.tex`:
  - l.119–120: "A finitely generated group is \emph{non-exact} if its reduced $C^{\ast}$--algebra is non-exact. Equivalently, it has no Guoliang Yu's property A (see e.g.\ \cite[Chapter 11.5]{Roe-book})."
  - l.125–127, Main Theorem: "There exist finitely generated residually finite non-exact groups defined by infinite graphical small cancellation presentations."
  - l.128: "This answers one of few questions from the Open Problems chapter of the Brown-Ozawa book \cite[Problem 10.4.6]{BrownOzawa-book}."
- **R. Willett, *Some notes on property A*,** arXiv:math/0612492, `main.tex`:
  - l.542: property A is "inherited by subspaces";
  - l.1228–1229: "inspection of the proof above reveals that a subspace of a property A space has property A".
- **D. Osajda, *Small cancellation labellings of some infinite graphs and applications*,** arXiv:1406.5015, l.166: "For countable discrete groups, Property A is equivalent to: the existence of a topological amenable action on a compact Hausdorff space \cite{HigRoe}, to the exactness of the reduced $C^{\ast}$--algebra \cites{GK,Oz}, to nuclearity of the uniform Roe algebra \cite{Roe}".

## 4. Proposal sketch for the note (formal proposal after a PASS)
A sentence after the LEF characterization, at most 2 text lines plus a 3-line bibitem:
> Exactness passes to subgroups, so applying Corollary~2 to the residually finite non-exact groups of Osajda~\cite{OsajdaRF} gives infinite simple Kazhdan LEF groups that are not exact.

- Trade-off: one new fact the reader must trust (Osajda's theorem). It shows the hosts of Corollary 2 are genuinely wilder on the C*-side than the lamplighter look suggests, while L(G) ⊂ R^ω.
- Open companion question (E2, §5): is G_X exact?

## 5. E2, open: is G_X = EL_3(LC(X,F_2)⋊Z) exact for every infinite minimal subshift X?
The Attempts are recorded in node `subshift-elementary-groups-are-exact`.
- A yes would separate the Z-family from the hosts of E1 on the C*-side, alongside the SL_3(Z) obstruction.
- A no would give a non-exact subgroup of GL_m(LC(X,F_2)⋊Z), a much stronger statement than E1.
