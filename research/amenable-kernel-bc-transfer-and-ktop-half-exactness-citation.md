---
rg: 2
id: amenable-kernel-bc-transfer-and-ktop-half-exactness-citation
kind: route
title: Chabert--Echterhoff, Permanence properties of the Baum--Connes conjecture, Doc. Math. 6 (2001), Theorem 3.3, Corollary 3.5 and Section 4
target: amenable-kernel-bc-transfer-and-ktop-half-exactness
requires: []
---

**Source.** J. Chabert, S. Echterhoff, *Permanence properties of the Baum-Connes conjecture*,
Documenta Math. 6 (2001) 127--183. Downloaded from EMS Press
(`ems.press/content/serial-article-files/25880`) on MSI and extracted with ghostscript
`txtwrite`. Quotes are verbatim apart from typesetting.

**Theorem 3.3.** "Let 1 → N → G → G/N → 1 be an extension of groups such that G/N has a
compact open subgroup. Let B be any G-algebra and assume that for every compact open subgroup
K̇ of G/N, the subgroup q^{-1}(K̇) of G satisfies BCC with coefficients in B. Then the partial
assembly map µ^{G,N}_{N,B} : K^top_*(G;B) → K^top_*(G/N; B ⋊_r N) is bijective."

**Corollary 3.5.** "Let 1 → N → G → G/N → 1 be an extension of groups such that G/N has a
compact open subgroup. Suppose further that N satisfies the Haagerup property (e.g., if N is
amenable). Then, if B is a G-algebra, G satisfies BCC (resp. BCI, resp. BCS) for B if and only
if G/N satisfies BCC (resp. BCI, resp. BCS) for B ⋊_r N."

For discrete `G/N` the trivial subgroup is compact open. The preimages of finite subgroups are
finite extensions of `N`, hence amenable.

**Section 4, half-exactness.** "By a result of Kasparov and Skandalis (see [17, Appendix]), it
is known that for any proper G-algebra D the functor A ↦ KK^G(D,A) is half exact. Replacing D
by C_0(X), for X a G-compact subspace of E(G), and taking the limit over X, implies that the
topological K-theory functor A ↦ K^top_*(G;A) is half exact, too. [...] every short exact
sequence 0 → I → A → A/I → 0 of G-algebras induces a natural six-term exact sequence"

**Section 4, K-exactness.** "If G satisfies BCC, then it follows from the half exactness of
K^top_*(G,·) and the naturality of the assembly map that the functor A ↦ K_*(A ⋊_r G) has to
be half exact, too. Thus we see that BCC can only hold for G if G is K-exact in the sense that
for every short exact sequence 0 → I → A → A/I → 0 of G-algebras, the natural sequence
K_*(I ⋊_r G) → K_*(A ⋊_r G) → K_*(A/I ⋊_r G) is exact in the middle term."

**Example 4.3, the split abelian form used in item 2.** "Since K^n is abelian, hence amenable,
it follows from Theorem 3.7 that G_n satisfies the Baum-Connes conjecture for C if and only
H_n satisfies BCC for C*_r(K^n) ≅ C_0(K^n). Moreover, the Gelfand transform carries the
decomposition action of H_n on C*_r(K^n) to the action of H_n on C_0(K^n) [...]"

That example uses Theorem 3.7, the almost-connected case. For discrete groups Theorem 3.3 and
Corollary 3.5 apply instead. The twisted system of a split extension is the ordinary action,
which is the standard identification the example relies on.

**Not re-read.** Proposition 3.2, the commutative diagram relating partial assembly to
assembly, which Corollary 3.4 cites.
