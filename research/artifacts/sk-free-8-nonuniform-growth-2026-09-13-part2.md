# sk-free-8: Kazhdan groups of non-uniform exponential growth from self-similar rings (part 2: consequences)

Continues part 1, which contains Theorem B: small-ball generating sets T_n(Σ) of EL_{3·2^n}(A) with γ(ℓ) ≤ exp(Cℓ^β) for ℓ ≤ 2^{⌊n/2⌋}/3. Status: established by this lane, UNREVIEWED (queued with sk-verify-13).

## 4. Self-similar rings
**Lemma 4.** For a unital ring S and N ≥ 1, EL_3(M_N(S)) = EL_{3N}(S) inside GL_3(M_N(S)) = GL_{3N}(S).

*Proof.*
- **⊆.** A block elementary matrix e_{pq}(B), B ∈ M_N(S), is the product of the e_{ij}(B_{ab}) with i in block p and j in block q, a < N, b < N. These commute because p ≠ q.
- **⊇.** If i and j lie in different blocks, e_{ij}(r) = e_{pq}(rE_{ab}) is block elementary. If both lie in block p, choose a block q ≠ p and an index k in it. Then e_{ij}(r) = [e_{ik}(r), e_{kj}(1)], a commutator of block elementary matrices. ∎

**Theorem A.** Let R be a unital ring of characteristic 2, generated as a ring by a finite set Σ, with R ≅ M_2(R) as rings. Then ω(EL_3(R)) = 1. If moreover EL_3(R) is infinite, EL_3(R) is a Kazhdan group of non-uniform exponential growth.

*Proof.*
1. **Matrix sizes.** By induction, R ≅ M_{2^n}(R) (M_2(M_{2^{n−1}}(R)) ≅ M_{2^n}(R)). Applied entrywise, a ring isomorphism R → M_{2^n}(R) gives a group isomorphism EL_3(R) ≅ EL_3(M_{2^n}(R)), and Lemma 4 identifies the latter with EL_{3·2^n}(R) = EL_{Y_n}(R).
2. **Growth rate.** Let U_n ⊆ EL_3(R) be the preimage of T_n(Σ), a generating set (Lemma 1). By Theorem B and Lemma 0, ω(EL_3(R),U_n) ≤ exp(C(2^{⌊n/2⌋}/3)^{β−1}) → 1, so ω(EL_3(R)) = 1.
3. **Exponential growth.** If EL_3(R) is infinite, it has property (T) by Ershov–Jaikin-Zapirain (Invent. Math. 179 (2010), Theorem 1.1; R is finitely generated). An infinite Kazhdan group is non-amenable, and a group of subexponential growth is amenable (balls form a Følner sequence along a subsequence). So EL_3(R) has exponential growth, and ω = 1 gives non-uniform exponential growth. ∎

Here C and β come from Theorem B with |Σ| fixed, so they do not depend on n.

## 5. Consequences
**Lemma 5 (tower of height two).** Let X be a Cantor space with homeomorphism T, and R = LC(X,F_2) ⋊_T Z with (fu^i)(f′u^j) = f(f′∘T^{−i})u^{i+j}. Suppose V ⊆ X is clopen, X = V ⊔ TV, and (V, T²|_V) is topologically conjugate to (X,T). Then R ≅ M_2(R).

*Proof.*
1. **T² fixes V.** T²V = X∖TV = V, since TV ⊔ T²V = TX = X.
2. **Matrix units.** Put ε_00 = e_V, ε_11 = ue_Vu^{−1} = e_{TV}, ε_10 = ue_V and ε_01 = e_Vu^{−1}. Then ε_ab ε_cd = δ_bc ε_ad and ε_00+ε_11 = 1. So R ≅ M_2(e_V R e_V).
3. **The corner.** e_V(fu^k)e_V = f·1_{V∩T^kV}u^k, which vanishes for k odd (V∩TV = ∅) and equals f1_Vu^k for k even. So e_VRe_V is the crossed product LC(V,F_2) ⋊_{T²|_V} Z with unit u²e_V.
4. **Transfer.** A conjugacy φ: (X,T) → (V,T²|_V) induces the ring isomorphism R ≅ e_VRe_V, f ↦ f∘φ^{−1}, u ↦ u²e_V. ∎

**Corollary A1 (subshift groups).** Let X be the subshift of a primitive aperiodic substitution ζ of constant length 2, for example Thue–Morse (0↦01, 1↦10) or period doubling (0↦01, 1↦00). Then G_X = EL_3(LC(X,F_2) ⋊ Z) has non-uniform exponential growth. So G_X is an infinite, finitely generated, simple, Kazhdan, LEF group of non-uniform exponential growth.

*Proof.*
1. **Recognizability** (Mossé; see §7 for the locator): ζ: X → ζ(X) is injective and {ζ(X), Tζ(X)} is a clopen partition of X. Since ζ is continuous on a compact space, it is a homeomorphism onto ζ(X).
2. **Conjugacy.** For bi-infinite x, ζ(x) is the concatenation of the blocks ζ(x_k) placed at [2k,2k+1], so ζ∘T = T²∘ζ. Lemma 5 with V = ζ(X) gives R_X ≅ M_2(R_X).
3. **Generators.** R_X is generated as a ring by u^{±1} and e_{[a]} (a in the alphabet), since cylinder indicators are products of the u^je_{[a]}u^{−j}. Theorem A applies.
4. **Other properties.** G_X is infinite, simple, Kazhdan and LEF by the note (main 9047d0d3c9, Theorem 1). ∎

**Corollary A2 (odometer factor, zero entropy).** Let X be an infinite minimal subshift with topological entropy 0 that has the dyadic odometer Z_2 as a topological factor (for example a regular Toeplitz subshift with periods 2^n). Then G_X has non-uniform exponential growth.

*Proof.*
1. **Towers.** A factor map π: X → Z_2 gives clopen V_n = π^{−1}(2^nZ_2) with X = ⊔_{k<2^n} T^kV_n and T^{2^n}V_n = V_n. The matrix units ε_ab = u^a e_{V_n} u^{−b} (a,b < 2^n) give R_X ≅ M_{2^n}(R_n), where R_n = LC(V_n,F_2) ⋊_{T^{2^n}} Z. This is step 2 of Lemma 5 with 2^n levels.
2. **Recoding.** (V_n, T^{2^n}) is expansive (a restriction of a power of an expansive map), aperiodic (X is infinite and minimal), and has entropy 2^n·h(X) = 0. So it is conjugate to a subshift Z_n, and by Krieger's embedding theorem (ETDS 2 (1982) 195–202) Z_n embeds into {0,1}^Z. Hence R_n is generated as a ring by the three elements u_n^{±1} and e_{[1]}.
3. **Theorem A variant.** Run Theorem A with EL_3(R_X) ≅ EL_{3·2^n}(R_n) and Σ_n = {u_n, u_n^{−1}, e_{[1]}}, where |Σ_n| = 3 for every n. The constants of Theorem B depend only on |Σ|. ∎

**Corollary A3 (Leavitt algebras).** Let L be the Leavitt algebra L_{F_2}(1,2), generated by x_1,x_2,y_1,y_2 with y_ix_j = δ_ij and x_1y_1+x_2y_2 = 1. Then L_L ≅ L_L ⊕ L_L, so L ≅ End(L_L) ≅ End(L²_L) ≅ M_2(L). EL_3(L) is infinite (e_12(r) ≠ e_12(r′) for r ≠ r′), so EL_3(L) is a Kazhdan group of non-uniform exponential growth. The same holds for EL_n(L), n ≥ 3, with Y_n replaced by X_n × [n].

**Remark (the sheets).** Theorem B uses exactly three sheets: sheet 1 for type 3, sheets 2 and 3 for type 4, and type 2 on the whole fibre. For EL_n with n ≥ 3 use X_n × [n], with type 2 = Sym(n) on the fibre over η_n. Every step is unchanged, with 6 replaced by n!.

## 6. What is new, bounded
**Bounded search:**
- Kourovka Notebook 21st edition (arXiv:1401.0300, file of 1 Sep 2026): 21.117 and greps for Kazhdan and growth.
- Sauer–Schesler arXiv:2605.30163 (V) and arXiv:2606.15945 (Kazhdan, acylindrically hyperbolic), read at source.
- Cornulier, Séminaire Bourbaki 1064 (arXiv:2002.09342), questions (1)–(8).
- Three web searches ("simple group" non-uniform exponential growth; Kazhdan non-uniform growth; simple quotients of acylindrically hyperbolic groups).
- git grep of main: no node on uniform exponential growth.

**Known before this lane:**
- non-uniform exponential growth (Wilson 2004);
- simple and finitely presented examples (V, Sauer–Schesler 2026; Kourovka 21.117 answered);
- a Kazhdan example (Sauer–Schesler June 2026: acylindrically hyperbolic, hence not simple, answering de la Harpe 2002 §7).

**Not found in the search:**
- a SIMPLE Kazhdan group of non-uniform exponential growth;
- a LEF (or sofic) simple group of non-uniform exponential growth (V is not LEF, since f.p. + LEF ⇒ RF; Wilson's groups are not simple);
- non-uniform exponential growth for elementary groups over rings.

**UNCHECKED firewall.** If Sauer–Schesler's group Q has an infinite simple quotient, that quotient is a simple Kazhdan group of non-uniform exponential growth (quotients do not increase γ, and it is infinite Kazhdan). It would not be known LEF. So the defensible novelty is: explicit infinite simple Kazhdan LEF groups of non-uniform exponential growth, and the elementary-group engine. Do not write "first simple Kazhdan" until simple quotients of Q are checked.

**Credit.**
- The engine is Sauer–Schesler's argument (generating sets of four types, commuting supports, normal form, counting through Bartholdi–Erschler inverted orbits), transferred from Aut(F_{4·2^n}) to EL_{3·2^n}(A). Types 2 and 4 are replaced by Sym(3) and by the transvections with ring-generator coefficients.
- The inputs are Grigorchuk 1984, Bartholdi–Erschler 2012, Ershov–Jaikin-Zapirain 2010, Mossé 1996 and Krieger 1982.
- The question is Gromov 1981; Wilson 2004 gave the first examples.

## 7. Locators still to confirm
- **Mossé**, "Reconnaissabilité des substitutions et complexité des suites automatiques", Bull. Soc. Math. France 124 (1996), 329–346: bilateral recognizability for primitive aperiodic substitutions. Quote the partition statement at source; the secondary quote is in Donoso–Durand–Maass–Petite, ETDS 36 (2016). For Thue–Morse and period doubling, a direct proof via the odometer factor is also routine.
- **Bartholdi–Erschler 2012:** "Growth of permutational extensions", Invent. Math. 189 (2012); Prop. 4.4 and Lemma 4.9, as cited by Sauer–Schesler. Not opened by this lane.
- **Krieger 1982:** the statement is recalled through secondary sources. Aperiodicity makes the periodic-point condition vacuous.

## 8. Next targets (open, recorded as Attempts)
1. Every infinite minimal subshift X (Sturmian X has no constant towers): is G_X of non-uniform exponential growth?
2. **Cornulier's question (7)** (Bourbaki 1064, verbatim): "Le groupe $[[\varphi]]'$ a-t-il une croissance exponentielle uniforme ? A-t-il un diamètre semi-libre (resp. sans torsion) uniforme (c'est-à-dire, existe-t-il un entier $N$ tel que pour tout système générateur, la $N$-boule contient un couple d'éléments engendrant librement un semi-groupe libre (resp. contient un élément sans torsion) ?"
   - The engine needs a fibre generator with an abelian fibre group whose conjugates generate together with level permutations.
   - T_{V_n} alone gives a uniform, elementary-amenable-like subgroup. So a finite-order fibre-dependent generator is needed, and its commutation with the type-4 conjugates must be checked.
