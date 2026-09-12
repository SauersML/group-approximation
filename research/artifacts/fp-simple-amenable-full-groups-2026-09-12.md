# Finitely presented simple amenable groups inside topological full groups

Lane `fp-simple-amenable-group`, 2026-09-12. Nodes:
`fp-infinite-simple-amenable-group` (open root),
`amenable-full-group-forces-invariant-measure`,
`fp-subshift-full-group-subgroups-extend-to-sft`,
`periodic-approximable-subshifts-host-no-fp-simple-group`.

Nothing here settles the root. Two general obstructions are proved, the
repository's finitely presented simple hosts are ruled out, and the class that
survives is stated precisely.

## 1. Status of the question

All sources below were read from arXiv TeX sources on MSI
(`/scratch.global/sauer354/fpsa/src/`).

- Juschenko--Monod, arXiv:1204.2132 (Ann. of Math. 178, 2013), abstract: "We
  provide the first examples of finitely generated simple groups that are
  amenable (and infinite)." The groups are `D([[phi]])` for minimal subshifts
  `phi`.
- Kourovka Notebook (arXiv:1401.0300 source, 21st edition), Problem 15.5
  (P. de la Harpe, "Well-known problem"): "Does there exist an infinite finitely
  generated group which is simple and amenable?" It is recorded as answered by
  Juschenko--Monod. We grepped every "amenab" line with a six-line window for
  "presented" or "presentation". No finitely presented version of the question
  turned up; the matches were 20.62 (Dixmier), archive 8.7 (Olshanskii--Sapir),
  14.34 and 16.52.
- Matui, arXiv:math/0404117, Theorem 5.7 and the corollary after it: for a
  minimal subshift, `D([[phi]]_0)`, `[[phi]]_0` and `[[phi]]` are never finitely
  presented. The proof puts `X` inside an ambient SFT, where the finitely many
  relators hold on an SFT neighbourhood, and then uses flip-conjugacy rigidity.
- Grigorchuk--Medynets, arXiv:1105.0719, Section 1: `[[T]]` is LEF, and for every
  minimal subshift `D([[T]])` is infinitely presented. The argument: finitely
  presented infinite simple groups are isolated among marked groups, so they
  are not limits of finite groups.
- Matui, arXiv:1210.5800, abstract: for one-sided irreducible SFT groupoids,
  `[[G]]` has type F_infinity. This gives "a new infinite family of finitely
  presented infinite simple groups". These groups are not amenable (Section 2
  below).
- Xin Ma, arXiv:2209.00580, Theorem C: `[[alpha]]` is LEF for every minimal,
  topologically free, residually finite action on the Cantor set.
- Szoke, arXiv:1808.09882, abstract: topological full groups of minimal actions
  of virtually cyclic groups are amenable. Every finitely generated group that
  is not virtually cyclic has a minimal free Cantor action whose full group
  contains `F_2`.
- Nekrashevych, arXiv:1601.01033, source line 138: the fragmentation groups
  `<A u B>` of minimal dihedral actions embed in the topological full group of a
  minimal subshift. These include his simple periodic groups of intermediate
  growth.

**Assessment.** We found no written source that states the finitely presented
version as a question or answers it. Our web-search budget was exhausted before
we could search further, so the attribution is still open: who asked this, and
where, is not recorded. The finitely generated version is Kourovka 15.5. Every
finitely presented infinite simple group recorded in this graph or in the sources
above is non-amenable. The Thompson, Higman--Thompson, Brin--Thompson and
Röver--Nekrashevych groups, the SFT full groups and the Leavitt unit groups
contain `V`. Torsion-free lattice examples such as the Burger--Mozes groups,
which cannot contain `V` because `V` has torsion, contain `F_2`. The root is
therefore recorded as OPEN, on this limited check.

## 2. Theorem 1: an amenable full group forces an invariant measure

**Setting.**
- `G` is an effective, Hausdorff, ample groupoid with compact unit space `X`,
  and every orbit has at least three points.
- `Gamma <= Homeo(X)` realizes moving bisections by 3-cycles, meaning: for every
  compact open bisection `U` and every `x` in `s(U)` with `U(x) != x`, there is a
  clopen `E` with `x in E ⊆ s(U)`, and some `gamma` in `Gamma` with
  `gamma|_E = U|_E`.

**Lemma 1.1.** `D([[G]])` realizes moving bisections, and so does every group
containing it.

*Proof.*
1. Let `y = U(x) != x`. Pick `z` in the orbit with `z` different from `x` and
   `y`, and a compact open bisection `V` with `V(y) = z`.
2. Choose a clopen `E` containing `x` so small that `E`, `U(E)` and `VU(E)` are
   pairwise disjoint.
3. Let `a` be the involution swapping `E` and `U(E)` through `U`. Let `b` be the
   involution swapping `E` and `VU(E)` through `VU`. Both lie in `[[G]]`.
4. For involutions `[a,b] = abab`, and applying it right to left sends
   `E -> U(E) -> VU(E) -> E`, with `[a,b]|_E = U|_E`. Check at `x in E`:
   `b(x) = VU(x)`, `a` fixes it, `b` returns it to `x`, and `a(x) = U(x)`.
5. So `[a,b]` lies in `D([[G]])`. ∎

**Theorem 1.** If `Gamma` realizes moving bisections and is amenable, then `X`
carries a `G`-invariant Borel probability measure: `mu(U(E)) = mu(E)` for every
compact open bisection `U` and every Borel `E ⊆ s(U)`.

*Proof.*
1. An amenable group acting continuously on a compact space fixes a point of the
   weak-* compact convex set of probability measures. This gives a
   `Gamma`-invariant `mu`.
2. **Moving points.** Suppose `x in s(U)` and `U(x) != x`. On the clopen `E_x`
   given by realization, `mu(U(E)) = mu(gamma E) = mu(E)` for Borel
   `E ⊆ E_x`.
3. **Fixed points.** Suppose `U(x) = x`.
   - Choose `z != x` in the orbit and a compact open bisection `W` with
     `W(x) = z`. Put `U' = U W^{-1}`.
   - `W` moves `x`, and `U'` moves `z`, since `U'(z) = x`.
   - Take a clopen `E_x` containing `x` inside the realization neighbourhood of
     `W`, with `W(E_x)` inside the realization neighbourhood of `U'`.
   - Then `mu(U(E)) = mu(U'(W(E))) = mu(W(E)) = mu(E)` for Borel `E ⊆ E_x`.
4. **Globalize.** `s(U)` is compact, so a finite clopen partition `{E_k}` refines
   the cover `{E_x}`. Because `U` is injective on `s(U)`,
   `mu(U(E)) = Σ_k mu(U(E ∩ E_k)) = Σ_k mu(E ∩ E_k) = mu(E)`. ∎

**Corollary 1.2 (compressible hosts are dead).** Let `G` be minimal. Suppose some
nonempty clopen `A` contains disjoint clopens `B` and `C`, with compact open
bisections from `A` onto `B` and from `A` onto `C`. Then no group realizing
moving bisections is amenable; in particular `[[G]]` and `D([[G]])` are not.

*Proof.*
1. Take `mu` from Theorem 1. Let `O` be the largest open `mu`-null set.
2. For every compact open bisection `U`, `U(O ∩ s(U))` is open and null, so it
   lies in `O`. Hence `O` is invariant.
3. By minimality `X \ O = X`, so `mu` has full support and `mu(A) > 0`.
4. But `mu(A) >= mu(B) + mu(C) = 2 mu(A)`, a contradiction. ∎

**Example 1.3.** Let `A` be an irreducible 0-1 matrix that is not a permutation
matrix, and `G_A` the one-sided SFT groupoid on `X_A`.
- For each vertex `a`, `[a]` is the disjoint union of the `[ab]` with
  `A(a,b) = 1`, and the shift is a compact open bisection from `[ab]` onto
  `[b]`.
- An invariant `mu` would therefore give a nonnegative, nonzero vector `v`,
  `v_a = mu[a]`, with `Av = v`.
- By Perron--Frobenius this forces `rho(A) = 1`. An irreducible 0-1 matrix with
  `rho(A) = 1` has all row sums 1 (if they were unequal, `rho` would lie strictly
  between the least and greatest row sums), so it is a permutation matrix.
- Hence Matui's finitely presented simple groups `D([[G_A]])` are not amenable.

## 3. Theorem 2: finitely presented subgroups extend to an SFT neighbourhood

**Conventions.**
- `Lambda` is a finitely generated group and `A` a finite alphabet.
- `Lambda` acts on `A^Lambda` by `(lambda . x)(mu) = x(mu lambda)`.
- A local rule is a finite set `D ⊆ Lambda` and a map `c: A^D -> Lambda`, acting
  by `T_c(x) = c(x|_D) . x`.
- A composite of local rules is again a local rule. We call its rule the
  *formal cocycle* of the word; it depends on `x` only on a finite window.
- `[[Lambda ~ X]]` is the group of homeomorphisms `g` of `X` with a continuous
  cocycle `c_g` such that `g(x) = c_g(x) . x`.
- On a free subshift the cocycle is unique and locally constant, so every `g`
  in `[[Lambda ~ X]]` is `T_c|_X` for some local rule.

**Theorem 2.** Let `X ⊆ A^Lambda` be a subshift on which `Lambda` acts freely.
Let `Gamma = <g_1, ..., g_k> <= [[Lambda ~ X]]` be finitely presented. Then:
- there is a subshift of finite type `Y` with `X ⊆ Y ⊆ A^Lambda`;
- there are `hat g_i` in `[[Lambda ~ Y]]` with `hat g_i|_X = g_i`;
- restriction to `X` is an isomorphism `<hat g_1, ..., hat g_k> -> Gamma`.

*Proof.*
1. **Rules.** Choose local rules `c_i` for `g_i` and `c_i'` for `g_i^{-1}`.
2. **Invertibility.**
   - Let `C_1` be the clopen condition that the formal cocycles of the words
     `s_i^{-1} s_i` and `s_i s_i^{-1}` are `e` at `x`, for all `i`.
   - `Y_2 = {x : lambda . x in C_1 for all lambda}` is an SFT.
   - It contains `X`, because on `X` these words act trivially and the action is
     free.
   - On the `Lambda`-invariant set `Y_2`, `T_{c_i}` and `T_{c_i'}` are mutually
     inverse orbit-preserving maps. So `hat g_i = T_{c_i}|_{Y_2}` is a
     homeomorphism in `[[Lambda ~ Y_2]]`.
3. **Relators.**
   - Fix a finite presentation `<s_1, ..., s_k | r_1, ..., r_m>`, with
     `s_i -> g_i`. One exists on this generating set, since finite presentation
     does not depend on the finite generating set.
   - Let `C_2` be the clopen condition that the formal cocycle of every `r_j` at
     `x` is `e`.
   - `Y = {x in Y_2 : lambda . x in C_2 for all lambda}` is an SFT containing `X`.
   - It is invariant under the `hat g_i`, and each `r_j(hat g)` acts on `Y` as
     `x -> e . x = x`.
4. **Isomorphism.**
   - So `s_i -> hat g_i|_Y` defines a surjection `pi: Gamma -> Delta_Y`.
   - Restriction to the invariant set `X` is a homomorphism
     `rho: Delta_Y -> Gamma` with `rho pi = id`.
   - Therefore `pi` is injective, hence bijective, and `rho = pi^{-1}`. ∎

**Corollary 2.1.** In Theorem 2, suppose `Gamma` is infinite and simple, and let
`Z ⊆ Y` be a nonempty closed invariant set.
- `<hat g_i|_Z>` is either trivial or isomorphic to `Gamma` through the
  generators.
- In particular every `hat g_i` fixes every finite `Lambda`-orbit in `Y`
  pointwise.

*Proof.* The kernel of `Gamma -> Homeo(Z)` is normal, so it is trivial or all of
`Gamma`. A finite image is impossible for an infinite group unless the map is
trivial. ∎

**Definition (PA).** A subshift `X` has *periodic approximations* if the
following holds for every `x` in `X`, all finite `W, K ⊆ Lambda`, and every
finite `B ⊆ Lambda \ {e}`. There is a `y` in `A^Lambda` such that:
- the orbit of `y` is finite;
- `y|_W = x|_W`;
- `Stab(y) ∩ B` is empty;
- every pattern `(lambda . y)|_K` occurs in `X`.

**Corollary 2.2.** If `X` is a free subshift with (PA), then no finitely
generated subgroup of `[[Lambda ~ X]]` is a finitely presented infinite simple
group.

*Proof.*
1. Take `Y` from Theorem 2. It is defined by allowed patterns on a finite shape
   `K`, and they include all `K`-patterns of `X`.
2. Some `g_i` moves some `x`, with cocycle `n = c_i(x|_D) != e`.
3. (PA) with `W ⊇ D` and `B = {n}` gives a finite-orbit `y` in `Y` with
   `hat g_i(y) = n . y != y`.
4. This contradicts Corollary 2.1. ∎

**Lemma 2.3.** Every infinite minimal subshift `X ⊆ A^Z` has (PA).

*Proof.*
1. **Window.** Take `x` in `X`, `K ⊆ [-M, M]`, `W`, and `B`, and let
   `b = max |B|`. The point `x` is not periodic, so there is `N >= M` with
   `W ⊆ [-N, N]` such that `x|_{[-N,N]}` is not `d`-periodic for any
   `1 <= d <= b`. (Otherwise one `d <= b` would work for infinitely many `N`,
   making `x` periodic.)
2. **Recurrence.** By uniform recurrence the word `v = x|_{[-N, N+2M]}` recurs at
   some shift `q > 2N+2M+1`.
3. **Periodic point.** Let `y` be `q`-periodic with
   `y|_{[-N,-N+q)} = x|_{[-N,-N+q)}`. For `t` in `[-N+q, N+2M+q]` we have
   `y(t) = x(t-q) = x(t)`. So `y = x` on `[-N, N+2M+q]`.
4. **Allowed patterns.** Every length-`(2M+1)` window of `y` is a translate of
   one inside that interval, so it occurs in `x`.
5. **Stabilizer.** The least period `d` of `y` exceeds `b`, since `y|_{[-N,N]}`
   is not `d`-periodic for `d <= b`. So `Stab(y) ∩ B` is empty. ∎

**Consequences.**
- No finitely generated subgroup of the full group of an infinite minimal
  `Z`-subshift is a finitely presented infinite simple group. This recovers
  Matui's Theorem 5.7 and the Grigorchuk--Medynets corollary. No novelty is
  claimed.
- The same applies to every finitely generated subgroup of such a full group,
  including Nekrashevych's simple periodic groups (arXiv:1601.01033, line 138).
- By Xin Ma's Theorem C, LEF full groups of residually finite actions give the
  same conclusion there.

## 4. What survives

A finitely presented infinite simple amenable subgroup of a topological full
group must avoid all of the following:
1. **Compressible groupoids** (Corollary 1.2). This rules out every
   Thompson-like host and the SFT full groups.
2. **Free subshifts with periodic approximations** (Corollary 2.2). This covers
   every infinite minimal `Z`-subshift, hence the Juschenko--Monod and
   Nekrashevych families.
3. **Residually finite minimal actions** (Xin Ma, Theorem C).

What remains:
- **(S1)** Free subshifts over amenable, not virtually cyclic `Lambda`, such as
  `Z^d` with `d >= 2`, inside SFTs whose finite orbits near `X` are fixed by the
  generators. The model case is a minimal aperiodic `Z^2` SFT. Whether one
  exists, and whether its full group is amenable, was not checked. Elek--Monod
  give a minimal `Z^2`-subshift with a non-amenable full group; Xin Ma's distal
  theorem gives amenable ones, but those are equicontinuous or residually
  finite, so item 3 applies to them.
- **(S2)** Non-subshift groupoids, where the coding factor of a finitely
  generated subgroup is not free. Theorem 2 needs freeness, because relator
  triviality then becomes a clopen condition. The recurrent groupoids of
  Juschenko--Nekrashevych--de la Salle (bounded automaton groups) live here.
  Their full groups are amenable when the groupoid is recurrent, but no
  finitely presented simple subgroup is known.

**Strengthening left open.** It is plausible that when `Gamma = Alt(Lambda ~ X)`,
Theorem 2 forces `X` itself to be an SFT. The argument would recode `X` so that
colours are locally injective, then use universal commutator identities for
cylinder 3-cycles, e.g. `[(1 2 3), (3 4 5)] = (1 4 3)`, to produce a 3-cycle
trivial on `X` but not on `Y`. The disjointness bookkeeping for general `Lambda`
was not carried out, so this is not claimed.

## 5. Not verified

- Existence of minimal aperiodic `Z^2` SFTs.
- Elek--Monod's statement, which was not re-read here.
- Nekrashevych's embedding proof. Only the statement at line 138 was read.
- Szoke's results beyond the abstract.
- Whether the finitely presented question is stated explicitly somewhere in the
  literature.
