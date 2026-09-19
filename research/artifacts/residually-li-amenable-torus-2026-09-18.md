# Torus surjunctivity through a division ring that dominates the augmentation

swarm-0917-w11-w11-gs-follow, 2026-09-18. Target node:
`residually-li-amenable-groups-are-torus-surjunctive`. Parent open node:
`injective-torus-automata-have-regular-degree` (C2).

## 0. Summary

Let `tau` be an injective torus automaton over a countable group `G`, with degree matrix
`D in M_d(Z[G])` (`tau^*(xi) = xi D` on `H^1 = Z[G]^d`), and let `H = <supp D>`.

- **Theorem 1 (criterion).** Suppose `Q[H]` embeds in a division ring `E` such that every
  square matrix `A` over `Q[H]` with `epsilon(A)` invertible over `Q` is invertible over `E`.
  Then `xi -> xi D` is injective on `Q[G]^d` (C2 for `tau`) and `tau` is onto.
- **Theorem 2 (hosts).** The hypothesis holds whenever `H` is residually-(locally indicable
  and amenable), by Jaikin-Zapirain's universality theorem (Selecta Math. 27 (2021), no. 74).
  So every countable group all of whose finitely generated subgroups are
  residually-(LI amenable) is torus-surjunctive at every `d`.
- **Proposition 3.** A free-by-(LI amenable) group is residually-(LI amenable). This covers every
  Baumslag–Solitar group `BS(m,n)`, `mn != 0`. In particular `BS(2,3)` is covered. It is finitely
  presented and non-Hopfian, so it is neither residually finite nor LEF. It was one of the two
  "first open instances" named by w10-gs-follow.
- **Where it stops (Section 5).**
  - For a general locally indicable `G`, the hypothesis of Theorem 1 is the statement that
    Cohn specialization runs from `D_{Q[G]}` to `epsilon`. Call this augmentation domination,
    **(AD)**.
  - The published literature proves (AD) only through universality, which is known for
    residually-(LI amenable) groups and a few other classes. It is not known for all locally
    indicable groups.
  - For Thompson's `F`, (AD) holds if `F` is amenable.
  - A group with torsion admits no such `E` at all.

## 1. Imports

**(I1) Constants.** `torus-automata-over-rf-or-domain-groups-are-surjunctive`, periodic-point
lemma: "For every finite-index normal `N <= G`, right multiplication by `p_N(D)` is invertible on
`Z[G/N]^d`. In particular `epsilon(D) in GL_d(Z)`." It is ESTABLISHED and holds for every group.
It is used only with `N = G`.

**(I2) Regular degree gives surjectivity.** `torus-automata-with-regular-degree-are-surjective`:
"If `xi -> xi D` is injective on `Q[G]^d`, then `tau` is surjective." ESTABLISHED, for every
countable `G`.

**(I3) Jaikin-Zapirain 2021.** A. Jaikin-Zapirain, *The universality of Hughes-free division
rings*, Selecta Math. (N.S.) 27 (2021), no. 4, Paper No. 74, DOI 10.1007/s00029-021-00691-w.
The abstract below was fetched from the Crossref record of that DOI on 2026-09-18. The TeX
formulas are rendered as plain text; otherwise it is verbatim:

> Let E*G be a crossed product of a division ring E and a locally indicable group G. Hughes
> showed that up to E*G-isomorphism, there exists at most one Hughes-free division E*G-ring.
> However, the existence of a Hughes-free division E*G-ring D_{E*G} for an arbitrary locally
> indicable group G is still an open question. Nevertheless, D_{E*G} exists, for example, if G
> is amenable or G is bi-orderable. In this paper we study, whether D_{E*G} is the universal
> division ring of fractions in some of these cases. In particular, we show that if G is a
> residually-(locally indicable and amenable) group, then there exists D_{E[G]} and it is
> universal. In Appendix we give a description of D_{E[G]} when G is a RFRS group.

We use it with `E = Q`. "Division ring of fractions" means that `Q[G] -> D_{Q[G]}` is injective
and epic, meaning its image generates `D_{Q[G]}` as a division ring. "Universal" is in Cohn's
sense (P. M. Cohn, *Skew Fields*, CUP 1995, Ch. 4; *Free Ideal Rings and Localization in
General Rings*, CUP 2006, Ch. 7). An epic `R`-field `U` is universal if for every epic `R`-field
`L` there is a specialization `U ~> L`. A specialization is a subring `R_0 ⊆ U` containing the
image of `R`, together with a homomorphism `alpha: R_0 -> L` compatible with the maps from `R`,
such that every element of `R_0 \ ker(alpha)` is invertible in `R_0`. The printed theorem
number inside JZ21 was not read. The abstract carries the whole statement we use.

*Equivalent rank form, recorded for the reader.* By Cohn's theorem on singular kernels (and
Malcolmson's rank-function version), universality says that
`rank_L phi(A) <= rank_U(A)` for every map `phi: R -> L` to a division ring and every matrix `A`
over `R`. Lemma 4 below derives the only consequence we need directly from the specialization
definition, so this equivalence is not used.

**(I4) Support subgroup.** Route `torus-degree-regular-on-prime-power-residual-support-proof`,
step 2 (Lemma 1 of that artifact): "`Q[G]^d` is the direct sum of the `r Q[H]^d` over a left
transversal `r`. Right multiplication by `D in M_d(Z[H])` preserves each summand. So
injectivity on `Q[H]^d` gives injectivity on `Q[G]^d`." This is elementary; Section 3 reproves
it in one line.

**(I5) Standard group theory,** each recalled with a proof sketch where it is used: the
Nielsen–Schreier theorem; Serre's theorem that a group acting freely without inversions on a
tree is free; Magnus' theorem that free groups of any rank satisfy `∩_n gamma_n(F) = 1`; the
Bass–Serre tree of an HNN extension.

## 2. Specializations invert matrices

**Lemma 4.** Let `R_0` be a ring and `alpha: R_0 -> L` a homomorphism to a division ring such
that every element of `R_0 \ ker(alpha)` is a unit of `R_0`. If `A in M_n(R_0)` and `alpha(A)`
is invertible in `M_n(L)`, then `A` is invertible in `M_n(R_0)`.

*Proof.* Induct on `n`. For `n = 1`, `alpha(a) != 0`, so `a` is a unit. For `n > 1`,
`alpha(A)` is invertible, so its first column is nonzero. Pick `i` with `alpha(A_{i1}) != 0`.
Then `u = A_{i1}` is a unit of `R_0`. Swap rows `1` and `i`, a permutation matrix that is
invertible over `R_0`. Subtract left multiples `A_{k1} u^{-1}` of row `1` from the rows
`k > 1`. The unitriangular matrix doing this is invertible over `R_0`. After these operations,
`P A = [[u, b], [0, S]]` with `P` invertible over `R_0` and `S in M_{n-1}(R_0)`. Apply
`alpha`: `alpha(P) alpha(A) = [[alpha(u), alpha(b)], [0, alpha(S)]]` is invertible over `L`.
A block upper-triangular matrix over a division ring is invertible only if its diagonal
blocks are, by comparing ranks. So `alpha(S)` is invertible over `L`. By induction `S` is
invertible over `R_0`. Then `[[u, b], [0, S]]` has the inverse
`[[u^{-1}, -u^{-1} b S^{-1}], [0, S^{-1}]]`, so `A` is invertible. QED

## 3. The criterion

**Theorem 1.** Let `G` be countable, `tau` an injective torus automaton over `G` with degree
`D in M_d(Z[G])`, and `H = <supp D>`. Suppose there are a division ring `E` and an injective
ring homomorphism `iota: Q[H] -> E` with the following property:

- **(AD_E)** every square matrix `A` over `Q[H]` whose augmentation `epsilon(A)` is invertible
  over `Q` has `iota(A)` invertible over `E`.

Then `xi -> xi D` is injective on `Q[G]^d`, and `tau` is surjective, hence a homeomorphism.

*Proof.*
- By (I1), `epsilon(D) in GL_d(Z)`, so `epsilon(D)` is invertible over `Q`.
- `D` has entries in `Z[H] ⊆ Q[H]`. So by (AD_E), `iota(D)` has an inverse `C in M_d(E)`.
- Let `x in Q[H]^d` with `x D = 0`. Then `iota(x) = iota(x) iota(D) C = iota(xD) C = 0`, and
  `x = 0` because `iota` is injective. So right multiplication by `D` is injective on
  `Q[H]^d`.
- Write `Q[G] = ⊕_r r Q[H]` over a set of representatives `r` of the left cosets `rH`. Then
  `Q[G]^d = ⊕_r r Q[H]^d` and `(r y) D = r (y D)`. So injectivity passes to `Q[G]^d`; this is
  (I4).
- By (I2), `tau` is surjective. A continuous bijection of a compact Hausdorff space is a
  homeomorphism. QED

Only the constants of `tau` enter, through `epsilon(D)`. The whole content is in the ring
hypothesis (AD_E), which concerns `Q[H]` alone and not dynamics.

## 4. Hosts: residually-(LI amenable) groups

Call `G` **RLA** if for every `g != 1` there is `N ⊴ G` with `g ∉ N` and `G/N` locally
indicable and amenable.

**Lemma 5.**
- (a) Subgroups of RLA groups are RLA.
- (b) RLA groups are locally indicable.
- (c) Extensions of locally indicable groups by locally indicable groups are locally
  indicable.
- (d) Torsion-free abelian groups are locally indicable. So poly-(torsion-free abelian)
  groups are locally indicable, and they are solvable, hence amenable.

*Proof.*
- (a) For `K <= G` and `g in K`, take `N ∩ K`. Then `K/(N ∩ K)` embeds in `G/N`, and
  subgroups of LI amenable groups are LI amenable.
- (b) Let `1 != K <= G` be finitely generated and pick `1 != g in K`. Take `N` as in the
  definition. The image of `K` in `G/N` is nontrivial and finitely generated, so it maps
  onto `Z`, and so does `K`.
- (c) Let `N ⊴ G` with `N` and `G/N` locally indicable, and `1 != K <= G` finitely
  generated. If `K ⊆ N`, then `K` maps onto `Z` because `N` is LI. Otherwise the image of
  `K` in `G/N` is nontrivial and finitely generated, so it maps onto `Z`.
- (d) A nontrivial finitely generated torsion-free abelian group is `Z^r` with `r >= 1`. The
  rest follows from (c) by induction on the length of the series. QED

**Theorem 2.** If `H` is RLA, then `E = D_{Q[H]}` with its canonical embedding satisfies
(AD_E). Hence every injective torus automaton over a countable `G` with `<supp D>` RLA is
surjective. In particular every countable group whose finitely generated subgroups are RLA
(for example, every countable RLA group) is torus-surjunctive at every `d`.

*Proof.*
- By (I3), with `E = Q`, `U = D_{Q[H]}` exists and is the universal division ring of
  fractions of `Q[H]`. The group `H` is locally indicable by Lemma 5(b), so (I3) applies.
- The augmentation `epsilon: Q[H] -> Q` is onto a field, so `Q` is an epic `Q[H]`-field.
  Universality gives a specialization `(R_0, alpha)` from `U` to it:
  - `R_0 ⊆ U` contains `Q[H]`;
  - `alpha: R_0 -> Q` restricts to `epsilon` on `Q[H]`;
  - every element of `R_0 \ ker(alpha)` is invertible in `R_0`.
- Let `A` be a square matrix over `Q[H]` with `epsilon(A)` invertible. Then
  `A in M_n(R_0)` and `alpha(A) = epsilon(A)`. By Lemma 4, `A` is invertible in
  `M_n(R_0) ⊆ M_n(U)`.
- `Q[H] -> U` is injective, being a division ring of fractions. Theorem 1 applies. For the
  last sentence, `<supp D>` is finitely generated. QED

**Proposition 3.** Let `1 -> K -> G -> Q -> 1` with `K` free, of any rank, and `Q` locally
indicable and amenable. Then `G` is RLA.

*Proof.*
- The derived subgroups `K^(i)` are characteristic in `K`, hence normal in `G`.
- For `g ∉ K`, take `N = K`.
- For `1 != g in K`: free groups of any rank satisfy `∩_m gamma_m(K) = 1` (Magnus). For
  infinite rank, retract onto the finitely generated free factor that contains `g`. Also
  `K^(i) ⊆ gamma_(2^i)(K)`. So `g ∉ K^(n)` for some `n`. Take `N = K^(n)`.
- The factors `K^(i)/K^(i+1)` are abelianizations of the free groups `K^(i)`
  (Nielsen–Schreier), hence free abelian. So `K/K^(n)` is poly-(free abelian): locally
  indicable and solvable by Lemma 5.
- `G/K^(n)` is an extension of `K/K^(n)` by `Q`. So it is locally indicable by Lemma 5(c).
  It is amenable as an extension of amenable groups. QED

**Corollary (Baumslag–Solitar groups).** For `m, n != 0`, `BS(m,n) = <a, t | t a^m t^-1 = a^n>`
is RLA. So injective torus automata over `BS(m,n)` are surjective at every `d`.

*Proof.*
- Let `rho: BS(m,n) -> Z[1/mn] ⋊ Z`, where the generator `t` of `Z` acts by multiplication by
  `n/m`, with `rho(a) = 1` and `rho(t) = t`. The relation holds: `t · m = (n/m) m = n`.
  Multiplication by `n/m` and by `m/n` preserves `Z[1/mn]`.
- The target is torsion-free abelian by `Z`, hence LI (Lemma 5) and solvable. Its subgroup
  `rho(BS(m,n))` is LI and amenable.
- `BS(m,n)` is an HNN extension of `<a> ≅ Z`. It acts without inversions on its Bass–Serre
  tree, and the vertex stabilizers are the conjugates of `<a>`.
- Let `K = ker rho`. Then `K ∩ g<a>g^-1 = g(K ∩ <a>)g^-1 = 1`, since `rho(a^k) = k != 0` for
  `k != 0`. So `K` acts freely on a tree and is free (Serre).
- Proposition 3 applies. QED

**What is new here.** `BS(2,3)` is finitely presented and non-Hopfian (Baumslag–Solitar 1962).
- It is not residually finite, since finitely generated residually finite groups are Hopfian
  (Malcev).
- So it is not LEF: finitely presented LEF groups are residually finite (proved in
  `research/artifacts/lef-torus-small-fibre-2026-09-18.md`, Section 4).
- It is not RPP, since RPP groups are residually finite.
- It contains `F_2`, so it is not amenable.
- So none of `torus-automata-over-rf-or-domain-groups-are-surjunctive` (at `d >= 2`),
  `torus-degree-regular-on-prime-power-residual-support`, `abelian-groups-are-torus-surjunctive`
  or `lef-groups-are-torus-surjunctive` covers it.
- w10-gs-follow named "`d = 2` over `BS(2,3)`" as the first open instance. It is now closed at
  every `d`.

Other RLA hosts include:
- every locally indicable amenable group, for example every poly-(torsion-free abelian) group,
  and every amenable left-orderable group by Witte Morris
  (`amenable-left-orderable-groups-are-locally-indicable`);
- every free-by-(LI amenable) group, such as free-by-cyclic groups and all `BS(m,n)`;
- every residually torsion-free nilpotent group, such as free groups, surface groups and RAAGs.

We did not decide whether some finitely generated LI amenable group fails to be LEF.

## 5. Where the method stops

**5.1 Torsion.** Suppose `H` contains a finite subgroup `1 != K`, and let `N_K = Σ_{k in K} k`.
Then `epsilon(N_K) = |K|` is invertible over `Q`, but `N_K (1 - k) = 0` for every `k in K`.
So no injective map of `Q[H]` into a division ring inverts `N_K`. Hypothesis (AD_E) therefore
forces `H` to be torsion-free with `Q[H]` a domain. Groups with torsion need the RPP or LEF
methods, or something new. This matches the Bezout witness in
`torus-degree-regular-on-prime-power-residual-support` (b).

**5.2 General locally indicable groups: the condition (AD).** For locally indicable `G`,
`D_{Q[G]}` exists in characteristic `0`. It is the division closure of `Q[G]` in `U(G)`
(Jaikin-Zapirain–López-Álvarez, Math. Ann. 2020, Cor. 6.7, as quoted in
Jaikin-Zapirain–Linton, arXiv:2303.05976v4, §2.3). Consider:

- **(AD)** every square matrix over `Q[G]` whose augmentation is invertible is invertible over
  `D_{Q[G]}`.

By Theorem 1, (AD) for every locally indicable group would give C2 and torus surjunctivity for
every locally indicable group at every `d`, with no approximation hypothesis at all.

(AD) is equivalent to `rk_epsilon(A) <= rk_{D_{Q[G]}}(A)` for all matrices. Given `A` with
`rk_epsilon(A) = r`, pick an `r x r` submatrix with invertible augmentation. (AD) makes it
invertible over `D`, so `rk_D(A) >= r`. The converse is clear.

This is item 1(ii) of `flat-weak-bass-holds-exactly-for-locally-indicable-groups` (ESTABLISHED,
proposed, referee pending). That node derives it for every locally indicable `G` from
"Jaikin-Zapirain (*The universality of Hughes-free division rings*, 2021): `D` is the universal
division `Q[G]`-ring of fractions".

- **Import concern.** The abstract (I3) does not say that. It says the paper studies
  universality "in some of these cases", and that "in particular" it proves universality for
  RLA groups.
- The other universality statement recorded in the graph is FSP's `thm:HFresults`, quoted in
  `fsp-graph-of-rings-and-linnell-extension-citation`. It covers "locally indicable amenable",
  "residually (torsion-free nilpotent)" and "free-by-cyclic" groups. All three classes are RLA
  (Proposition 3 for the last).
- So unless the body of JZ21 proves more (it was not read here), item 1(ii), and with it (iii)
  and item 3 of that node, are supported only for RLA groups.
- The flagship uses of that node, items 4–5, concern amenable groups, where RLA holds. So they
  survive.
- This is flagged on the bus. That node is not edited here.

**5.3 Thompson's group `F`.**
- `F` is bi-orderable, hence locally indicable.
- Every nontrivial normal subgroup of `F` contains `[F, F]`, and every proper quotient is
  abelian (Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*, Thm 4.3).
- So `F` is RLA if and only if `F` is amenable:
  - if `F` is amenable, it is LI amenable itself;
  - conversely, take `1 != g in [F, F]` and `N` with `g ∉ N`; then `N = 1`, so `F = F/N` is
    amenable.
- Hence: if `F` is amenable, `F` is torus-surjunctive at every `d`. If `F` is not amenable,
  C2 over `F` by this route needs (AD) for `F`, which is open.
- In the amenable case Gottschalk over `F` is already classical, so for the flagship the
  interesting case is non-amenable `F`, where only (AD) would help.

**5.4 Relation to Gottschalk.** RLA groups are residually amenable, hence sofic, so Gottschalk's
conjecture is already known over them (Gromov; Weiss). This result advances only the torus lane,
C2 and `every-group-is-torus-surjunctive`. The bottleneck from torus to finite alphabets,
`torus-surjunctivity-implies-finite-alphabet-surjunctivity`, is untouched.

Theorem 1 itself is not an approximation argument, though. It would reach a non-sofic group as
soon as that group, or just the support subgroups of its degree matrices, satisfies (AD). So
(AD) is an independently failable prerequisite for C2 that is orthogonal to soficity:
- C2 on locally indicable groups ⇐ (AD) on locally indicable groups.
- C2 on groups with torsion is out of reach of (AD) by 5.1.

**5.5 Side record: sofic local defect lemma.** The w10 NEED asked for a local small-fibre lemma
for sofic models. No proof was found. The non-local version is false, since the null-homotopic
embedding `T^N -> T^(N+1)` has `f^* = 0` in degree one. The route above bypasses soficity for
the RLA class entirely. It uses the ring `D_{Q[H]}` rather than finite models.
