# Literature status: MF reduced C-star algebras of infinite Kazhdan groups

Lane `ex-mf-kazhdan-cstar`, 2026-09-12.  Every quotation below was read from
the arXiv PDF fetched on MSI this session (`curl -L https://arxiv.org/pdf/<id>`)
and read locally, page or line cited.  The search bound is stated at the end.

## [MdlS] Magee--de la Salle, arXiv:2312.03220v2 (30 Jan 2024)

*SL_4(Z) is not purely matricial field*, C. R. Math. 362 (2024) 903--910.

- **Theorem 1.1** (p. 1).  "Every finite dimensional unitary representation of
  SL4(Z) contains a non-zero SL2(Z)-invariant vector."  Here `SL_2(Z)` is the
  upper-left block `[[*,*,0,0],[*,*,0,0],[0,0,1,0],[0,0,0,1]]`.
- **Definition 1.2** (p. 1): `rho_i -> lambda_Gamma` strongly if
  `lim ||rho_i(z)|| = ||lambda_Gamma(z)||` for every `z in C[Gamma]`; `Gamma` is
  purely matricial field (PMF) if some sequence of finite-dimensional unitary
  representations does this.
- **Corollary 1.3** (p. 2).  "SL4(Z) is not purely matricial field."  Proof:
  `||rho(S+S^-1+T+T^-1)|| = 4` in every finite-dimensional `rho`, while the
  regular norm is the `SL_2(Z)` Kesten norm `< 4`.
- **Status sentence** (p. 2).  "It does not seem to be known whether
  C*_r(SL3(Z)) or C*_r(SL4(Z)) is MF in the sense of Blackadar and Kirchberg."
- **The gap at three** (p. 2).  "Theorem 1.1 does not hold with 'four' replaced
  by 'three', since for primes p there are nontrivial irreducible
  representations of SL3(Z/pZ) without non-zero SL2(Z/pZ)-invariant vectors
  (P. Deligne, private communication, see Example 2.2). Nevertheless it could
  still be the case that SL3(Z) is not purely MF and we would be very
  interested to know the answer of this question. It would perhaps clarify the
  relation between property (T) and purely MF — as far as we know there is no
  direct relation."
- **Reduction** (p. 3).  By Bass--Milnor--Serre (and [Bek07, Section 5]) every
  finite-dimensional unitary representation of `SL_4(Z)` factors through
  `SL_4(Z/NZ)`; the proof is Proposition 2.1 for `SL_4(Z/NZ)`, reduced to prime
  powers by the Chinese remainder theorem and tensor products of invariant
  vectors.
- **Example 2.2** (p. 8, due to Deligne).  "For every prime power q, SL3(Fq)
  has an irreducible representation such that, for every g in SL2(Fq),
  Tr(pi(g)) = (q-1)(q^2-1) if g = 1; 1-q if (g-1)^2 = 0 != g-1; 0 if
  (g-1)^2 != 0.  This representation does not have a non-zero
  SL2(Fq)-invariant vector."  These are the characters `chi_{r^2 s}(u)` of
  Simpson--Frame [SF73, Table 1b], attached to tori of split rank 0.

## [Mag25] Magee, arXiv:2503.21619v1 (27 Mar 2025)

*Strong convergence of unitary and permutation representations of discrete
groups*.

- Section 2 (text lines 234--237 of the extracted PDF): "there is a lacuna in
  the field: we do not know how to construct explicit f.d. representations of
  free groups that strongly converge to the regular representation".
- Section 2.4, *Non-examples*: "With M. de la Salle we established [MdlS23]
  that SLd(Z) is not PMatF for d >= 4. This leaves a curious gap at d = 3."
  Then: "there are f.d. irreducible unitary representations of SL3(Z) with
  dimension tending to infinity and without non-zero SL2(Z)-invariant vectors.
  See (ibid.) for details — this example is due to Deligne."
- The survey does not mention property (T) outside its bibliography (grep of the
  extracted text: `Kazhdan` occurs only in the reference to Bekka--de la
  Harpe--Valette).

## [vH25] van Handel, arXiv:2510.12520 (ICM 2026 survey)

*Strong Convergence: A Short Survey*.

- Section 2.2, after Theorem 2.5 (Cassidy): "Could one hope to achieve strong
  convergence with no randomness at all, using number-theoretic constructions
  such as those that have been used to obtain regular graphs with optimal
  spectral properties [64]? These tantalizing questions remain very much
  open."  Reference [64] is Lubotzky--Phillips--Sarnak, *Ramanujan graphs*.
- Section 2.3, *Beyond freeness*: Theorem 2.6 (Louder--Magee, limit groups,
  random permutation representations) and Theorem 2.8 (Magee--Thomas,
  right-angled Artin groups, random unitary representations), then: "it was
  shown by Magee and de la Salle [66] that the group SL4(Z) does not even admit
  a strongly convergent sequence of unitary representations. Beyond the results
  discussed above, the question of which groups admit strongly convergent
  representations remains largely open."
- No statement about property (T) groups.

## Consequences for `infinite-kazhdan-group-with-mf-reduced-cstar`

1. **Open, including `SL_4(Z)` in the approximate sense.**  MdlS exclude only
   genuine representations of `SL_d(Z)`, `d >= 4`.  By their own status
   sentence, MF of `C*_r(SL_4(Z))` (asymptotic homomorphisms) was not known in
   2024.  Nothing found in 2025--26 changes this.
2. **`SL_3(Z)` is open even for genuine representations.**  MdlS ask for it
   explicitly; Magee's survey calls it "a curious gap at d = 3".
3. **No explicit strongly convergent sequence is known for any nonamenable
   group.**  So a positive answer through congruence quotients of an
   arithmetic Kazhdan lattice would also be the first deterministic
   strong-convergence theorem, above the free-group case [vH25, Section 2.2].
4. **Every known source is a-T-menable** (limit groups, RAAGs and their virtual
   subgroups, Coxeter and 3-manifold groups; GKMP amalgams and GKM extensions
   need a Kazhdan seed already).  This matches the root node's attempts.

## Search bound

WebSearch queries run 2026-09-12: "strong convergence representations SL_3(Z)
property (T) arXiv 2025 2026"; "Magee de la Salle strong convergence SL_4(Z)
invariant vectors"; "strongly converging OR strong convergence property (T)
hyperbolic group random representations MF reduced C*-algebra"; "purely
matricial field OR strongly convergent property (T) lattice arXiv 2026";
"SL_3(Z) OR SL(3,Z) matricial field OR strong convergence reduced C*-algebra
2025 2026 arXiv"; "strong convergence Ramanujan graphs LPS congruence quotients
explicit deterministic strongly convergent".  Hits: the three surveys above,
GKMP arXiv:2603.24502, Shulman arXiv:2603.13564 (MF of amalgams; grep of its
text shows no Kazhdan or `SL_3` statement), Toeplitz exactness
arXiv:2604.14106, Caspers--Chen arXiv:2607.15100.  None gives strong convergence
or MF for an infinite property (T) group, and none proves `SL_3(Z)` not PMF.
This is a search-engine bound plus three surveys, not an exhaustive review.
