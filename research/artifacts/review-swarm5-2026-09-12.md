# Review of swarm-5 claims, 2026-09-12

Lane `swarm5-reviewer`. Adversarial review of ESTABLISHED claims landed after about
16:00, split with `swarm4-reviewer`. That lane already covers:
- in `review-swarm4-2026-09-12.md`: 548bdf1fd (§18), 4c08f019b (§22), fb8f58e9b (§24),
  ce98de0fc (§26), and cbc0cacb1, 8eaac4437, a442c4975, 34e7a8c0b, 272475ab8 (§27);
- 4a1570fd4, 4f3e5243a, fd68ee7ab, 2b19d1c07 and d34e26446.

**Sources.** The MSI login master was down, so every citation below was checked
against the arXiv PDF, fetched locally with `curl` and read with `pdftotext` or the
PDF reader. Primary sources that could not be fetched are marked. `cairn check` and
`cairn why` were not run, for the same reason. The only graph edits here are wording
and citation notes; no id, route or `requires` changed.

Verdicts: **PASS**, **GAP** (true, but a stated input or citation is missing or
wrong), **FAIL** (a false statement, corrected forward here).

---

## 1. `a2-action-with-non-finitely-presented-image` (12bd1722d). PASS

*Priority review.* This claims to answer Question 5.8 of Fournier-Facio–Wu–Zaremsky,
arXiv:2603.24687v2.

**Fidelity.** Read from the v2 PDF (dated 2 Apr 2026):
- **Question 5.8 (p. 27), verbatim:** "Does there exist an example of a group action
  G ↷ S that is of type [A_2] such that G/ker(G ↷ S) is not finitely presented? (This
  is equivalent to the induced action of this quotient on S being not of type (A_2).)"
  The claim quotes it exactly.
- **p. 25:** "(That being said, we do not know an explicit example where it fails, see
  Question 5.8.)" This matches the claim.
- **Definition 1.3 (pp. 2–3):** type [A_n] means (i) G is of type F_n; (ii) for every
  finite T ⊆ S, Stab_G(T) is of type F_{n−|T|}; (iii) the diagonal action on S^n has
  finitely many orbits. For n = 2 that is: G finitely presented, point stabilizers
  finitely generated, finitely many orbits on S². These are exactly the three
  conditions checked in `normalizer-extension-of-type-a-actor-is-a2-cover`.
- **Theorem B = Theorem 4.1 (pp. 3, 16), and Corollary 4.2 (p. 16):** they give the
  consequences in items 3 and (6) of the claim.

The claim answers exactly what is asked, with no weaker hypotheses.

**Construction, checked line by line.**
- **(1) Actor.** V ↷ Ω_C is type (A): V is finitely presented, faithful, has 7 orbits
  on ordered pairs, and stabilizers are D(U) × D(U^c) ≅ V × V. So Γ = SV_V is finitely
  presented by Zaremsky's criterion as quoted in FFWZ p. 3.
- **(2) Normalization.** I recomputed δ_w f δ_w⁻¹ on δ_w(B(p)):

  ```
  (δ_w f δ_w⁻¹ κ)(s) = w(q(s) · strip_{p(g⁻¹s)}(w⁻¹ κ(g⁻¹s)))
  ```

  This matches the route's φ_t. Outside F it is the identity; on F it splits into
  prefix replacements. The bricks B(u_j) partition δ_w(B(p)), and the images are
  bricks. Correct.
- **(3) δ(V) ∩ Γ = 1.** The coordinate s is chosen outside supp p, g(supp p), supp q
  and g⁻¹(supp p). Both coordinates κ(s) and κ(g⁻¹s) are then free on B(p), which
  forces g⁻¹s = s and w = id. Correct.
- **(4) Z≀Z ≤ F.** The standard lamplighter inside F. The fundamental domain
  [1/4, 1/2) = [t(1/2), 1/2) is correct.
- **(5) Kernel and image.** Q ∩ Γ = 1, so the kernel is ker φ and the image is
  Γ ⋊ (Z≀Z). The image is not finitely presented by Baumslag 1961 plus quotienting by
  the finitely generated normal Γ.
- **(6) Simple quotient.** Not finitely presented, by FFWZ Corollary 4.2.
- **(7) Kernel removal.** ker = {1} × ker ψ. Its normal closure in G′ equals its normal
  closure in F_2∗V, because θ_k = id for k ∈ ker ψ. Correct.

**Supporting claims.**
- **`twisted-btb-clopen-action-is-type-a`: PASS.** Clopen sets are brick unions with
  adjustable counts. Tuples in the same atom pattern are in one orbit. Stabilizers
  split as D(U) × D(U^c), and each factor ≅ SV_G. I recounted the pair patterns:
  7 ordered, 5 unordered.
- **`normalizer-extension-of-type-a-actor-is-a2-cover`: PASS.** Π is a homomorphism;
  the kernel is as stated; the semidirect product is finitely presented. The stabilizer
  projection to F_m has finite index, because φ(w) permutes the finitely many Γ-orbits.
  The image is not finitely presented through ΓQ/Γ.

**Novelty (bounded).** No later paper was found:
- Zaremsky's arXiv listing after 2603.24687 has two papers ("Action graphs,
  semiconjugacy, and non-embedding in V" and "Word length, Morse theory, and
  Vietoris–Rips complexes").
- Fournier-Facio's listing has three ("Finiteness properties and Higman's rope trick",
  2607.21727; "A torsion-free non-sofic group", 2608.02025; and a bounded cohomology
  paper).

None addresses Question 5.8; the rope-trick abstract was read. The arXiv API search
for "twisted Brin" returned HTTP 503.

## 2. `c-tilde-artin-groups-satisfy-permutational-boone-higman` (21dfc8888). PASS

*Priority review.* Also `c-tilde-artin-groups-are-punctured-plane-braid-groups`:
PASS.

**Fidelity: both sources really list C̃_n, n ≥ 3, as open.**
- **BFFHZ arXiv:2503.21882v2, after Corollary B, verbatim:** "For spherical and
  Euclidean Artin groups, the Boone–Higman conjecture remains open for the exceptional
  type spherical Artin groups, and the Euclidean Artin groups other than type Ã_n; in
  rank 3 it is also known for type C̃_2 and G̃_2 (and Ã_2, which we recover) [BLIW]."
- **Survey arXiv:2306.16356v3, Remark 5.4, verbatim:** "item (13) remains open for many
  classes of Artin groups, including those of exceptional spherical type and those of
  Euclidean type other than the Ã_n and triangle cases (C̃_2 and G̃_2)."
- **Corollary B's list:** B_n = C_n, D_n, I_2(m), Ã_n. The proof of Corollary B uses
  B_n → LB_n → LB^ext_n → Aut(F_n), annular braid groups, [KP02], [PV92] and
  commensurability. C̃_n does not appear.

**The identification.** Read from Allcock, arXiv:math/9907194v1.
- **Convention:** "each diagram X_n has n + 1 nodes".
- **Table 1.1, row C̃_n:** "2 punctures | quotient 1 | n > 1". The caption says the Artin
  group "is a normal subgroup of the n-strand braid group of the orbifold which is the
  plane equipped with the given features"; with quotient 1 the two are equal.
- **§4, "The diagram C̃_n":** W = Z^n : 2^n : S_n, V0 = {x_j ± x_k ∉ Z, x_j ∉ ½Z}, and
  "this identifies V0/(Z^n : 2^n) with the pure braid space of C − {0, 1/2}".

I checked this independently, with no index shift.
- x ↦ 2cos 2πx identifies (C − ½Z)/D_∞ with C − {±2}, and D_∞ acts freely there.
- x_j ± x_k ∉ Z is equivalent to the cosines being different.
- So π_1(V0/W) = π_1 UConf_n(C − {±2}), with n strands and n + 1 = rank(C̃_n)
  generators, as expected.
- Nguyễn's theorem (π_1 of the regular orbit space is the affine Artin group) is cited
  through Allcock and was not read.

**The embedding A(C̃_n) ≤ B_{n+2}.** The route's Fadell–Neuwirth argument is correct:
the base Conf_2(C) ≃ S¹ has π_2 = 0 and the fibre is connected.

*Caveat on the Charney–Crisp quotation.* Charney–Crisp arXiv:math/0408412v1, p. 2,
lines 183–184 of the extracted text, says "the Artin groups A(B_n) and A(C̃_{n−1}),
respectively, are isomorphic to the subgroups of the braid group A(A_n) leaving fixed
one, respectively two, of the punctures". With Allcock's identification, the stabilizer
of two punctures in B_{n+1} is an extension of Z (the twist of those two punctures) by
π_1 UConf_{n−1}(C − {p, q}). So "isomorphic to the stabilizer" seems to overstate it by
a Z; the abelianizations differ. Either way A(C̃_{n−1}) is a subgroup of B_{n+1}, and the
claim only uses the embedding. Nothing downstream depends on the stronger wording.

**Closure.**
- **Braid groups:** permutational Boone–Higman holds, by BFFHZ Theorem A (Aut(F_n))
  and the proof of Corollary B (B_n ↪ Aut(F_n)).
- **Subgroups:** "embeds in a group admitting an action of type (A_2)" passes to
  finitely generated subgroups trivially (FFWZ Conjecture 1.5 wording, p. 3).
- **Finitely presented simple envelope:** "equivalently embeds in a finitely presented
  simple twisted Brin–Thompson group" (FFWZ p. 3, citing [Zar24, BFFHZ]).

**Not re-checked.** The "Consequence" paragraph (closure under direct and free products
through BFFHZ Corollary F) was not re-read from source. **Novelty** is bounded: the arXiv
API searches for "Boone-Higman" and "Artin + Boone" came back empty, apparently
rate-limited. The combination is direct, but both 2025 sources list the case as open.

## 3. `one-sided-inverse-pairs-transfer-to-table-realizations` (a2807a30e). PASS

- **Push-forward theorem:** correct; linearity handles merged products.
- **Corollary 1:** finite-dimensional algebras are directly finite, and realizations
  combine through products.
- **Corollary 2:** U(A, B) is canonical and injective on cells, and pairs transfer both
  ways along realizations.
- **Corollary 3:** U(B_r, B_r) ≅ G_{4r}. I rechecked both maps:
  - the relator lengths r + r + 2r = 4r, which needs geodesic w_g, as the landed text
    says;
  - the four-block cutting of trivial words of length ≤ 4r;
  - both composites.

  The ball B_{2r} maps bijectively.

No literature input beyond the credited Elek–Szabó idea.

## 4. `approximately-orthogonal-unitary-translates-kill-quasitraces` (abc9e32f4). GAP (citation)

The computation is correct.
- **Quarter-power bound:** ‖b^{1/2}c^{1/2}‖⁴ = ‖c^{1/2}bc^{1/2}‖² ≤ ‖bcb‖ ≤ ‖bc‖.
- **Off-diagonal block:** ‖E‖ ≤ mδ^{1/4}.
- **Diagonal:** σ̃(diag(a_i)) = mσ(a), by commuting additivity plus unitary invariance.
- **Sandwich:** diag − ε1 ≤ X*X ≤ diag + ε1 with commuting ε1, which gives
  σ(a) ≤ σ(1)/m + (m+1)δ^{1/4}σ(1).
- **Ideal form:** N_σ is closed under addition by σ(x*x + y*y) ≤ 2(σ(x*x) + σ(y*y)).
  This follows from ZZ* ≤ 2 diag(xx*, yy*) in M_2 plus monotonicity, so the ideal
  statement holds.

**The gap.** The route says "No literature import", but step 3 uses the extension of a
bounded 2-quasitrace σ to M_m(A) for arbitrary m. That extension is a standard theorem
(Blackadar–Handelman), not one of the 2-quasitrace axioms. It should be cited; the
primary source was not fetched. The conclusion is unaffected.

## 5. `sl3z-ozawa-block-corona-has-unique-trace` citation edit (021e5a3d4). PASS

Bekka, arXiv:math/0609102v2, read from the PDF.
- **Theorem 1** is virtual: case (ii) extends only on a finite-index Λ.
- **Theorem 3:** "Let φ be a character of SL_n(Z) for n ≥ 3. Then, either (i) φ is the
  character of an irreducible finite dimensional representation of some congruence
  quotient SL_n(Z/NZ) … or" the trivial extension of a central character. The text just
  before it says: "SL_n(Z) for n ≥ 3 has no characters other than the obvious ones
  described above".
- **Centre:** trivial for odd n (p. 3), so for n = 3 this is δ_e.

The edited source note is accurate.

## 6. `thompson-v-sofic-via-folner-full-group-theorem`, dead route (6202b06a3). PASS

**Structure.** The route has `requires: []` and targets `thompson-v-is-sofic`. It is
invalidated by `cuntz-groupoid-admits-no-folner-sequence`, which lists it under
`invalidates:` and has a proof route requiring
`thompson-v-cantor-orbits-have-no-folner-sets`. So the dead route cannot establish V's
soficity, provided that invalidator is established. `cairn why` was not run.

**Citation.** Ma, arXiv:2110.11548v1, read from the PDF.
- **Theorem C = Theorem 7.5:** "Let G be a locally compact Hausdorff minimal second
  countable ample groupoid with a compact unit space. Suppose G admits a Følner
  sequence. Then [[G]] is sofic."
- **Corollary D(1):** the fiberwise amenable version, for a unit with trivial isotropy.

The route's paraphrase drops "ample, compact unit space", which the Cuntz groupoid
satisfies. Accurate.

## 7. Full-group obstructions for finitely presented simple amenable groups (d86f04c21). PASS ×3

- **`amenable-full-group-forces-invariant-measure`.**
  - The 3-cycle commutator abab restricts to U on E (recomputed).
  - The Markov–Kakutani measure is invariant on moving germs; fixed germs are handled
    by detouring through W; compactness globalizes.
  - Minimality gives full support, hence the compressibility contradiction.
  - SFT example: v = Av, ρ(A) = 1; min row sum ≤ ρ with equality iff all row sums are
    equal, so A is a permutation matrix.
- **`fp-subshift-full-group-subgroups-extend-to-sft`.**
  - Local rules and formal cocycles.
  - Y_2 and Y are SFTs containing X.
  - π is surjective with left inverse restriction, so it is an isomorphism.
  - A finite orbit gives a finite image, which is trivial for an infinite simple group.
- **`periodic-approximable-subshifts-host-no-fp-simple-group`.**
  - Item 1: the y given by (PA) lies in Y and is moved by n, contradicting item 2 of the
    extension claim.
  - Item 2: I rechecked the periodic gluing. y agrees with x on [−N, N+2M+q], every
    length-(2M+1) window of y occurs in x, and the least period of y exceeds max|B|.

Matui Theorem 5.7 was not re-read. The root `fp-infinite-simple-amenable-group` is
correctly OPEN.

## 8. Kadison–Kaplansky fence on torsion-free SL_3(Z) subgroups (5c01600ce). PASS ×4

- **`assembly-image-traces-are-integral-for-torsion-free-groups`.** Gomez Aparicio–Julg–
  Valette, arXiv:1905.10081, Proposition 4.20 and its proof (extracted lines 1757–1792):
  "assuming Γ to be torsion-free, τ∗ is always integer-valued on the image of µr".
  Verified. Atiyah 1976 not read.
- **`lafforgue-unconditional-assembly-for-reductive-lie-subgroups`.** Lafforgue ICM,
  arXiv:math/0304342:
  - Theorem 1.6.2, verbatim: "For any group G in the classes a’), b) or c’), and for any
    unconditional completion A(G) of C_c(G), µ_A … is an isomorphism."
  - Line 342: "respectively contain all closed subgroups of reductive Lie" groups.
  - Line 350: "slightly incorrect".
  - Line 192: µ_red = i∗∘µ_{L¹}.

  Verified. Invent. Math. 2002 not read.
- **`sl3z-has-no-spectral-unconditional-completion`.** Gomez Aparicio–Julg–Valette,
  Remark 6.18, verbatim: SL_3(Z) "does not have property (RD) … there is no
  unconditional completion B(Γ) that is a dense subalgebra of C*_r(Γ) stable under
  holomorphic calculus", with H = Z² ⋊ Z via [[3,1],[2,1]]. Verified. Jolissaint,
  Lafforgue 2010 and Jenkins were not read.
- **`unconditional-spectra-of-kk-witnesses-cross-the-gap`.** Rechecked step by step:
  - integer traces from μ_A onto plus trace integrality;
  - no idempotents, by similarity to a projection plus a faithful trace;
  - the Riesz projection maps to χ_{(−∞,c)}, with holomorphic and continuous calculus
    agreeing on the real spectrum;
  - the n = 1 gap gives a non-integer μ_a((−∞, c)), since the spectral measure has full
    support;
  - the RD case goes through H^s_ℓ(Λ) as a spectral unconditional completion, with
    spectral permanence.

  Correct. The capacity item depends on an existing node.

## 9. Strong Atiyah for congruence Kazhdan groups (7e4ff5d66)

### 9a. `congruence-kazhdan-groups-satisfy-strong-atiyah`. FAIL in item 1, corrected forward

**The error.** Item 1 said "Gamma(3) and every subgroup of it … is infinite,
torsion-free and has property (T)". That is false: infinite cyclic subgroups do not have
(T), and the trivial subgroup is finite. The correct statement: Γ(3), its finite-index
subgroups and E_3(3) are infinite, torsion-free and have (T); every subgroup is
torsion-free.

**The fix.** Items 2–3 hold for every subgroup, and the claim now says so, with a review
note in the claim. The title and all consequences drawn elsewhere, including that
E_3(3) is a Kazhdan group satisfying Strong Atiyah and has no zero divisors in
characteristics 0 and 3, are unaffected.

**Minor.** The route attributes finite index of E_3(3) = ⟨e_ij(3)⟩ to Bass–Milnor–Serre.
Their theorem concerns the normal closure of the elementary matrices. That the subgroup
they generate has finite index for d ≥ 3 is due to Tits (1976). Not load-bearing.

### 9b. `p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah`. GAP (citation), noted in the claim

Farkas–Linnell, arXiv:math/0511747v2, read from the PDF.
- **Theorem 1.1:** as quoted.
- **Theorems 1.2 and 1.3:** stated only for Γ = CS(u,d,p) itself.

Part 2 for a W that properly contains CS(u,d,p) needs two more inputs:
- **characteristic p:** FL Theorem 6.1, "k[[G]] is a right and left noetherian domain",
  restated as Fisher–Ng Theorem 2.10, together with k[H] ⊆ k[[W]];
- **characteristic 0:** part 1, through Fisher–Ng §2, lines 396–398 of the extracted text.

The conclusion is correct, and the missing citation is now recorded in the claim.

**Fisher–Ng, arXiv:2606.19606v1**, read from the PDF:
- Theorem 2.11: "If G is a torsion-free compact p-adic analytic group, then G satisfies
  the Strong Atiyah Conjecture over C."
- Line 400: passage to subgroups "is the case for subgroups of torsion-free groups".
- Line 40: the Out(F_n) property (T) citations [KKN21, Nit23].

All verified. The rest of part 1 and the W × Z instance argument check out: W ∩ Z = 1,
CS(v,d,p) ≤ W × Z is normal, and it has finite index by dimension.

---

**Corrections landed with this artifact:**
- `research/congruence-kazhdan-groups-satisfy-strong-atiyah.md`: item 1 narrowed, with a
  review note;
- `research/p-adic-analytic-torsion-free-groups-satisfy-strong-atiyah.md`: citation note.

**Cross-check noted for §27 of `review-swarm4`.** The phrase "the cocycle is not trivial"
in `leavitt-tensor-powers-are-twisted-crossed-products` only shows ω ≢ 1 for the chosen
lifts u_1, u_2. It is not a statement about the cohomology class, and nothing downstream
uses one.
