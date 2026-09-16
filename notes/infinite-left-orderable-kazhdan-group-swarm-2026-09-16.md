# Swarm log: `infinite-left-orderable-kazhdan-group` (Navas Question 3), 2026-09-16

The agent was `swarm-infinite-left-orderable-kazhda`. It locked the target claim itself.
The outcome is a **reduction/equivalence**, not a resolution. Q3 remains open.

## 1. Setup

The target is the root claim "There is an infinite left-orderable group with property
(T)", which is Navas, arXiv:1712.06462v2, p. 3, Question 3. The same page poses Question
2 (circle version) separately and says "the answers to both Question 2 and 3 remain
unclear". The graph had only the interval/line form, together with the Aut(F_4) and
rigid-pair routes.

## 2. Literature gate (checked 2026-09-16)

Web search was unavailable, because the per-session budget was exhausted. The gate
used the arXiv API and direct PDF text extraction instead.

**Read directly:**

- **Navas**, arXiv:1712.06462v2, pp. 1-4. Poses Q1-Q3 as open, with the `C^{3/2}`
  finiteness result and the relative-(T) examples `SL(2,Z) ⋉ Z^2`, `F_2 ⋉ Z^2`.
- **Duchesne**, *A group with Property (T) acting on the circle*, arXiv:2011.12861v3
  (v3 dated 2021-05-04; journal ref IMRN 2023, no. 12, pp. 10615-10640).
  - p. 1: "The question of the existence of an infinite countable group with Property
    (T) acting faithfully on the circle is still open."
  - Remark 1.7 (p. 3): `Homeo_+(S^1)` has (T) as a topological group, because it has no
    nontrivial unitary representations. That rests on Glasner--Megrelishvili, which was
    not re-read.
- **Lodha--Matte Bon--Triestino**, arXiv:1803.08567v4, §1 (p. 3).
  - "It remains a wide open problem whether there exists an infinite Kazhdan group of
    circle homeomorphisms."
  - Corollary 1.5(i): homomorphisms from countable Kazhdan groups to `PDiff^{3/2}(S^1)`
    have finite image.
  - Corollary 1.5(ii): homomorphisms to `ΩDiff^{3/2}(S^1)` have a finite orbit.
  - The paper does not relate the circle question to the interval question.
- **Bekka--de la Harpe--Valette**, *Kazhdan's Property (T)*, from the authors' PDF text.
  Re-read: Thm 1.3.1, Cor 1.3.5, Cor 1.3.6, Thm 1.7.1, Thm 1.7.11 (Serre), Example
  1.7.13(iii), Thm 2.12.7.

**Checked more lightly:**

- **Vergara**, arXiv:2407.03579v3 (8 Dec 2025), p. 1: still open. This was already
  quoted in the target claim.
- **Deroin--Hurtado**, arXiv:2008.10687. Full-text grep only, for "Kazhdan", "circle"
  and "lift". The circle-to-line passage there is only for higher-rank lattices, through
  Ghys.
- **arXiv API listings**:
  - `abs:"property (T)" AND abs:circle` returned 9 entries, none a resolution.
  - Title/abstract queries on left-orderable Kazhdan groups surfaced several papers.
    None resolves Q2 or Q3. Metadata was re-fetched on 2026-09-16:
    - Fedorynski--Lodha, arXiv:2509.09856v1 (2025-09-11), on the simple
      left-orderable groups `G_ρ`;
    - Orlef, arXiv:1409.1289v4, *Random groups are not left-orderable*;
    - Brum--Matte Bon--Rivas--Triestino, arXiv:2104.14678v3 (2024-11-21), *Locally
      moving groups and laminar actions on the line*.
  - Gonen Cohen, arXiv:2607.00697v2 (2026-08-21), concerns actions of p-adic and
    S-arithmetic lattices on manifolds. That is the lattice setting (Question 1 type),
    not a resolution of Q2 or Q3.

**Verdict.** No resolution of Q2 or Q3 was found as of 2026-09-16, within these sources.

## 3. What was proven

The complete proofs are in
`research/artifacts/kazhdan-circle-group-lift-dichotomy-2026-09-16.md`.

**Theorem (lift dichotomy)**, node `kazhdan-circle-group-lift-dichotomy` (ESTABLISHED
through `kazhdan-circle-group-lift-dichotomy-proof`). Let `G ⊂ Homeo_+(S^1)` be
Kazhdan and `Ĝ = p^{-1}(G) ⊂ Homeo_Z(R)` be its full lift. Then exactly one of the
following holds.

- **(A)** A subgroup of `Ĝ` maps isomorphically onto a normal finite-index subgroup of
  `G`.
- **(B)** `Ĝ` is Kazhdan.

*Proof idea.*

- If some `φ : Ĝ → R` has `φ(T) = 1`, then `ker φ` works for (A). The quotient `G/K` is
  abelian, hence finite.
- Otherwise `Hom(Ĝ,R) = 0`. Since `Ĝ` is finitely generated, `Ĝ^{ab}` is finite, and
  Serre's central extension theorem (`bdhv-central-extension-property-t`) makes `Ĝ`
  Kazhdan.
- Exclusivity: (A) produces a finite-index `K̂ × Z` inside `Ĝ`.

Case (A) is the vanishing of the real Euler class.

**Corollary (Navas Q2 ⟺ Q3).**

- The new OPEN claim `infinite-kazhdan-group-of-circle-homeomorphisms` is Q2.
- Route `infinite-left-orderable-kazhdan-group-from-circle` (Q2 ⟹ Q3): pass to the
  index-≤2 orientation-preserving part, then take `K ≅ K̂` or `Ĝ_+`. Both are subgroups
  of `Homeo_+(R)`, and so they are left-orderable.
- Route `infinite-kazhdan-group-of-circle-homeomorphisms-from-line` (Q3 ⟹ Q2):
  dynamical realization, then one-point compactification of the line.
- The two routes form a 2-cycle whose other prerequisites are established. It is the
  kernel's equivalence pattern, and check.sh accepted it.

**Consequence for attacks.** A Q3 witness can always be taken to be one of two kinds:

- (A) a Kazhdan group acting on the line that commutes with an integer translation,
  with zero real Euler class;
- (B) a Kazhdan group whose centre contains the translation `T`.

So a proof that Kazhdan subgroups of `Homeo_+(R)` are trivial may not assume a finite
centre, or the absence of a central element acting freely.

*(Referee correction: this is weaker than it sounds; see §7. Shape (A) is automatic
for every line witness, so the dichotomy is not a normal form. It gives no WLOG
reduction in either direction.)*

**Correction made during the session.** The first draft of the dynamical-realization
lemma used the midpoint embedding `t : H → R`, its closure and affine gap filling. Its
justification of bijectivity on the closure was incomplete: that needs the fact that
every gap of `closure(t(H))` has both endpoints in `t(H)`. The fact is true, since a gap
not ending in `t(H)` halves infinitely often, but it was unstated.

The draft was replaced by a gap-free proof, which is the artifact's Lemma 2:

- `H ×_lex Q` is a countable dense order without endpoints;
- Cantor's back-and-forth theorem, proved in the artifact, makes it isomorphic to `Q`;
- automorphisms of `Q` extend to `Homeo_+(R)` through Dedekind cuts.

## 4. Approaches tried, and where each dies

1. **Witte Morris's nilpotent mechanism on Aut(F_n), for the Aut(F_4) route.** It dies:
   - The mechanism needs a Heisenberg-type configuration `[a,b] = c` central in
     `⟨a,b⟩`.
   - Solvable subgroups of `Out(F_n)` are virtually abelian (Bestvina--Feighn--Handel;
     not re-read here), and `Aut(F_n) ⊂ Out(F_{n+1})`. So no Heisenberg subgroups
     exist.
   - Exact check in `experiments/kazhdan-circle-group-lift-dichotomy-2026-09-16/`
     (`transvection_commutators.py`, output `.out`), for the Steinberg-type triple
     `ρ_12, ρ_23, ρ_13` in `Aut(F_3)`, with `ρ_ij : x_i ↦ x_i x_j`:
     - With the convention `[a,b] = a b a^{-1} b^{-1}`, the commutator is
       `x_1 ↦ x_1 x_2 x_3^{-1} x_2^{-1}`, not `ρ_13^{±1}`.
     - With `a^{-1} b^{-1} a b` one gets `ρ_13^{-1}`. This was computed by hand.
     - Either way `ρ_13` does not commute with `ρ_12`: `ρ_13ρ_12(x_1) = x_1x_3x_2` but
       `ρ_12ρ_13(x_1) = x_1x_2x_3`.

     So the triple is not a Heisenberg group. This is evidence only.
2. **Obvious subgroup obstructions to virtual left-orderability of Aut(F_4).** Torsion
   is killed by passing to a torsion-free finite-index subgroup. Obstructions through an
   embedded higher-rank lattice are unavailable, by recollection of Bridson--Wade's
   theorem that higher-rank lattices have finite image in `Out(F_n)`; that source was
   not re-read. Nothing was concluded. The hole
   `aut-f4-has-left-orderable-finite-index-subgroup` is untouched.
3. **Finite positive-cone certificates.** SAT-style non-left-orderability certificates
   treat one finitely presented group at a time. Virtual left-orderability quantifies
   over infinitely many finite-index subgroups, and a certificate for one level subgroup
   does not transfer to deeper levels. No computation was run for this reason.
4. **Harmonic actions / Koopman spectral gap.** For an action on the line with a Radon
   quasi-invariant or stationary measure, (T) gives a spectral gap for the Koopman
   representation when it has no invariant vectors. No contradiction was derived:
   spectral gap by itself constrains nothing one-dimensional.
5. **Projective and lifted projective circle actions.** They have finite image (BdlHV
   Thm 2.12.7; artifact §6.1). This is an obstruction for a family only.
6. **An invariant probability measure on the circle.** It gives a finite-index subgroup
   with a fixed point, which is case (A). It produces a Q3 witness and yields no
   obstruction (artifact §6.2).
7. **Uniform unitary obstructions.** Dead (Duchesne, Remark 1.7).
8. **Regularity.** Dead beyond `C^{3/2}` and piecewise `C^{3/2}`: Navas, and LMT
   Corollary 1.5, re-read.

## 5. A direction not pursued (heuristic, sources not re-read)

The translation number `τ` on `Homeo_Z(R)` is a homogeneous quasimorphism with
`τ(T) = 1`. This is classical and was not re-proved here.

- *Case (B).* `Hom(Ĝ,R) = 0`, so `τ|Ĝ` is a nonzero homogeneous quasimorphism that is
  not a homomorphism. So a case-(B) witness `Ĝ` must be a Kazhdan group with
  `QM(Ĝ) ≠ Hom(Ĝ,R)`.
- *Case (A), assuming Ghys's theorem.* Suppose `e_b^R = 0` implies semiconjugacy to
  rotations, and so a finite orbit for Kazhdan `G`. Then a case-(A) witness without
  finite orbits has a nonzero real bounded Euler class that dies in `H^2(G;R)`. It is
  then given by a nonzero homogeneous quasimorphism on `G`.

If both steps hold, Kazhdan groups with no nonzero homogeneous quasimorphisms have no
infinite faithful circle actions without finite orbits. Higher-rank lattices are
examples, by Burger--Monod, not re-read. Hyperbolic Kazhdan groups have many
quasimorphisms (Epstein--Fujiwara, not re-read), so this rules out nothing there. This
is not in the graph. It would need Ghys's bounded-Euler-class theorem imported with a
checked citation.

## 6. Files

- `research/kazhdan-circle-group-lift-dichotomy.md` (claim, established)
- `research/kazhdan-circle-group-lift-dichotomy-proof.md` (route)
- `research/infinite-kazhdan-group-of-circle-homeomorphisms.md` (claim, OPEN: Navas Q2)
- `research/infinite-left-orderable-kazhdan-group-from-circle.md` (route, Q2 ⟹ Q3)
- `research/infinite-kazhdan-group-of-circle-homeomorphisms-from-line.md` (route,
  Q3 ⟹ Q2)
- `research/artifacts/kazhdan-circle-group-lift-dichotomy-2026-09-16.md` (proofs)
- `experiments/kazhdan-circle-group-lift-dichotomy-2026-09-16/transvection_commutators.py`
  and `.out`

`check.sh` on the six research paths exited 0 against landed `3ef186281`.

## 7. Referee (2026-09-16)

**Read in full:**

- the six research files: the two claims, the three routes and the artifact;
- this note and the experiment;
- the nodes they rely on: `bdhv-central-extension-property-t` with its citation route,
  `discrete-kazhdan-groups-are-finitely-generated`,
  `amenable-infinite-simple-circle-groups-fix-a-point-proof`, and the target claim.

`git status` showed no unlisted solver files.

**Mathematics checked, line by line:**

- *Lemma 0.* Covering, surjectivity of `p` via the constant `d = 1`, kernel `⟨T⟩`
  central.
- *Lemma 1.* The lexicographic left order at the first differing rational. Totality,
  transitivity and left invariance are all correct.
- *Lemma 2.* The order on `H ×_lex Q` is dense without endpoints, the action preserves
  it, Cantor back-and-forth, Dedekind-cut extension including monotonicity and
  continuity, and faithfulness.
- *Theorem 3, Case 1.* `p^{-1}(K) = K̂⟨T⟩` and `G/K ≅ φ(Ĝ)/Z`, which is abelian,
  hence finite.
- *Theorem 3, Case 2.* `Hom(Ĝ,R) = 0` and `Ĝ` is finitely generated, so `Ĝ^{ab}` is
  finite. Serre's theorem applies with `C = ⟨T⟩` central and `Ĝ/C ≅ G`. This matches
  the hypotheses of `bdhv-central-extension-property-t` exactly; a discrete compact
  abelianization means a finite one.
- *Exclusivity.* A finite-index `K̂ × Z` maps onto `Z`.
- *Both corollaries.* The index-≤2 orientation subgroup, and the one-point
  compactification with continuity at `[0]`.
- *Euler-class remark.* The cocycle identity `c = ψ(g) + ψ(h) - ψ(gh)` and its
  converse, recomputed.
- *Experiment.* Recomputed by hand: `[ρ12,ρ23](x1) = x1 x2 x3^{-1} x2^{-1}` with
  `aba^{-1}b^{-1}`, and `a^{-1}b^{-1}ab = ρ13^{-1}`. Both match.

No mathematical error was found. The 2-cycle of routes is the README's equivalence
pattern. Neither direction self-justifies, so Q2 and Q3 both stay OPEN.

**Citations spot-checked at source on 2026-09-16:**

- *Navas*, arXiv:1712.06462v2, LaTeX source: Questions 2 and 3 verbatim, the `C^{3/2}`
  sentence, the `SL(2,Z) ⋉ Z^2` blow-up, "the answers to both Question 2 and 3 remain
  unclear", and Ghys's finite-orbit theorem for higher-rank lattices.
- *Duchesne*, arXiv:2011.12861v3, source: the "still open" sentence (p. 1), and the
  Deroin--Hurtado finite-image sentence.
  - The Remark on `Homeo_+(S^1)` and Glasner--Megrelishvili is numbered 1.7: Definition
    1.1, Theorem 1.2, Propositions 1.3-1.6, then the Remark.
- *LMT*, arXiv:1803.08567v4, source: the "wide open problem" sentence, and Corollary
  `c-T` numbered 1.5 (Theorem 1.1, Remarks 1.2-1.3, Theorem 1.4, Corollary 1.5), with
  parts (i) `PDiff^{3/2}` finite image and (ii) `ΩDiff^{3/2}` finite orbit.
- *BdlHV*, authors' PDF (perso.univ-rennes1.fr/bachir.bekka/KazhdanTotal.pdf), text
  extracted by the referee:
  - Corollary 1.3.5, including the `R^n`/`Z^n` sentence;
  - Corollary 1.3.6, the discrete abelianization being finite;
  - Theorem 1.7.1, the finite invariant measure equivalence;
  - Example 1.7.13(iii), `Sp_{2n}(Z)` lifted, with infinite centre and (T) for `n ≥ 2`;
  - Theorem 2.12.7: continuous homomorphisms into `O(n,1)` or `U(n,1)` have relatively
    compact image.

  All match.
- *Vergara*, arXiv:2407.03579v3 source: still poses only the line version, as an open
  problem.
- *arXiv API listings* (2026-09-16): `abs:Kazhdan AND abs:circle` (18 entries),
  `abs:"property (T)" AND abs:circle` (9), `abs:"property (T)" AND abs:orderable`.
  No resolution of Q2 or Q3, and no statement of the equivalence. Web search was
  unavailable to the referee (budget exhausted). Novelty remains unaudited beyond these
  sources, and the equivalence may well be folklore; the nodes do not claim novelty.

**Changes made:**

1. *Overclaim softened.* The route `infinite-left-orderable-kazhdan-group-from-circle`
   said a triviality proof "cannot assume the centre is finite". That is replaced by the
   honest statement: the route gives no reduction to a finite centre, and shape (A) is
   automatic for every line witness, via the compactification and the periodic lift.
   - Artifact §4 now says the same, and the type-(ii) identification is marked
     heuristic.
   - §3 of this note carries a pointer to the correction.
2. *Missing justification added.* The claim `infinite-kazhdan-group-of-circle-homeomorphisms`
   asserted that the lifted `Sp_{2n}(Z)` groups are not groups of line homeomorphisms.
   The referee added a torsion argument: `diag(A,A) ∈ Sp_{2n}(Z) ∩ SU(n)` of order 4
   lifts with order 4 through the simply connected `SU(n)`. The claim's status check
   now records the referee's re-verification of the quotes.
3. *Wording.* In Lemma 0 of the artifact, "Clearly `p(FG) = p(F)p(G)`" is replaced by
   the one-line computation.

**Verdict:** landed with minor fixes. The dichotomy
`kazhdan-circle-group-lift-dichotomy` is sound and correctly ESTABLISHED, modulo the
imported BdlHV theorems already in the graph. The two routes soundly record
Navas Q2 ⟺ Q3. Q2, Q3 and `aut-f4-has-left-orderable-finite-index-subgroup` remain OPEN.
