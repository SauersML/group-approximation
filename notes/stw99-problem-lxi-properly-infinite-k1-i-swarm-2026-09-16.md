# STW Problem LXI swarm lane, 2026-09-16

Lane `swarm-stw99-problem-lxi-properly-inf`. Root: `stw99-problem-lxi-properly-infinite-k1-injective`.
Locked hole: `properly-infinite-unital-algebra-not-k1-injective-exists`, the negation claim. Outcome: an
equivalence reduction of LXI, with one new established claim. LXI is not decided.

## 1. Setup

A **witness** is a pair `(A, u)`: `A` unital properly infinite, `[u] = 0` in `K_1(A)`, `u notin U_0(A)`.
LXI says no witness exists. BRR Theorem 5.5 reduces it to `O_inf * O_inf`, and Blanchard 0804.4624v13,
Proposition 4.2, reduces it to `T_2 *_C T_2`.

The idea was to take a hypothetical witness and shrink it as far as possible. By Zorn, pass to a quotient
in which `u` survives but dies in every further quotient; call that witness **quotient-minimal**. Then
split on whether the quotient is prime.

## 2. What was established

Everything below is in artifact `research/artifacts/lxi-quotient-minimal-counterexamples-2026-09-16.md`.

1. **Proposition 1** (Rohde's thesis, Lemma 5.1.7, reproved). Every witness has a quotient-minimal
   quotient witness.
2. **Proposition 2** (after Rohde, Lemma 5.1.8 and the proof of Lemma 5.2.3). If `(B, v)` is
   quotient-minimal, then for every nonzero ideal `J`, `v` is homotopic to some `v_J in U(J~)` with
   `[v_J]_{K_1(J)} = 0`. So `J~` is not K1-injective and `J + sigma(T_2)` is again a witness. Moreover `B`
   has no nontrivial central projection, no stable ideal, and no ideal whose unitization has stable rank
   one. In the properly infinite setting Rohde's weak K0-surjectivity hypothesis is not needed: exponentials
   of lifts of projections realize every exponential-map class.
3. **Theorem 3 and Corollary 4** (new; not found in BRR, Blanchard or Rohde). Suppose a quotient-minimal
   witness `(B, v)` is not prime, with `J_1 ∩ J_2 = 0`. Then `D = B/(J_1 + J_2)` is nonzero and properly
   infinite, and there is a based loop `l` in `U(D)` with `kappa_D(l) = 0` in `K_1(SD)` that is not null
   relative to endpoints. In fact `[l]` avoids `pi_{1*}pi_1 U(B_1) · pi_{2*}pi_1 U(B_2)`. So
   `(C(T, D), l)` is a witness. The proof:
   - glues quotient paths through the pullback `B = B_1 ×_D B_2`;
   - first corrects both paths by Bott loops so that the glued loop is K1-trivial;
   - shows that a null-homotopy of the glued loop would lift, by a relative lifting argument on the
     square, to a path from 1 to `v` in `U(B)`.
   Graph node: `nonprime-minimal-lxi-counterexample-yields-loop-witness`, with direct proof route `-proof`.
4. **Corollary 5.** LXI holds iff both of the following hold:
   - (P) `prime-quotient-minimal-k1-trivial-unitaries-are-null`;
   - (L) `properly-infinite-unitary-loops-detected-by-k1-suspension`.
   Routes: `stw99-lxi-from-prime-case-and-loop-detection` (root from P, L and the Theorem 3 claim);
   `prime-minimal-unitaries-null-from-lxi`; `unitary-loop-detection-from-lxi`.
5. **Proposition 6.** (L) for `D` is equivalent to injectivity of `pi_1 U(D) -> pi_1 U(M_2(D))`. The proof
   applies BRR Lemma 2.4(ii) in `M_2(C(T, D))`. So (L) is the loop analogue of BRR Proposition 5.2(ii).
6. **Remark 5.2.** Assume the halving hypothesis (c): properly infinite algebras with `[1] = 0` are
   K1-injective. Then for any quotient-minimal quotient of Blanchard's `T_2 * T_2` witness, the two Toeplitz
   defect ideals intersect nontrivially, and `[1_D] ≠ 0` for every `D` produced by Theorem 3.

Honest assessment. The reduction is an equivalence, and neither (P) nor (L) is currently known to be easier
than LXI. Its value is structural: a counterexample must live either in a prime algebra or in the
fundamental group of a unitary group. Also, (L) contains the analogue of LXI with `pi_0` replaced by `pi_1`,
and that analogue may be a better target for a counterexample.

## 3. Approaches tried and where each one dies

- **Survival in `A * O_2`.** A witness of `A` should survive in `A *_C O_2`, where `[1] = 0`, so that the
  halving hypothesis would bite. There is no retraction `A * O_2 -> A`, so non-nullness does not transfer.
  This is the survival problem already recorded in `trivial-unit-class-lxi-iff-universal-halving-homotopy`.
- **Corner ascent.** Pick a properly infinite full projection `p` with `[p] = 0` (Cuntz) and try to move a
  K1-trivial unitary into `pAp + (1-p)`. That needs to move subprojections along homotopies. Once `u`
  almost commutes with such a `p` (with properly infinite full complement), BRR Lemma 2.4(ii) already makes
  `u` null, with no halving input needed. So "LXI iff (c) and corner ascent" is essentially a restatement.
  It was not promoted.
- **Isometry-conjugation calculus.** For an isometry `t` put `phi_t[u] = [t u t^* + 1 - t t^*]` on
  `G = U(A)/U_0(A)`. Checked:
  - `phi_t phi_{t'} = phi_{t t'}` and `phi_{W t} = Ad_{[W]} phi_t`;
  - `phi_{s_1} = phi_{s_2}`, via the self-adjoint unitary `W = s_2 s_1^* + s_1 s_2^* + (1 - s_1 s_1^* - s_2 s_2^*)`,
    which lies in `U_0`;
  - `phi(G)` is abelian.
  Concluding that `G` itself is abelian, or trivial on K1-trivial classes, needs the unit axiom
  `phi_s = id`, which is the open halving homotopy. Dead end.
- **Prime case.** Primeness constrains the ideal lattice but gives no handle on path components. The gluing
  of Theorem 3 in a prime algebra only yields a path modulo `J_1 ∩ J_2 ≠ 0`, which quotient-minimality
  already gives. Simple `B` are included, so (P) contains K1-injectivity of all simple properly infinite
  algebras. That is known for purely infinite simple algebras (Cuntz) and for Z-stable ones (Jiang), but not
  for general simple properly infinite algebras, such as corners of Rordam's algebra with a finite and an
  infinite projection.
  Correction to an earlier working note of this lane: "simple B satisfies (P) by Cuntz" is wrong as stated;
  simple properly infinite algebras need not be purely infinite.
- **Iterating Theorem 3.** `C(T, D)` always has the nontrivial center `C(T)`, so it is never prime. Applying
  Proposition 1 to it again gives no control over primeness.
- **Loop halving.** Transporting the halving homotopy to loops gives a statement no easier than the unitary
  one.
- **Delooping.** There is no C\*-algebraic delooping that turns loops in `U(D)` into unitaries of a properly
  infinite algebra, other than `C(T, D)`. That returns the unitary problem.
- **Vacuity check caught during the work.** "`C(T, D)` is K1-injective for all properly infinite `D`" is
  trivially equivalent to LXI, because `D` is a retract of `C(T, D)`. That is why the reduction uses the loop
  statement (L), which is genuinely weaker than K1-injectivity of `C(T, D)`, instead of that formulation.
- **Homotopy domination and converse gluing.** No candidate was found for dominating a witness by a
  pullback of K1-injective algebras. The converse of the pullback gluing, "undetected loops give
  non-prime witnesses", was not attempted beyond Corollary 4.
- **Toeplitz defect ideal.** The existing one-ideal form (`toeplitz-defect-ideal-unitization-k1-injective`)
  was read and not advanced. Remark 5.2 of the artifact only adds that, under (c), the two defect ideals
  intersect nontrivially in any quotient-minimal quotient.

## 4. Known partial cases of the new holes

- (L) holds for `D` whenever `C(T, D)` is K1-injective. That includes:
  - Z-stable `D`, via the node `z-stable-unital-algebras-are-k1-bijective`;
  - purely infinite simple `D`, via Rohde's thesis, Theorem 5.2.11, for continuous `C(X)`-algebras with
    purely infinite simple fibres over finite-dimensional `X`, applied with `X = T`. Its BRR inputs were not
    rechecked.
- (P) holds for purely infinite simple and for Z-stable simple `B`. For separable prime quotient-minimal
  witnesses, no nonzero ideal is purely infinite simple. This uses the unital-or-stable dichotomy for
  separable purely infinite simple algebras, which is used in Rohde's proof of Proposition 5.2.9 and not
  rechecked here.

## 5. Weakest steps for a referee

1. Theorem 3, Step 5, the relative lifting: surjectivity of `Phi` onto the pullback algebra `P`, and the
   straight-line homotopy to the radial retraction.
2. Theorem 3, Steps 2--3, the bookkeeping: naturality and signs of `kappa`, and the use of Bott periodicity
   `K_0(E) ≅ K_1(SE)` (RLL Chapter 11, theorem number not rechecked) together with BRR Proposition 2.3(ii).

## 6. Literature consulted (checked 2026-09-16)

- Blanchard--Rohde--Rordam, arXiv:0704.1554v1 (12 Apr 2007), read in full text: Proposition 2.3,
  Lemma 2.4 (wording of (ii) rechecked this session), Proposition 2.7, Proposition 5.2 and Theorem 5.5.
- E. Blanchard, arXiv:0804.4624v13: Proposition 4.2 and Remarks 4.7(i), rechecked in the text this session.
- R. Rohde, *K1-injectivity of C\*-algebras*, PhD thesis, IMADA, University of Southern Denmark, March 2009
  (referee correction; the lane originally wrote "Copenhagen"), full text: Theorem 3.1.3,
  Lemmas 5.1.6--5.1.9, 5.2.2, 5.2.3, Proposition 5.2.9 and Theorem 5.2.11.
- Schafhauser--Tikuisis--White, arXiv:2506.10902v2 (2026-05-08): LXI still listed as open.
- arXiv API search `abs:"K_1-injective"`, newest first, run 2026-09-16. Ten hits; none resolves LXI.
  - A. S. Toms, arXiv:2609.09535v1 (2026-09-08): a simple unital non-K1-injective algebra. That is Problem
    LIX, in the finite setting.
  - G. Szabó, arXiv:2601.23029v2 (2026-01-30): K1-injectivity of Paschke dual algebras. It is used for a KK
    uniqueness theorem and is not a general properly infinite result.
- E. Blanchard, arXiv:1606.04773v1: not reread; its covariance defect is recorded in the root's firewall.
- Rordam--Larsen--Laustsen, CUP 2000, Chapters 11--12: standard background, theorem numbers not rechecked.
- M. Rordam, Acta Math. 191 (2003), a simple algebra with a finite and an infinite projection: cited from
  BRR's bibliography, not read. (The referee has since read it; see below.)

## Referee (2026-09-16)

**Checked.**
- Every listed file was read, together with the nodes they reference: the root,
  `brr-commutator-criterion-null-unitary` and its citation route,
  `stw74-simple-infinite-projections-are-properly-infinite`,
  `k1-injectivity-extends-over-properly-infinite-quotients`, `z-stable-unital-algebras-are-k1-bijective`,
  `trivial-unit-class-lxi-iff-universal-halving-homotopy` and its artifact, and
  `rordam-mixed-examples-not-real-rank-zero`. No unlisted solver files were found.
- The mathematics was checked line by line:
  - Propositions 1 and 2 (Zorn over ideals not killing `u`; pushing `v` into `J~` by F1 plus the exponential
    map in the properly infinite setting).
  - Theorem 3, all steps. That covers the pullback (F6); the Bott correction; the relative lifting on the
    square, including surjectivity of `Phi` onto `P = {(f, g) : f|_Y = pi_1 g}` (lift `g ∘ r`, then correct by a lift
    in `C_0(X \ Y, B_1)`); the radial retraction from `(1/2, 2)` and the straight-line homotopy to it; the
    use of (F1) to lift `W_0 W_1^*`; and the contradiction.
  - Corollaries 4--5, Proposition 6, and the three routes, including the converse routes. Their cycle through
    the root has precedent in the graph.
- Sources were fetched and read: BRR arXiv:0704.1554 (Proposition 2.3(ii), Lemma 2.4(ii), Theorem 5.5);
  Rohde's thesis (institution, and Lemmas 5.1.6--5.1.8); Rordam arXiv:math/0204339v2 (Proposition 2.1,
  Corollaries 7.1--7.2).
- Duplicate search (`bin/cairn search --similar`) found no existing node with the same content as the three
  new claims. All ids are within the length cap, and both new holes carry `## Attempts`.

**Changed.**
1. The thesis institution was wrong. Rohde's thesis is from IMADA, University of Southern Denmark (Odense),
   March 2009, supervised by M. Rordam; the title page of the PDF on Rordam's students page confirms this.
   Corrected in the artifact, the (L) node and these notes.
2. The Rordam Acta citation was "not read". It has now been read, and Corollary 7.1 confirms the claim
   used. Upgraded in the artifact and the (P) node.
3. Theorem 3 step 3 relied on Bott periodicity with an unrechecked theorem number. Added (F5') to the
   artifact: a self-contained proof that every class of `K_1(SE)` is `kappa_E` of a based loop in `U(E)`
   for unital properly infinite `E`, without Bott periodicity. The proof route now notes this.
4. Added a novelty hedge to the artifact's sources. Theorem 3 is a Mayer--Vietoris-type pullback argument,
   and a version of it may exist elsewhere.

**Not fixed (non-load-bearing).** The BRR inputs to Rohde's Theorem 5.2.11 are still not rechecked. That
theorem appears only in `## Attempts` and remarks, as a known partial case. The attribution of the
unital-or-stable dichotomy to Zhang is also not rechecked, and is flagged as such.

**Verdict.** Landed with fixes. The established content is claim
`nonprime-minimal-lxi-counterexample-yields-loop-witness`, by direct proof, together with the equivalence
routes LXI ⇔ (P) ∧ (L). (P), (L) and LXI itself remain open. As the lane itself says, the reduction is
structural: neither (P) nor (L) is known to be easier than LXI.
