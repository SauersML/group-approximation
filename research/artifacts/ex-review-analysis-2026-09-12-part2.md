# EX review, analysis lanes, part 2: Baum--Connes module route and Blackadar--Kirchberg structure (2026-09-12)

Lane `ex-verify-analysis`. Verdict legend as in `ex-review-analysis-2026-09-12.md` §0. Main tip at
review time: `cfdab43f5`.

## 1.3 ex-baum-connes: the module K-inexactness route

### `k-inexact-module-triple-refutes-trivial-coefficient-bc` (acc5d83c1b): PASS

Priority (2). This is the reduction that the family on
`some-nonexact-group-has-a-k-inexact-module-triple` builds on. I re-derived it.

- **Algebras.** W is abelian, hence amenable, so `C*_r(V ⋊ G) -> C*_r((V/W) ⋊ G)` exists. Under
  Fourier transform it is `res ⋊_r G` with kernel ideal `C_0(U) ⋊_r G`. The composite
  `q ∘ (i ⋊ G)` is 0, so im ⊆ ker always holds, and "not exact" means ker ⊋ im.
- **Transfer.** Chabert--Echterhoff Corollary 3.5 applies with N = V, respectively V/W, amenable and
  G/N = G discrete, since the preimages of finite subgroups are finite extensions of N, hence
  amenable. So BCS for V ⋊ G is equivalent to BCS for G with coefficients `C(X)`, and BCI for
  (V/W) ⋊ G to BCI for G with `C(Z)`.
  - The degree-wise reading uses the commutative diagram of their Proposition 3.2, which the
    citation marks "not re-read". It is standard, and the conclusion "some group fails BC with
    trivial coefficients" does not need the degree.
- **Chase.** Take `x` in ker q_*.
  1. x = μ_X(y), by surjectivity.
  2. μ_Z(res_* y) = q_* x = 0, by naturality in the coefficients.
  3. res_* y = 0, by injectivity.
  4. y = i_* z, by half-exactness of K^top_*(G; ·), quoted verbatim from their §4.
  5. x = (i ⋊ G)_* μ_U(z), by naturality.
- **Model tests.** Both are right: W = V is exact by Ozawa's Lemma A.1, and exact G by
  Kirchberg--Wassermann.
- **Citation route.** Theorem 3.3, Corollary 3.5 and the §4 passages are quoted verbatim with
  numbers.

### `reduced-group-algebras-contain-no-nonzero-ghosts` (996c78f231): PASS

Re-derived. An element of `M_n(C*_r G)` has entries `⟨T(e_i⊗δ_h), e_j⊗δ_g⟩` that depend only on
`gh^{-1}`. For infinite G each value is attained off every F × F, so a ghost has all entries 0. As
an invalidator, this node correctly kills `bc-counterexample-via-ghost-projection`, and its proof
route has `requires: []`.

### `module-dual-actions-have-no-wandering-open-sets` (dd95bf500c): PASS

Re-derived.
- A continuous automorphism of a compact group preserves normalized Haar measure, by uniqueness.
- A nonempty open set has positive measure.
- N > 1/m(B) translates chosen outside F·F^{-1} must meet pairwise somewhere, so returns are
  infinite, and the open invariant part is never proper.
- The Haar trace is faithful because E is faithful and m has full support. It equals the canonical
  trace of `C*_r(V ⋊ G)`.

### `split-quotients-give-exact-reduced-crossed-products` (dd95bf500c): PASS on (A)--(C) and (D)1; (D)2 read in part

- **(A)** An equivariant cp splitting acts entrywise on the finite compressions. It gives a cp
  contraction of reduced crossed products, and `x − (ψ⋊G)(q⋊G)x_n` has coefficients in I.
- **(B)** Representations of `C*_r(Γ)/J` are σ∘q with σ ≺ ... The chain is
  σ ≺ σ ⊗ λ_{Γ'/S'} ≅ Ind Res σ ≺ Ind(∞·λ_{S'}) = ∞·λ_{Γ'}. It uses Eymard co-amenability and Fell
  continuity of induction.
- **(C)** Case 2: q(ker(G → Aut(V/W))) has finite index in Γ', hence is co-amenable.
- **(D)1** ψ(e) is H-invariant, and H acts topologically transitively on μ_p^G because it is
  infinite. So ψ(e) is constant, while its restriction to Z is not.
- **(D)2** was read only to its lemma on invariant means. It is not used by any established node.

### `window-defect-forces-module-triple-inexactness` (dd95bf500c): PASS

Re-derived.
- **Step 1.** The π_ζ with ζ ∈ Z form a faithful family. Their uniform spectral gap bounds the
  resolvent of ⊕π_ζ(qD) on (−ε, ε), so f(qD) = 0.
- **Step 2.** A polynomial approximation turns (H2)(a) into ||π_{ξ_n}(f(D))η_n − η_n|| → 0.
- **Step 3.** Ideal elements act on η_n through the values b_g(k^{-1}ξ_n) with k ∈ S_n R_n. These
  tend to 0 by (H2)(b), continuity and compactness.
- **Step 4.** The distance to the ideal is ≥ 1.
- The real-object model test is recorded as context and was not imported.

## 1.4 ex-blackadar-kirchberg: spectral structure of a counterexample

Imports used, with the verbatim quotes checked in their citation routes against the numbers given:
- Brown--Dadarlat arXiv:math/0008182, Propositions 2.5, 4.1, 4.2 and 4.6;
- Gabe arXiv:1804.08095v2, Theorem A and Corollaries B, D and E, plus Corollary C through
  `gabe-traceless-exact-qd-af-embedding`;
- TWW/Gabe/Schafhauser through `tww-gabe-schafhauser-af-embedding-theorem`.

I did not re-read these sources.

### `stw07-separating-qd-quotients-force-quasidiagonality` (1283a1a764): PASS

- **Main statement.** Use Voiculescu's local characterisation. Choose finitely many quotients that
  recover the norm on F, and take the direct sum of their approximately multiplicative models.
- **Radical.** It is the main statement applied to all quasidiagonal quotients.
- **C(X)-algebras.** By Schur, irreducible representations factor through fibres.
- **Asymmetry examples.** The cone over O_2, and C([0,1], O_2) as a sum of two cones. Both are
  correct.

### `bk-no-compact-open-ideals-are-qd-invisible` (a9803215dd): PASS

Re-derived.
- Gabe Theorem A embeds I into C_0((0,1], O_2). Its hereditary hull J is approximately unital,
  quasidiagonal and full in J' = C_0(U) ⊗ O_2.
- Push forward along id_K ⊗ ρ. For nuclear separable B, Kasparov's theorem gives
  Ext(K⊗K⊗B, K⊗K⊗J) ≅ KK^1(B, J).
- Brown's stable isomorphism gives KK^1(B, J') = 0, since O_2 is KK-contractible.
- BD Proposition 2.5 then applies: J is σ-unital, and B is separable, nuclear and quasidiagonal. So
  E(η) is quasidiagonal, and E embeds in it.
- **Lemma 1** holds. Compact open sets of an extension's spectrum meet the quotient in compact open
  sets, and compact sets in a chain lie in one member.
- **Consequence 3**, the gluing reduction, is correct: C([0,1], B) and its two cone-like ideals.
- **Consequence 4**'s aside "outside Brown--Dadarlat Theorem 3.4" was not checked. It is a remark,
  not a claim.

### `bk-primitive-quotients-qd-or-traceless-force-qd` (8dbc69d167): PASS

Re-derived.
- **(1)** A finite nonzero value gives a hereditary B with a bounded trace. An extreme tracial state
  is factorial, so its kernel is prime, hence primitive in the separable case. So it lives on some
  E/P' with P' ∈ V, and extends to a nontrivial lower semicontinuous trace there, against
  tracelessness.
  - Wording note: the natural extension from an ideal is the supremum over an approximate unit.
    "Extending by ∞ off the ideal" need not be lower semicontinuous, but the conclusion is the same.
- **(2)** Gabe's Corollary C, (iii) ⟹ (iv), for the separable exact traceless stably finite ideal E_V.
- **(3)** F∖V has empty interior in Prim(E)∖V. So the quasidiagonal primitive ideals are dense
  there, their intersection in E/E_V is 0, and the separating-quotients theorem applies.
- **(4)** Theorem 1 glues E_V and E/E_V.
- **UCT case.** For T_1 spectra, primitive quotients are simple. A simple exact algebra is traceless
  or stably finite: Gabe's Corollary C applies because a point is compact open, and a faithful
  densely finite trace forces stable finiteness. The stably finite UCT ones are quasidiagonal by
  TWW on a full hereditary subalgebra with a bounded trace, using stable isomorphism invariance.

### `stw07-qd-radical-criterion-compact-open` (d502e4d3be): PASS

- Theorem 1 applied to R_qd(E) gives the criterion.
- The compact ideal K with Prim K = W is compact in the ideal lattice of E, by distributivity.
- K is not traceless, else Gabe's Corollary C would make W compact-free.
- For E = (A⊗K)~ the quotient is C, so R_qd ⊆ A⊗K.

### `bk-counterexample-trichotomy-via-qd-radical` (e641978298): PASS, conditional on two earlier imports

- The three cases R = E, R proper and not quasidiagonal, and R quasidiagonal are exhaustive and
  exclusive.
- **Case 3.**
  - BD Proposition 2.5 forces [γ^s] ≠ 0, and every push-forward along an approximately unital
    quasidiagonal embedding is nonzero too.
  - KK-contractible R is excluded, and so is R ≅ R⊗W, since W ~_KK 0.
  - A compact-free spectrum is excluded by Theorem 1.
  - The UCT split uses Moutzouris Remark 2.5 and BD Theorem 4.11 through the pre-existing
    `brown-dadarlat-qd-extensions-and-k0-hahn-banach`. I did not re-read that import.

### Wiring for the simple case: PASS

`bk-t1-spectrum-from-simple-case` and `stw99-vii-simple-from-t1-case` form an equivalence cycle.
Its two ends, `bk-t1-primitive-spectrum-case` and `stw99-vii-restricted-to-simple-algebras`, are OPEN,
and the latter's other route requires the OPEN IX.1. So nothing fires, and Problem VII stays OPEN.
