# EX review, analysis lanes, part 7 (2026-09-13)

Lane `ex-verify-analysis`. Verdict legend as in `ex-review-analysis-2026-09-12.md` §0. Main tip at
review time: `1bd095f87`.

## 1.14 ex-quantum-pcp: stabilizer rounding of Pauli and code Hamiltonians

These claims constrain constructions and do not decide `quantum-pcp-constant-gap-local-hamiltonian`,
which is OPEN. None of its routes has all its required claims established (part 2, §2).

### `pauli-sums-near-their-one-norm-round-to-stabilizer-states` (b4a31b6ec9): PASS

Re-derived.
- **Commuting good set.** Anticommuting signed Paulis satisfy (A_P + A_Q)² = 2I, so
  ⟨A_P⟩ + ⟨A_Q⟩ ≤ √2. So G = {δ < 1 − 1/√2} pairwise commutes.
- **Pattern.** The joint measurement determines the outcomes x_P on G* = ±A, with E x_P = 1 − δ_P, so
  some outcome pattern with positive probability has Σ_{G*} w(1 − x) ≤ Σ_{G*} wδ.
- **Averaging.** Take P ∉ G*.
  - If P anticommutes with a member of A, then ⟨P⟩ = 0 on S_x.
  - Otherwise P is a nonzero class of the nondegenerate symplectic space C(A)/A, so some R ∈ C(A)
    anticommutes with P. Conjugation by R permutes S_x and flips ⟨P⟩, so the average is 0.
- **Loss.** Outside G, δ ≥ 1 − 1/√2 = 1/(2 + √2), which is exactly the condition for
  max{0, 1 − δ} ≤ (1 + √2)δ. So the loss is ≤ (1 + √2)F.
- **Lower example.** (X + Z)/2 has λ_max = 1/√2, while stabilizer states have ⟨X⟩ + ⟨Z⟩ ≤ 1. The ratio
  is (√2 − 1)/2 ÷ (√2 − 1)/√2 = 1/√2.
- **Model test.** The MSI run (7500 instances, n ≤ 3, exhaustive) is recorded in an artifact and was
  not rerun.

### `pauli-projector-hamiltonians-are-stabilizer-approximable` (32cc9569fb, b4a31b6ec9): PASS

- H = (WI − K)/2, so (SR) gives ⟨H⟩ ≤ (2 + √2)λ_min.
- **Code projectors.** Π = 2^{-r} Σ_S g_S is a distinct-Pauli decomposition of weight one, so
  H = WI − K and the same bound holds.
- **Mixed terms.** H_s ≤ H, and ⟨H − H_s⟩ ≤ V.
- **NP verifier.** The stabilizer tableau energy is an exact rational (Aaronson--Gottesman), and
  large code projectors are evaluated by group intersection.
- **Example.** (I − X)/2 + (I − Z)/2 gives ratio 1 + 1/√2.

### `pauli-norm-games-qpcp-needs-imperfect-completeness` (c06c96f721): PASS, conditional on the cited lemma

- The energy test accepts with probability Σ_P (|β_P|/W)(1 + s_P⟨P⟩)/2 = 1/2 + tr(Hρ)/(2W). So the
  acceptance errors are Pauli frustrations F = 2Wε, and (GT1) is the Pauli-sum clause above.
- ε_c = 0 forces a common +1 eigenvector, hence pairwise commutation, which is decidable over F_2.
- **(GT2), NP side.** (SR) with weight ≤ 1.
- **(GT2), gap.** (1 − x/r − e^{−x})/3 at x = ln r equals (1 − (1 + ln r)/r)/3, and ln r < r − 1.
- **Trust surface.** Lemma 6 and Section 4.2 of arXiv:2403.13084v1, through
  `natarajan-vidick-games-pcp-amplification-error`.

### `qudit-stabilizer-rounding-for-code-constraint-hamiltonians` (cd0f02cfd0): PASS

Re-derived.
- **Commutation bound.**
  - ||uψ − ψ||² = 2δ for a unitary u.
  - (u_j u_k − u_k u_j)ψ has norm |1 − ω^m|.
  - The triangle inequality bounds that norm by 2(√(2δ_j) + √(2δ_k)).
  - |1 − ω^m| ≥ 2 sin(π/d), so both δ < sin²(π/d)/8 is impossible.
- **Averaging.** Prime d gives maximal stabilizer extensions. A centralizer Weyl operator R with
  R u_j = ω^m u_j R, m ≠ 0, permutes S_x, so E⟨u_j⟩ = ω^m E⟨u_j⟩ = 0.
- **Loss.** For δ ≥ τ, max{0, 1 − δ} ≤ ((1 − τ)/τ)δ, with (1 − τ)/τ = 8/sin²(π/d) − 1.
- **(CC_d).** Weight-one code projectors give the factor 8/sin²(π/d).
- **Model test.** The MSI qutrit run is recorded as an artifact and was not rerun.

## 1.15 ex-mf-kazhdan-cstar: invariant-vector obstructions to MF reduced algebras

The root `infinite-kazhdan-group-with-mf-reduced-cstar` stays OPEN. Its new routes require the OPEN
`sl3z-purely-matricial-field` and `cubic-division-lattice-purely-matricial-field`. The claims
`sl4z-matricially-stable` and `sl4z-reduced-cstar-is-not-mf` are also OPEN.

### `sl4z-representations-have-sl2-invariant-vectors` (6ad8fffd39): PASS as an import

- The citation route quotes Magee--de la Salle arXiv:2312.03220v2, Theorem 1.1 and Corollary 1.3,
  verbatim, with the page of the proof of Corollary 1.3.
- The overgroup remark is correct: restriction keeps representations finite-dimensional, and λ_Γ
  restricted to SL_2(Z) is a multiple of λ_{SL_2(Z)}.

### `matricially-stable-overgroups-of-sl4z-are-not-reduced-mf` (6ad8fffd39): PASS

Re-derived.
- **Lift.** The polar parts of the lifts of ι(λ(g)) form an asymptotic homomorphism.
- **Correct.** Matricial stability gives genuine π_n with the same corona image. Since ι is isometric,
  limsup_n ||π_n(z)|| = ||λ_Γ(z)||.
- **Fixed vector.** For z = S + S^{-1} + T + T^{-1}, every finite-dimensional π_n has an SL_2(Z)-fixed
  vector, so ||π_n(z)|| = 4. But ||λ_Γ(z)|| = ||λ_{SL_2(Z)}(z)|| < 4 by Kesten, since S and T generate the
  nonamenable SL_2(Z).
- There are infinitely many n with k_n ≥ 1, because ι is injective.
- The claim is correctly conditional on point-norm matricial stability, and the weak form is
  correctly excluded.

### `deligne-sl3-representations-have-principal-sl2-invariants` (25684228b2): PASS

Re-derived the character count, with |Ω_q| = |PSL_2(F_q)| = q(q² − 1)/2.
- **h = 1** contributes the degree (q − 1)(q² − 1).
- **Unipotents.** The q² − 1 nontrivial unipotents of SL_2 give q² − 1 elements of Ω. Sym² makes each
  one regular unipotent in GL_3, and Green's formula gives the character value 1 at the class (3).
  The same formula gives 1 − q at transvections and the degree at 1, matching MdlS Example 2.2.
- **Remaining classes.** Sym²(−u) = Sym²(u) is already counted. Every other h has eigenvalues
  (a², 1, a^{-2}) with a ≠ ±1, so it is conjugate to a block element with (g' − 1)² ≠ 0 (including
  a² = −1, giving −I_2), where the trace is 0.
- **Sum.** (q − 1)(q² − 1) + (q² − 1) = q(q² − 1), divided by q(q² − 1)/2, gives dim π^Ω = 2.
- **Norm step.** The fixed vectors give eigenvalue 4, and PSL_2(Z) is nonamenable.
- **Trust surfaces.** Green's formula for cuspidal characters, and MdlS Example 2.2's vanishing at
  block elements.

### `sl3z-has-no-invariant-vector-witnesses` (25684228b2, 73d2907e3b): PASS, conditional on its imports

- Replace each H_j by a free F_j (Tits). The simple parts of its Zariski closure are SL_3, a block A_1
  or SO_3.
- **(a)** Strong approximation gives the whole SL_3(F_p).
- **(b)** Conjugated Deligne representations miss the block.
- **(c)** For p ≥ 5 there are odd η ≠ sgn. Such an η is nontrivial on the squares, since a character
  trivial on squares is 1 or sgn, and nontrivial at −1. So the degenerate principal series has no
  Ω-fixed vector on any of the three orbits.
- **Tensor product.** The primes are distinct, so the simple quotients (PSL_2(F_p), PSL_3(F_p)) are
  pairwise non-isomorphic. Goursat makes the perfect core of the image the full product, so
  π^{F_j} ⊆ ⊗_i π_i^{N_i} = 0. Tensors of irreducibles across the factors stay irreducible, and CRT
  surjectivity pulls them back to SL_3(Z).
- **Trust surfaces.**
  - strong approximation (Matthews--Vaserstein--Weisfeiler, Nori);
  - the orbit-stabilizer character computations of the artifact's Lemmas 2 and 2', which I checked only
    at the level above;
  - the MSI census.
- The claim correctly says it does not decide `sl3z-purely-matricial-field`.

### `cubic-division-lattice-subgroups-are-zariski-dense` (25684228b2): PASS

Re-derived.
- **Setup.** A non-solvable Zariski closure contains a Q-simple S. Over Q̄ it is SL_3, a block SL_2 or
  SO_3.
- **Block SL_2.** Its centralizer torus {diag(t, t, t^{-2})} is unique, hence defined over Q. Its Q̄-span
  {diag(x, x, y)} descends to a 2-dimensional commutative subalgebra of D, which must be a quadratic
  subfield. A degree-3 division algebra has none.
- **SO_3.** By Schur the invariant symmetric form is unique up to scalar, so the adjoint involution is
  Galois-stable. It descends to an involution of the first kind, so exp(D) ≤ 2. But period equals
  index (3) over number fields.
- **Setting.** Imported: Γ_D cocompact (Godement), with property (T) (Kazhdan), and strong approximation
  for the consequence.
