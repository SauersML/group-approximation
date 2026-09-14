# sk-verify-14, part 6: review of the permanence firewalls and exactly modelled full groups (sk-fp-sofic-host, sk-sofic-host-hamming) (2026-09-13)

Lane sk-verify-14, queue `sk/queue/sk-verify-13.txt`, lines 18, 19, 20, 31.
- **Targets:** `research/artifacts/sk-fp-sofic-host-status-2026-09-13.md` and `research/artifacts/sk-sofic-host-hamming-2026-09-13-part1.md`, with their nodes.
- **Method:** every step re-derived by hand. No other review was on main when I started.

## 0. Verdicts

| claim or route | verdict |
|---|---|
| `lea-permanence-closure-fp-kazhdan-groups-are-residually-finite` (+ `lea-permanence-closure-fp-kazhdan-rf-proof`) | **PASS** |
| routes `fp-sofic-kazhdan-non-rf-via-deligne-triple-cover`, `-via-km-246-lattice`, `-via-fp-simple-ring` | **PASS**, as one-step implications |
| `kazhdan-groups-in-sofic-permanence-closure-are-lef` (Theorem K) | **PASS** |
| `exactly-modelled-orbit-full-groups-have-lef-subgroups` (Lemma E) | **PASS** (instance 3 checked in outline) |

## 1. The finitely presented firewall (line 18)
- **Base case, all factors LEA.**
  - Finite products and subgroups of LEA groups are LEA.
  - For K = ⟨S | R⟩ and g ≠ e, let F be the set of prefixes of the words for g and for the relators. A local embedding φ: F → A into an amenable group has φ(e) = e, and the prefix induction gives a homomorphism ψ: K → A with ψ(g) = φ(g) ≠ e.
  - ψ(K) is amenable and Kazhdan, hence finite. So K is residually finite.
- **Induction on (α,k)**, lexicographic: α the largest rank in the family, k the number of factors of that rank.
  - **(P1):** replace G_1 by a lower-rank H ⊇ G_1.
  - **(P2):** π_1(K) is finitely generated, so it lies in one H_i.
  - **(P3):** the image of K in G_1/N is amenable and Kazhdan, so finite. K_0 = K ∩ (N × ⋯) has finite index, so it is finitely presented with (T), and residual finiteness passes up from finite index.
  - **(P4):** FA fixes a vertex of the Bass–Serre tree, so π_1(K) lies in a conjugate of a vertex group.
  - **(P5):** split G_1 into its factors.
  - In each case the new factors have rank < α, so α drops or k drops. The number of factors may grow, but it is not part of the invariant.
- **Ranks.** At limit ordinals the rank is the union, so every rank is 0 or a successor. The union is closed under the operations, because each operation uses a set of members of bounded rank.
- **Sharpness.**
  - Deligne's triple cover E_3 of Sp_4(Z) is a finite-central extension of the residually finite group Sp_4(Z).
  - It is finitely presented and Kazhdan, and not residually finite by `deligne-covers-of-sp2g-z-have-finite-residual-2z`.
  - So the claim really fails once finite-central extensions are allowed.
- **Model test.** The Kar–Nikolov amalgam SL_n(Z[1/p]) *_Z SL_n(Z[1/p]) is in 𝒫 by (P4), finitely presented and not residually finite. It fails FA, so it has no (T), as the claim requires.

## 2. The three routes into Open problem 6.1 (line 19)
Each route checks finite presentation, (T) and non-residual-finiteness of its witness, and leaves soficity as the open required claim.
- **Deligne.**
  - Sp_4(Z) is finitely presented, and a finite extension of a finitely presented group is finitely presented.
  - Sp_4(Z) is a lattice in a simple Lie group of real rank 2, so it has (T), and a finite extension keeps (T).
  - Res_fin(E_3) = C_3 ≠ 1 comes from the required node.
- **Kac–Moody.** S_q is finitely presented, infinite, simple and Kazhdan by the required node. An infinite simple group has no nontrivial finite quotients.
- **Simple ring.** S = EL_n(R)/Z is finitely presented, simple and sofic by the required claim.
  - S is infinite, since e_12(R) ∩ Z = 1 (e_12(r) is central only for r = 0) and R is infinite.
  - S has (T) as a quotient of EL_n(R), which is Kazhdan by Ershov–Jaikin-Zapirain because R is finitely generated.

## 3. Theorem K (line 20)
- **α = 0.** A finitely generated Kazhdan subgroup of an amenable group is finite, and subgroups of LEF groups are LEF.
- **(O1), (O2).** As in §1.
- **(O3).** Each projection p_i(G) is a finitely generated Kazhdan quotient of G inside H_i, so it is LEF by induction, and G ≤ ∏p_i(G) is LEF.
- **(O4).**
  - G/(G∩N) ↪ H/N is amenable and Kazhdan, so finite, and G∩N is a finitely generated Kazhdan subgroup of N, so LEF.
  - **Finite extensions of LEF groups are LEF.** G ↪ K ≀ (G/K) (Kaloujnine–Krasner). A ball of K≀Q has coordinates in a bounded ball of K, and applying a partial embedding φ coordinatewise commutes with permuting coordinates. So it gives a partial embedding into F ≀ Q.
- **(O5).** FA puts G in a conjugate of a vertex group, which is isomorphic to a member.
- **(O6).**
  - G_k = ⟨w_i(S_k)⟩ converges to (G,(w_i)), since balls of G in the marking (w_i) are read from balls of H of bounded radius.
  - By openness of (T) (Shalom; `fpbs-shalom-property-t-is-open`, checked at source in part 1 of this review), G_k is Kazhdan for large k, so LEF by induction.
  - LEF is closed in the space of marked groups: a ball of the limit is a ball of some G_k.
- **Model test.** BS(2,3) is in 𝒫 by (O5) and is not LEF (finitely presented and not residually finite). This shows the Kazhdan hypothesis is necessary.
- **Consequences.** A finitely presented Kazhdan member is LEF, hence residually finite, which recovers §1. De Cornulier's groups and Deligne's lattice are finitely presented, Kazhdan and not residually finite, so they lie outside 𝒫. Hosts for non-LEF inputs lie outside 𝒫.

## 4. Lemma E (line 31; §4 of the sk-sofic-host-hamming artifact)
- **W_𝒜 is a group.** c_{gh}(x) = c_g(hx)c_h(x) has level sets {c_h = λ_2} ∩ λ_2^{−1}{c_g = λ_1} ∈ 𝒜, and inverses work the same way.
- **ĝ is a permutation.**
  - β is a unital Boolean homomorphism, so the sets β{c_g = λ} partition E.
  - g maps {c_g = λ} onto λ{c_g = λ}, so these images partition X. Equivariance on F·𝒜_0 then makes σ(λ)β{c_g=λ} = β(λ{c_g = λ}) a partition of E too.
- **Exact multiplicativity.**
  - For v ∈ β({c_h = λ_2} ∩ λ_2^{−1}{c_g = λ_1}): ĥv = σ(λ_2)v ∈ β{c_g = λ_1} by equivariance, so ĝĥv = σ(λ_1λ_2)v.
  - That set lies in {c_{gh} = λ_1λ_2}, so \widehat{gh}v agrees. The sets partition E.
  - σ(e) = id follows from exact multiplicativity.
- **Injectivity.**
  - For g ≠ 1 in B_{2r}, μ{c_g ≠ e} = μ{gx ≠ x} > 0.
  - |β{c_g ≠ e}| ≥ (μ{c_g ≠ e} − ε)|E|, and at most |F|ε|E| points are fixed by some σ(λ), λ ≠ e. So ĝ ≠ 1.
  - For g ≠ h in B_r, \widehat{h^{−1}g} = ĥ^{−1}ĝ ≠ 1.
- **Instance 1 (profinite actions).** The level-k cylinders are modelled exactly. The fixed-point fractions tend to μ(Fix λ) = 0 by essential freeness.
- **Instance 2 (Bernoulli shifts of LEF groups).**
  - β is the preimage under (c,q) ↦ (h ↦ c(qι(h)))|_{B_R}, so a Boolean homomorphism.
  - Equivariance follows from ι(λ)ι(h) = ι(λh) on the ball.
  - Counts are exactly |A|^{−|W|}, since h ↦ qι(h) is injective on W.
  - q ↦ qι(λ)^{−1} has no fixed points for λ ≠ e.
- **Instance 3 (dual actions of G_X), in outline.**
  - The bounded-degree covariance of the periodic ring models gives an injective linear map from a finite-dimensional space of characters that intertwines the actions exactly. So counts 2^{−dim} are exact.
  - The fixed-point fraction of σ(λ) is 2^{−rk(σ(λ)−I)}, which tends to 0 for λ ≠ e.
  - Not written out in full here.
- **Model tests.** BS(2,3) inside the full group of its Bernoulli shift shows that action has no exact models. Odometers have exact models and residually finite full groups.
