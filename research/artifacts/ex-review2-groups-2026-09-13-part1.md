# EX review, wave 2, part 1: the Kun--Thom wreath soft kernel (2026-09-13)

Lane `ex-verify2-groups`. Index: `ex-review2-groups-2026-09-13.md`. Read at tip `7d41d1a16`.
Sources: the four artifacts `research/artifacts/ex-q34-kt-wreath-soft-kernel-2026-09-13.md` and `-part2`, `-part3`,
`-part4` (landings 28dd802138, 41947938e3, 34e6a621ff, 59400bf9e1), and the nodes they feed.

## 1. Part 1 Lemma 2 and part 2 Lemma 6: deep congruence via Suslin: PASS

**Lemma 2 (finite orbit).**
- *(a)* `s.x_j = x^(s e_j)`, and the columns of `s` are positive, so `s(R_+) = F_q[y_1..y_d] <= R_+`, and
  `s Gamma s^(-1) = EL_r(S') <= Gamma`.
- *(b), the index.* `gamma s^(-1) h Gamma = s^(-1) h Gamma` iff `h^(-1)(s gamma s^(-1))h in Gamma`. So the index is
  `[EL_r(S') : EL_r(S') ∩ h Gamma h^(-1)]`.
- *(b), the ideal.* With `I = (y_j^2)`, each `y_j` has `x_1`-exponent `s_(1j) >= 1`, so `I <= x_1^2 R_+`. The
  monomials `x^(sa)` are distinct, so `S' ≅ F_q[y]` and `|S'/I| = q^(2^d)`.
- *(b), the conjugation.* I expanded `(1 - x_1^(-1)E_12) B (1 + x_1^(-1)E_12)` myself and got the artifact's
  expression. So `h^(-1)(1+B)h in SL_r(R_+)`.
- *(b), Suslin.* `SL_r(R_+) = E_r(R_+)`, for `r >= 3`, is Suslin's theorem, and the Izv. 41 (1977) 235--252 reference is
  the right paper. So the principal congruence kernel mod `I` lies in the stabilizer, and the orbit is finite.
- *(b), the fibre.* `c = (s^(-1)hs) s^(-1)Gamma` with `s^(-1)hs in N`, so `c` is in the fibre of `s^(-1)Gamma`.
  `O` avoids `s^(-1)Gamma`, since otherwise `h in Gamma`, which fails because `x_1^(-1) notin R_+`.
- *(c).* Parity-corrected `u` is `Gamma`-invariant and fibre-even.
- *(d).* Every `N`-orbit on `G/Gamma` is `N/gGammag^(-1)`, which is in bijection with `N/Gamma`. That is infinite,
  since `e_12(x_1^(-k))Gamma` are distinct because `x_1^(-l) - x_1^(-k) notin R_+`.

**Lemma 6.**
- *(a), finite index.* `Gamma(m^k)` has finite index in `Gamma`, so it is Kazhdan.
- *(a), compressors.* A nonnegative `t in SL_d(Z)` has nonzero columns, so `|ta| = Σ_j a_j Σ_i t_ij >= |a|`. Hence
  `t(m^k) <= m^k` and `t Gamma(m^k) t^(-1) <= Gamma(m^k)`. The compression semigroup contains `Gamma` and the
  elementary `e_ij(1)` of `SL_d(Z)`.
- *(a), generation.* Every `c in Z^d` is `t(mu e_1)`, by transitivity on primitive vectors, so
  `<Gamma, SL_d(Z)> ⊇ EL_r(R)`. So the semigroup generates `G`. That is Kun--Thom's definition of infranormal,
  checked verbatim (§5).
- *(a), normal closure.* It contains `e_ij(lambda x^a)` for `|a| >= k`, hence `e_ij(lambda x^c)` for all `c != 0`,
  using a primitive `p'` with `|p'| >= k`. `[e_il(lambda x^c), e_lj(x^(-c))] = e_ij(lambda)` gives the constants. So the
  normal closure is `N`.
- *(b).* `(sa)_j = Σ_l s_jl a_l >= |a| >= k`, so `s(B) in x^(k·1) M_r(R_+)`. With `k >= 2 max b_j`,
  `h_i^(-1) s(B) h_i in M_r(R_+)`. Determinant 1 and Suslin give `s(gamma) in h_i Gamma h_i^(-1)`, and
  `Lambda <= s(Gamma) <= Gamma` fixes `o`.

## 2. Part 2 Theorem M (the transport lemma) and Theorem 7: PASS

- **(HC), re-derived for block size `k`.** `||M - M'||_2^2 = 2 - 2 Re tr(M^* M')`, and
  `|tr(M^* M')| <= #{x : σx = σ'x}/n`. So `d_H <= ||.||_2^2/2`. Equality for `M' = (c; id)` gives `2 d_H(σ, id)`.
  So `pi_omega` is a homomorphism and soft elements are block-diagonal.
- **(COV).** For a monomial `(c; σ)` and a diagonal `f`, the phases cancel pointwise.
- **Theorem M.**
  - `b = rho(a)` is diagonal, and `psi(l).b = b` by (COV).
  - `λ` is a sofic representation of the sofic group `G` along `omega`.
  - `σ' = psi|G × λ` is a homomorphism, since Hamming defects add. Its traces multiply, so they vanish off `1`.
    That is Definition 2.1 of Kun--Thom.
  - Item 2 of `normal-closure-fixes-gamma-fixed-algebra` then gives `psi(n).b = b` for `n in <<Lambda>>_G`.
  - `f ↦ f ⊗ 1` is isometric, so nothing is lost in the tensoring.
- **The import's item 2 follows from item 1.** The kernel of `G` acting on `D^(σ(Gamma))` is a subgroup, normal
  because the algebra is `σ(G)`-invariant, and it contains `Gamma`. Item 1 is Kun--Thom 4.1 through doubling:
  - an invariant set `E` gives the swap on `E × {0,1}`, which centralizes the doubled `σ(Gamma)`;
  - its `σ(G)`-conjugates are then centralizing swaps, supported on `σ(g)E`.
- **Theorem 7.**
  - `f(h) = rho(e_Gamma + e_(hGamma))` takes values in the abelian `rho(K_even)`.
  - Lemma 6(b) with `h_1 = h'` gives `Lambda` fixing `o` and `h'Gamma`. So `a = e_Gamma + e_(h'Gamma)` centralizes
    `Lambda`, and Theorem M with `n = h` gives `rho(e_(hGamma) + e_(hh'Gamma)) = f(h')`.
  - So `f` is a homomorphism. `EL_r(R)` is perfect, so `f = 1`.
  - The fibre of `gGamma` is the `N`-orbit `{g n Gamma}`, because `gN = Ng`. Pairs span its even configurations,
    and `ker rho` is normal.
  - For the displayed equality, `W_N` is residually finite, and its permutation models are monomial.
- **Part 1 Theorem 3** is correct by the same steps, and superseded as the artifact says.

## 3. Part 3 Lemma 10, Theorem M_k and Theorem 9 (the bounded-block extension): PASS, one notation note

- **Single generation.** A countably generated abelian von Neumann algebra is singly generated, by Borel functional
  calculus on `C^*(x_i) ≅ C(K)`, `K` metrizable.
- **Diagonalization.** Kadison, Amer. J. Math. 106 (1984) 1451--1468, diagonalizes a normal element of `M_k(Z)` by
  a unitary of `M_k(Z)`. The statement matches; no theorem number is cited and I did not re-read one. `V` lifts
  to block-diagonal unitaries, so `V rho V^*` is block-monomial.
- **Atoms.** On `z_Π`, `C` is the functions constant on the blocks of `Π`.
  - One inclusion is clear.
  - For the other, the kernel projection of `rho(a) - rho(a)_(j_0) ⊗ 1` lies in `C`. The infimum over the
    countable `A` is the block of `j_0`.
- **Automorphisms.** `Ad rho(g)` preserves `C`, since `A` is normal, and acts by `psi(g)` on `Z`. Center-valued
  traces are preserved, so `β_g` is a rank-preserving bijection of blocks.
- **Cocycle.**
  - Pointwise, `β_(gg')(y) = β_g(psi(g')y) ∘ β_(g')(y)`, so `τ_(gg')(y) = τ_g(psi(g')y) ∘ τ_(g')(y)`. This is exactly what
    `σ~(g)(y,j) = (psi(g)y, τ_g(y)(j))` needs to be a homomorphism.
  - The finite-stage defects vanish along `omega`.
- **(ACOV).** Checked on block projections.
- **Theorem M_k.**
  - `θ(rho(a))` is `σ~(Lambda)`-fixed.
  - `σ~ × λ` is a sofic representation of `G`, and item 2 of the import applies.
  - `rho(nan^(-1)) in C`, because `A` is normal, and `θ` is injective.
- **Theorem 9.** `A = K_even` is abelian and normal, and soft by Lemma 1, so Theorem 7's proof runs verbatim.
- **Note.** The artifact writes the cocycle identity as `τ_(gg') = (psi(g').τ_g)·τ_(g')`. Under part 1's
  convention `σ.f = f ∘ σ^(-1)`, the correct left factor is `psi(g')^(-1).τ_g`. Nothing downstream uses the
  displayed form, since the lift is written pointwise. Sent to the owner lane.

## 4. Part 4 Theorem 12 (the Clifford cover): PASS

- **(SC).** `tr((X-t)^*(X-t)) = 1 - |t|^2`, and `tr(X ⊗ conj X) = |tr X|^2`. The second identity holds for any unitary
  on the whole space, with no block structure needed. So `X ⊗ conj X -> 1` forces `||X - λ1||_2 -> 0` with
  `λ = tr X/|tr X|`.
- **The sign is soft.**
  - `x in Rad_sof(H)`: tensor a sofic representation of `Q ⊇ im H` with one of `G`, pulled back along `k ↦ 1`.
    Theorem 4.1 puts `σ(tkt^(-1))` in the centralizer of `σ(Gamma)`. So `σ(h) = σ(t^(-1)γt)` commutes with `σ(k)`,
    and `r ↦ 1`.
  - The surjection `H ->> Wtilde_S` sends `x` to `z`, since `{o, y} in S`. So `z in Rad_sof(Wtilde_S)`, and
    `rho(z)` is block-diagonal.
- **Corners.** Close projections in `M_k` have equal rank once the unnormalized distance is below 1. So the rank
  function of `p_-` is `psi`-invariant, and each stratum `Y_r` gives a block-size-`r` model with `rho_r(z) = -1`.
- **Tensor square.**
  - `rho_r ⊗ conj rho_r` sends `z` to `1`.
  - `Vtilde_S/<z> = F_2[X]`, so it is a bounded-block model of `W`. Theorem 9 kills `K_even` there.
  - By (SC), each `rho_r(utilde)` is a scalar.
- **Lemma 13.**
  - Suppose `b_S` vanishes on fibre-even pairs. Substituting `u = e_o + e_a`, `v = e_y + e_c` gives
    `1_S(a, c) = f(a) + f(c)` for all `a != c` in `F`. I checked the cases `a` or `c` in `{o, y}` separately; they use
    `f(o) = 0` and `f(y) = 1`.
  - The edge set is complete bipartite on `(A, F \ A)` with both sides nonempty. It determines the bipartition, so
    `N -> Z/2` is a homomorphism. It is trivial, because `N` is perfect.
  - `N` is transitive on `F`, so `A` is `∅` or `F`, a contradiction.
- **Contradiction and descent.** Scalars commute, so `rho_r(z) = 1`. Hence `p_- = 0`, `rho` factors through `W`, and
  Theorem 9 applies.

## 5. Citations and imports

- **Kun--Thom arXiv:2608.06222.**
  - Definition of infranormal, Theorem E, Theorem 4.1 and Definition 2.1: checked against the verbatim transcription
    in `research/artifacts/kun-thom-2608-06222-verified.md`. Hypotheses as used: `Gamma` infranormal, `Gamma` and
    `G` Kazhdan, `σ` with `tr σ(g) = 0` for `g != 1`. §6 records the check against the arXiv PDF.
  - The unrefereed-preprint trust surface travels with every node here, as each node says.
- **`kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`**, `invariant-graph-clifford-phase` item 2 and
  `kun-thom-clifford-radical-phase` are consumed as established. I re-derived only the two facts used: the
  surjection's value on `x`, and `x in Rad_sof(H)`.
- **Not re-derived.** Corollary 4(b), Corollary 11(b) and the microstate corollaries lean on
  `diagonal-normalizer-rigidity` and `coarse-frame-normalizers-are-near-block-monomial`.

## 6. Verdicts

| claim | verdict |
|---|---|
| `kt-wreath-monomial-models-kill-fibre-even-lamps` | PASS on the lemmas §14.3 left open (§§1--3). With §14.3, the whole derivation is now reviewed |
| `soft-kazhdan-central-elements-fixed-by-normal-closure` | PASS (§2, §3), one notation note |
| `kt-clifford-cover-block-models-kill-the-sign` | PASS (§4) |

None of these decides Question 3.4. Every conclusion is about bounded-block models, and the nodes say so.
