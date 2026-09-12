# Adversarial review (reviewer-2): Leavitt tensor hosts and the positive-characteristic Boone--Higman class

Reviewer lane `reviewer-2`, 2026-09-12. The coordinator requested this review
of the `boone-higman` lane's commits 39f4b641b and 26d251f05 (tree restored in
3f71a3a50). Scope:
- artifacts `boone-higman-leavitt-tensor-hosts-2026-09-12.md` and
  `boone-higman-prime-field-leavitt-hosts-2026-09-12.md`;
- nodes `leavitt-tensor-hosts-khanh-transfer-proof`,
  `prime-field-leavitt-tensor-hosts-proof`,
  `leavitt-square-unit-group-is-fp-simple-and-acyclic` and
  `positive-char-surface-linear-groups-satisfy-boone-higman`, with their chains.

**Sources.** Read from the extracted PDF texts:
- Khanh arXiv:2609.08428v1, full text lines 55-895: Theorem 2.2, Lemmas 2.3
  and 2.4, the proof of Theorem 2.2, Section 3, Lemma 4.1, Proposition 4.2,
  Theorem 5.1 and its proof, and Lemmas 5.2, 5.3, Theorems 5.4, 6.1;
- Ara--Cortiñas arXiv:1108.0352v3: abstract, introduction, Section 6;
- Belk--Bleak--Matucci--Zaremsky arXiv:2306.16356v3 (22 May 2025): Sections
  3-4 and Problem 5.3 with Remark 5.4;
- Zaremsky arXiv:2405.09722: abstract, Example 4.7, the proof of Theorem 1.2.

Nothing below is Lean-verified except where a Lean declaration is named.

## Verdicts

| Node | Verdict |
|---|---|
| `leavitt-tensor-hosts-khanh-transfer-proof` / `leavitt-tensor-hosts-acyclic-steinberg-and-fp` | PASS (trust surfaces below) |
| `central-simple-leavitt-tensor-unit-groups-are-simple` | PASS |
| `leavitt-square-unit-group-is-fp-simple-and-acyclic` | PASS |
| `prime-field-leavitt-tensor-hosts-proof` / `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` | PASS |
| `odd-leavitt-unit-groups-mod-scalars-are-fp-simple` | PASS |
| `positive-char-surface-linear-groups-satisfy-boone-higman` | PASS, conditional as stated |
| Novelty against the BH survey | No prior positive-characteristic linear class found (bounded) |
| Cairn wiring | No false establishment; four bookkeeping gaps |

## 1. The transfer over `B ⊗ L` (characteristic two) — PASS

**What in Khanh is specific to `L`.** The artifact's census (its Section 1)
matches the source text.
- Section 2 of Khanh is stated for "nonzero unital F_2-algebras" with
  `A^2 ≅ A`.
- Theorem 5.1 is stated for "a nonzero unital ring of characteristic two".
- Lemma 5.2 is stated for "any unital ring".
- The genuinely `L`-specific steps are two:
  - the stable input `K(R) = 0` from ABC Theorem 7.6 (Proposition 3.2, first
    paragraph);
  - Leavitt word reduction with coefficient `1` (Lemma 4.1).
  The artifact replaces exactly these.

**Lemma 2.1, normalization.** This is Khanh's Lemma 4.1 with coefficients in
`B`.
- `B ⊗ F_2<e,f> -> R` is injective, since positive words are independent in
  `L` and the tensor product is over a field.
- Khanh's prefix-antichain identity (4.1) holds in `R`, because `B ⊗ 1`
  commutes with `L`.
- The disjoint length intervals `[j(Λ+1)+1, j(Λ+1)+1+Λ]` and the suffix
  `e^M f` work verbatim.
- `η_i* a_i x = c_i ⊗ 1` with `c_i != 0` follows, because `η_i* ν = 0` for
  every other antichain word `ν`. Neither word is a prefix of the other,
  which rules out a nonzero `η_i* ν = ρ*`.

**Lemma 2.2, simultaneous strong division.** Checked by computation.
- `Y_i (c_i ⊗ 1) Z = Σ_(k,(i',k')) y_(ik) c_i z_(i'k') ⊗ β_(ik)* β_(i'k') = Σ_k y_(ik) c_i z_(ik) ⊗ 1 = 1`,
  since same-length distinct words give `β* β' = δ`.
- `u_i a_i X = Y_i η_i* a_i x Z = 1`.
- **Kernel.** The idempotent `η_i η_i*` splits `R = η_i R ⊕ ker η_i*`, and on
  `η_i s` the map `u_i` is `Y_i s`. So
  `ker u_i = η_i ker Y_i ⊕ ker η_i* ≅ ker Y_i ⊕ R^h` by Khanh (4.2).
- `Y_i W_i = 1` with `W_i = (c_i ⊗ 1) Z` gives `R = W_i R ⊕ ker Y_i` with
  `W_i R ≅ R`.
- Hence `ker u_i ≅ R^h ≅ R` by leaf coordinates, with `h >= 1`. PASS.

**Proposition 2.4, Khanh Prop. 4.2 over `R`.** Khanh's decomposition (4.3) and
its coordinate formulas (4.4) use only `b_i y_i = 1` with `y_i = ρ_i v`. His
complement identification (4.5) uses only an explicit isomorphism
`ker b_i ≅ R^(q_i - 1)`. The replacement `(x, η_i*) -> (X, u_i)` supplies both.
`ρ_i Φ` is left multiplication by some `a_i != 0` in any ring. Corollary 4.3
(coning) and the fan argument of Theorem 5.4 use only Proposition 4.2. PASS.

**Proposition 3.1, standard inclusions.**
- Khanh's Proposition 3.2 uses the compression `c`, the identity
  `Φ_(s+1)(c(u)) = diag(Φ_s(u), I)` and the unit `w` with
  `w c(u) w^-1 = c(c(u))` (his (3.5), (3.6)). All three live in `e, f`.
- `(c_*)^2 = c_*` plus local nilpotence gives `c_* = 0` on `H_n` as soon as
  `lim H_n = H_n(GL_∞(R)) = 0` in that degree.
- Remark 3.2 is correct in the direction used: `K_i(R) = 0` for `i <= N` makes
  `BGL^+` `N`-connected, and Hurewicz gives `H_i = 0` for `i <= N`. PASS.

**Theorem 4.1, acyclicity by degree.** The degree accounting was checked
against Khanh's proof of Theorem 2.2 (text: induction on `n`).
- Step `n` fixes `r = n+3`.
- It uses the induction hypothesis `H_t(A^x) = 0` for `0 < t < n`.
- It uses hypothesis (2) at `r = n+3`, so that the Borel projection is an
  isomorphism on `H_n`.
- It uses hypothesis (1) only in degree `n`, through Lemma 2.4 with `k = 1`,
  `q = n+2`.

The truncated form is correct. For the two headline groups every `K_i`
vanishes, so the untruncated Theorem 2.2 applies anyway. PASS.

**Theorem 4.2, GE, Steinberg comparison and finite presentation.**
1. **GE.** Khanh's Lemma 5.3 reads the Menal--Moncasi remark as applying "to a
   simple ring in which each nonzero x admits y,z with yxz = 1, and requires
   no regularity assumption". Corollary 2.3 supplies that hypothesis for
   `B ⊗ L`. `H_1(R^x) = 0` then puts every `diag(u,1)` in `E_2`, by Whitehead's
   identity as in his proof. PASS; trust surface: Menal--Moncasi and
   Ara--Goodearl--Pardo, not re-read.
2. **Steinberg comparison.**
   - `St_3` is perfect and `H_2(GL_3(R)) = 0`. The five-term sequence gives
     `N_3 = [St_3, N_3]`, and Lemma 5.2 kills `j_3(N_3)` in `St_4`.
   - Theorem 5.1 applies as stated, since `R` has characteristic two.
   - The coordinate refinement in Khanh's Theorem 5.4 uses only `T_r U_r = I`,
     `U_r T_r = I` and Voronetsky §4, Proposition 1. Khanh states it needs "no
     hypothesis on stable rank, quasi-finiteness, or centrality". PASS; trust
     surface: Voronetsky, not re-read.
3. **Finite presentation.** The displayed presentation of `B ⊗ L` is correct:
   over a field, the tensor product is the coproduct modulo commutation of
   generators. Krstić--McCool Theorem 3 (`n >= 4`, finitely presented rings)
   applies at rank 5. PASS.

**Theorem 5.1, simplicity; Lean check.**
- `GroupApproximation/Leavitt/RootDetectionBinary.lean`,
  `rootDetection_of_leavittFamily`, has hypotheses `3 <= card ι`,
  `LeavittFamily R`, `hdiv`, and `hcentral` (every central unit is `1`).
- `ElementarySimplicity.lean`, `isSimpleGroup_of_rootDetection`, has
  hypotheses `hdiv`, nontriviality and detection.
- For central simple `B`, `Z(B ⊗ L) = Z(B) ⊗ Z(L) = F_2`, since the centre of a
  tensor product over a field is the tensor product of the centres. So the
  only central unit is `1`.
- Both files are `sorry`-free and imported by `GroupApproximation.lean`. No
  axiom audit was run in this review. PASS.

## 2. `(L ⊗ L)^x` — PASS

- **`L` central simple:** `leavitt-center-is-coefficient-field` (Lean, every
  field) plus Corollary 2.3 with `B = F_2`.
- **Finitely presented:** Khanh (6.1).
- **K-theory.**
  - Ara--Cortiñas work "over a field k", with `L_2` the Leavitt algebra of type
    `(1,2)` over `k`.
  - Lemma 6.1 ("Let E be a finite graph. Then L(E) is regular supercoherent")
    and Proposition 6.2 ("Let R be regular supercoherent. Then the algebraic
    K-theories of L_2 and of L_2 ⊗ R are both trivial") match the quotes.
  - The introduction says "all algebraic K-theory groups K_i, i ∈ Z, vanish on
    them".
- **Trust surface:** the regular coherence of path algebras
  (Ara--Brustenga [3]) behind Lemma 6.1 was not re-read.

## 3. Every prime field — PASS

**Lemma 1.1, Quillen's count at odd `p`.** Correct.
- **Annihilation by `p`.** The cellular complex of `BZ/p` has differentials
  `0` in odd degrees and `p` in positive even degrees. Khanh's identity
  homotopy on each two-term summand, tensored, gives `p H_j(V;Z) = 0`, and
  `Z --p--> Z -> F_p` gives the injection.
- **Cohomology and weights.** `H*(V;F_p) = Λ(V^∨) ⊗ S(βV^∨)` is natural in
  linear automorphisms. A degree-`j` monomial has at most `j` factors, since
  Bockstein generators have degree 2 and one weight each. So its weight is a
  sum of `s` powers `p^a` with `1 <= s <= j`.
- **Carrying.** Replacing `p` counters by one in the next cyclic position
  preserves the residue mod `d = p^m - 1` and strictly lowers the count. The
  terminal digits satisfy `c_a <= p-1` with `1 <= Σ c_a <= s < m`. Their value
  lies in `[1, d-1]`: `d` itself needs `m(p-1) >= m` counters. This is Quillen's
  Lemma 16 for general `p`.
- **Norm.** The norm vanishes on nontrivial characters, and `d` is prime to
  `p`.

**Lemma 1.2 and Theorem 1.3.** Khanh's proofs of Lemma 2.4 and Theorem 2.2 use
the prime 2 only through Lemma 2.3's conclusions: "annihilated by 2", "odd
order", "2-primary". The embedding `F_(2^m) -> A` goes through
`A ≅ M_m(A)`. Replacing these by `p`, "prime to `p`" and `F_(p^m)` is
mechanical. PASS.

**Theorem 2.1, the signed Steinberg comparison.** Checked by computation. In
Khanh's proof of Theorem 5.1, characteristic two enters only through
`w_ij^2 = 1`, used to get the reverse conjugation identities.
- **Braid relation.** With `τ' = [[0,-1],[1,0]] ⊕ I` and `h'` the signed swap
  of `b_2, b_3`, both `τ'h'τ'` and `h'τ'h'` send `b_1 -> b_3`, `b_2 -> -b_2`,
  `b_3 -> b_1`.
- **Weyl lift.** `X_12(-1)X_21(1)X_12(-1)` maps to `τ'`.
- **Conjugation by `W`, from the Steinberg relations alone:**
  - `X_1j(c) -> X_2j(c)` and `X_2j(c) -> X_1j(-c)`;
  - `X_i1(c) -> X_i2(c)` and `X_i2(c) -> X_i1(-c)`, via successive commutators;
  - `X_12(c) = [X_13(c), X_32(1)] -> [X_23(c), X_31(-1)] = X_21(-c)`, and
    `X_21(c) -> X_12(-c)`.

  This is the substitution `X_ij(c) -> X_(π(i)π(j))(ε_i ε_j c)` read off from
  `τ' b_i = ε_i b_(π(i))`. These substitutions compose as signed matrices.
- **Central correction.** `W W_23 W` and `W_23 W W_23` agree on generators, so
  `z` is central and maps to `1`.
- **Relations.** `ψ(T) = W z` gives `ψ(T)σ(h')ψ(T) = z^2 W W_23 W = z W_23 W W_23 = σ(h')ψ(T)σ(h')`.
  `η'(k(a,b,H)) = k(-b,a,H)`, and
  `W σ(k) W^-1 = ℓ_0(H) x_1(-b) x_2(a) = σ(η'(k))`.
  `σ(h') = ℓ(H') = W_23`, since `ℓ` is word-independent.
- **Brown presentation.** Khanh's derivation of (5.4) uses only `τ b_1 = b_2`,
  `h ∈ J` with `h b_2 = b_3`, and equality of the two projections. The ordered
  frame complex has no edge inversions. His remark that `T^2 = 1` follows is
  not used in proving `p: Π -> G` is an isomorphism, so its failure for signed
  `τ'` is harmless.
- **Surjectivity.** It uses `X_i1(-c)` and `X_21(-c)` in place of `X_i1(c)`,
  `X_21(c)`.

PASS.

**Theorem 4.1, simplicity modulo scalars; Lean reading.**
- In `GroupApproximation/Leavitt/DiagonalNormalExtraction.lean`, `hcentral` is
  used in `exists_elGen_mem_of_diagonal` only at line 86, to prove
  `center = ⊥`. That is used only to get `g ∉ center` and a noncommuting `z`,
  at lines 87-99.
- The non-diagonal branches of `rootDetection_of_leavittFamily`,
  `exists_elGen_mem_of_inv_entry_zero` and `exists_elGen_mem_of_dense_entries`,
  take no `hcentral`.
- So for a normal `N` not inside the scalar centre `F_p^x`, choosing `g ∈ N`
  noncentral runs the same proof.
- The centre of `E_n(R)` is `F_p^x ∩ E_n(R)`, since `Z(R) = F_p`.

PASS as a written argument. **Not formalized:** the Lean theorems carry
`hcentral` and do not state the odd-`p` result.

**Theorem 5.1 and Theorem 6.1, odd `p`.**
- **K-theory.** Ara--Cortiñas work over an arbitrary field, so `K(L_p) = 0` and
  `K(L_p ⊗ L_p) = 0`.
- **Presentation.** A finitely presented group modulo a finite central
  subgroup is finitely presented.
- **Laurent realization.** It is characteristic-free:
  - the monic normalization `1/h = t_d/(c f)` holds;
  - `C[g^±][T]/(f(T) - g) ≅ C[t_d][1/f]` is free of rank `deg f`;
  - `F_p[g^±] -> L_p` is injective by the test-module argument.
- **Avoiding scalars.** `diag(x, 1)` is scalar only for `x = 1`.

PASS.

## 4. Novelty — no prior positive-characteristic linear class found (bounded)

- **Survey v3, Problem 5.3.** It lists braid, mapping class, `Aut/Out(F_n)`,
  non-solvable BS, `GL_n(Q)`, free Burnside, finitely presented metabelian,
  free-by-cyclic, one-relator, CAT(0), automatic, finitely presented residually
  finite and Artin groups. None is a positive-characteristic linear class.
- **Remark 5.4** records Bux--Llosa Isenrich--Wu (BS, free-by-cyclic) and
  Belk--Fournier-Facio--Hyde--Zaremsky (`Aut(F_n)`).
- **Known containers.** Scott 1984 (`GL_n(Z)`), `V`, Röver--Nekrashevych
  groups.
- **"Characteristic p" in the survey.** It appears only as Boone--Higman
  analogues for rings of characteristic `p` ([57], line 402). That is an
  embedding theorem for rings, not for linear groups.
- **Zaremsky 2405.09722.** Example 4.7 gives self-similarity of
  `R^⊕n ⋊ GL_n(R)` when `R` has a finite-index principal left ideal `Rx`
  (`x` a non-zero-divisor, `∩ Rx^k = 0`), and Boone--Higman *if that group is
  finitely presented*. The paper instantiates only `Z` and `Z[1/m]`,
  characteristic zero.
  - `F_q[t]` and `F_q[t,1/t]` meet the ideal hypothesis. No source read here
    establishes finite presentation of the corresponding affine groups.
  - So Example 4.7 is a *possible alternative technique* for transcendence
    degree one in characteristic `p`, not prior art for it.
  - Transcendence degree two (`F_q[t_1,t_2]`) is out of its reach.
- **Web search** (2026-09-12) found no positive-characteristic linear class.
- **Assessment.** This is a genuine new class as far as a bounded check can
  tell. The node's scope sentence is accurate. The Baumslag metabelian example
  is one instance of Problem 5.3(7), not the whole item, and the node says so.

## 5. Cairn wiring

**No false establishment.**
- `boone-higman-via-central-simple-leavitt-tensor-host` requires the open
  `decidable-group-algebras-have-fp-central-simple-hosts`.
- `leavitt-tensor-powers-have-trivial-k-theory` is OPEN.
- The Boone--Higman root stays OPEN.

**Bookkeeping gaps.** None affects correctness.
1. `leavitt-tensor-hosts-khanh-transfer-proof` requires the `L`-specific
   conclusions `leavitt-unit-group-finitely-presented` and
   `leavitt-steinberg-map-iso-from-rank-three`. What the derivation uses is the
   general criteria: Khanh's Theorems 2.2 and 5.1, Lemma 5.2, Menal--Moncasi
   GE, Voronetsky's refinement and Krstić--McCool. Those should be citation
   claims the route requires.
2. `prime-field-leavitt-tensor-hosts-proof` requires the characteristic-two
   claim `leavitt-tensor-hosts-acyclic-steinberg-and-fp`. That claim is about
   `F_2`-algebras and does not imply the odd-`p` host theorem. The route uses
   characteristic-free steps of its *proof*, so the dependency should be on
   those steps (or on the general-criteria claims of item 1).
3. `ara-cortinas-leavitt-tensor-k-theory-vanishes` is titled "binary Leavitt
   algebra", but its body correctly covers every field. The odd-`p` consumer
   relies on the body, so the title should say "over every field".
4. The odd-`p` simplicity-mod-centre step is a paper argument reading a Lean
   proof, not a Lean theorem. Any wording that suggests Lean certification for
   it should be avoided.

## Trust surfaces (unchanged by this review)

- Khanh v1 is unrefereed. Its criteria were re-read at statement and
  proof-structure level; the stabilizer spectral sequence was not re-derived.
- Menal--Moncasi / Ara--Goodearl--Pardo GE, Voronetsky's refinement,
  Krstić--McCool, Ara--Brustenga regular coherence: statements as quoted by
  their consumers, not re-read.
- The Lean root-detection theorems are `sorry`-free, but no axiom audit was run
  here.
