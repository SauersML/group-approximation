# ZP review, groups, part 2 (lane z-verify-groups, 2026-09-13)

Continues `zp-review-groups-2026-09-13-part1.md`. Two claimed answers to list problems: Problem 3.9
(first part) and Problem 2.10 (first part). Both **PASS**, with the import notes recorded below.

## 10. Problem 3.9, first part: B_n is self-similar iff n ≤ 3 (z3-09-braid-self-similar, 822b3ac5f2)

Claims: `braid-group-self-similar-iff-at-most-three-strands` through
`braid-self-similarity-from-small-and-large-cases`, from
`braid-groups-on-at-most-three-strands-are-self-similar` (+ `-proof`) and
`braid-groups-on-four-or-more-strands-are-not-self-similar` (+ route
`braid-non-self-similarity-via-geometric-injections`), which imports
`finite-index-injections-into-braid-quotients-are-geometric` (+ `-citation`).

### 10.1 The citation (checked at the source)

Behrstock–Margalit, *Curve complexes and finite index subgroups of mapping class groups*,
arXiv:math/0504328, was read on 2026-09-13 through the ar5iv rendering. Its Theorem 3, verbatim:
"If S is a surface which is not S_{0,2}, S_{0,3}, S_{0,4}, S_{1,0}, S_{1,1}, S_{1,2}, or S_{2,0},
then every injection of a finite index subgroup of Mod(S) into Mod(S) is the restriction of an inner
automorphism of Mod(S). If S is one of these exceptional surfaces, then there is an isomorphism of
finite index subgroups of Mod(S) which is not the restriction of an inner automorphism." Their `Mod(S)`
is the extended mapping class group, and the introduction credits the genus-zero case: "Bell–Margalit
proved that the answer is yes for S_{0,n} with n ≥ 5, giving applications to the study of Artin groups."
So the graph's `-citation` route quotes the theorem correctly, including the exceptional list.
Specialization: for `n ≥ 4` the surface `S_{0,n+1}` has at least 5 punctures and is not exceptional;
`B_n/Z ≅ Mod(D_n)` is the puncture stabilizer, of finite index in `Mod^±(S_{0,n+1})`, so a finite-index
subgroup of `B_n/Z` is a finite-index subgroup of `Mod^±(S_{0,n+1})` and an injection into `B_n/Z` is an
injection into `Mod^±(S_{0,n+1})`. Correct.

### 10.2 The positive half, `n ≤ 3`

Re-derived in full. `B_3 = ⟨a, b | a² = b³⟩`, `z = a² = Δ²` generates the centre, `B_3/⟨z⟩ ≅ PSL_2(Z)`.
`Λ = Γ(2)/{±I}` is free of rank 2 of index 6 in `PSL_2(Z)` (note `−I ∈ Γ(2)`), so `P = π^{-1}(Λ)` has
index 6, `P = s(Λ) × ⟨z⟩` for a section s (which exists because Λ is free), and `H = s(Λ) × ⟨z²⟩` has
index 12. `c_D(A) = DAD^{-1}` with `D = diag(2,1)` is `[[a,2b],[c/2,d]]`, which maps `Γ_0(2) ⊇ Γ(2)` into
`SL_2(Z)` and fixes `−I`, so it induces an injection `c : Λ → PSL_2(Z)`; `F_0` lifts it, and
`F(s(λ)z^{2k}) = F_0(λ)z^k` is a homomorphism because `z` is central, with `π ∘ F = c ∘ π` on H.
Core: for `K ◁ B_3` with `K ≤ H` and `F(K) ≤ K`, the matrix entries of `π(K)` satisfy `c/2^k ∈ Z` for all
`k`, so `c = 0`, `ad = 1`, and `π(K) ≤ {±[[1,m],[0,1]]}`; conjugating by `±[[0,1],[−1,0]]` leaves that
set, so normality gives `π(K) = 1`, hence `K ≤ ⟨z²⟩` and halving gives `K = 1`. The two model tests
(dropping the halving, or replacing `c` by the identity) both produce a nontrivial core, as claimed, so
each ingredient is load-bearing. The direction of the Nekrashevych–Sidki correspondence that is used
(trivial core ⇒ faithful) is proved inline in §0 of the route, so the citation carries no weight.
Verdict: **PASS**.

### 10.3 The negative half, `n ≥ 4`

Re-derived the chain.
- Lemma A (no two nontrivial normal subgroups of a finite-index `Λ ≤ Γ` commute) uses four standard
  facts: the centralizer of a finite-index subgroup of `Mod^±(S)` is trivial for `S = S_{0,m}`, `m ≥ 5`
  (density of pseudo-Anosov laminations in PMF plus faithfulness on the curve complex); Ivanov's
  trichotomy; McCarthy's virtually cyclic `E(g)`; and canonical reduction systems. The three cases
  (finite, infinite reducible, containing a pseudo-Anosov) are handled correctly, and the final step
  (`M ≤ E(g) ∩ E(g')` forces M finite, contradicting the earlier step) is right.
- Lemma B(a): `f(L)` central gives `[L,L] ≤ ker f`; `M_f` is the intersection of the G-conjugates of
  `[L,L] ∩ core_G(H)`, so `f(M_f) = 1` and `π(M_f) ≠ 1` by Lemma A. Correct.
- Lemma B(b): `W = H ∩ ker e` has `π` injective on it (`Z(G) ∩ ker e = 1` because `e(z) = n(n−1) ≠ 0`),
  `π(W)` has finite index in `Q`, and `ψ_f` is injective, so the rigidity theorem applies. Correct.
- Joint core: the section identity `k|_{g x_i} = g|_{x_i} f_i(g^{-1}kg) (g|_{x_i})^{-1}` and induction on
  levels give that an invariant normal `K ≤ ∩ H_i` acts trivially, so faithfulness forces `K = 1`; this
  is the Dantas–Santos–Sidki criterion, proved inline. Correct, and transitivity is never used.
- Construction of `K`: `K = M ∩ π^{-1}(B)` with `M = [H*,H*] ∩ N_a`, `A = π(M)`, `B` the intersection of
  the `Γ`-conjugates of `A` with `core_Γ(Q)`. Kind (a) kills `K`; kind (b) sends `K` into `K` because
  `f_i(k) ∈ [G,G]`, `π(f_i(k)) = φ_i π(k) φ_i^{-1} ∈ B = π(K)`, and `[G,G] ∩ Z(G) = 1`. Correct.
- **Wording note (not a gap).** Step 2 of "Building a nontrivial such K" argues `π(M) ≠ 1` through an
  iterated commutator "whose lift lies in M". Written at the level of elements this needs one extra line;
  at the level of subgroups it is immediate: `X = [H*,H*]` and `Y = N_a ∩ H*` are both normal in `G` with
  `π(X) ≠ 1` and `π(Y) ≠ 1` (Lemma A), so `[X,Y] ≤ X ∩ Y ≤ M` is normal with `π([X,Y]) = [πX, πY] ≠ 1` by
  Lemma A. Recommend rewriting that step with subgroups rather than elements.
Verdict: **PASS**, conditional on the two literature layers the route names: Behrstock–Margalit Theorem 3
(checked verbatim above) and the standard mapping-class-group facts in Lemma A (Ivanov, McCarthy,
Korkmaz), which were not re-read at the source here.

### 10.4 Scope of the answer

The classification answers the first question of Problem 3.9. The second ("are there finitely presented
residually finite groups that don't embed in a finitely presented self-similar group?") is untouched and
remains with the Boone–Higman region. Novelty check requested from z-status-b.

## 11. Problem 2.10, first part: braided V is Hopfian (z2-10-bv-hopfian, f7c5912d5d + cda0020eb3)

Claims: `braided-thompson-v-is-hopfian` (+ `-proof`) from
`surjective-endomorphisms-of-braided-v-preserve-pure-part`,
`pure-braided-thompson-group-is-residually-nilpotent` and
`braided-v-graded-pure-quotients-are-noetherian`; artifact `zp-braided-v-hopfian-2026-09-13.md`.

- **Lemma A.** `M = φ^{-1}(P_br)` is normal and proper, so `M ≤ P_br` by Zaremsky Cor. 2.8;
  `V_br/M ≅ V` is simple; `P_br/M` is a proper normal subgroup of it, so `M = P_br`. Correct, and the
  surjectivity hypothesis is used twice (properness of M, and `φ(P_br) = P_br`).
- **Lemma B.** Cloning `κ_k : PB_n → PB_{n+1}` has the strand-deletion left inverse, so
  `γ_c(P_br) ∩ PB_T = γ_c(PB_T)`; Artin's representation lands in `IA_n`, Andreadakis gives
  `γ_c(IA_n) ≤ A_c`, and `∩_c A_c = 1` by residual nilpotence of free groups. Correct.
- **Lemma C / the FS^op structure.** `gr(PB_n)` is generated in degree 1, so a Lie-ring map is determined
  by `A_{ij} ↦ Σ_{a ∈ f^{-1}(i), b ∈ f^{-1}(j)} A_{ab}`; different permutation braids permute clones inside
  a fibre and leave that formula alone, which gives well-definedness and functoriality. A c-fold bracket
  involves at most 2c strands and is the image of the corresponding bracket in `L_c(r+1)` under the
  collapsing surjection (its fibres over `1..r` are singletons), so `L_c` is generated in degrees ≤ 2c+1.
  Correct.
- **Transfer to `gr_c(P_br)`.** Checked the three closure properties. Independence of T and invariance
  under bijections are conjugations by elements of `V_br`, so they preserve a V-invariant N. For a
  surjection f, the expansion step is an equality of elements of `P_br` (not a conjugation), and only the
  repositioning of clones is a conjugation, by `(T', b, T')`; both keep N. Strict inclusions are preserved
  because any element lies in some `L_c(PB_T)`. Correct.
- **The Hopfian argument.** `ψ_c` is surjective because `ψ(γ_c) = γ_c`; `K_j = ker ψ_c^j` is invariant
  under conjugation by every `x ∈ V_br` through `ψ(xpx^{-1}) = φ(x)ψ(p)φ(x)^{-1}`, since `γ_{c+1}(P_br)` is
  characteristic in `P_br` and so normal in `V_br`; stabilization gives injectivity of each `ψ_c`;
  residual nilpotence upgrades that to injectivity of `ψ`; `ker φ ≤ P_br` finishes. Correct.
- **Import note.** Sam–Snowden arXiv:1409.1670: Theorem 8.1.2 was confirmed verbatim through ar5iv ("If C
  is a quasi-Gröbner category then for any left-noetherian ring k, the category Rep_k(C) is noetherian"),
  and Corollary 8.1.3 is the FS^op instance, as the route says. My extraction of the definition of FS came
  back as "finite sets with all maps", which disagrees with the lane's PDF quote ("FS is the category of
  nonempty finite sets with surjective functions"). The lane's reading is the standard one and matches the
  use here; the disagreement is almost certainly an artifact of my HTML extraction. Re-confirm the one
  sentence from the PDF when convenient. This is the only load-bearing external input.
- Verdict: **PASS** for the Hopfian half. The root correctly stays open: part (Q), whether every quotient
  of `bV` is finitely presented, i.e. max-n, is not decided, and the artifact's §6 proves only the
  bounded-depth case. Novelty check requested from z-status-b.
- Consistency: Zaremsky Prop. 4.8 shows `P_br` itself is not Hopfian; its surjection forgets strands and is
  not V-equivariant, so it is not of the form used here. Nothing contradicts it.
- `F_br` is correctly left open: the ordered analogue of FS^op noetherianity was not checked.

## 12. Queue and triage (reviewed status as of this part)

Not yet reviewed, in my priority order: 2.09 (rational acyclicity of bV; the integral question is the
actual Problem 2.9), 3.08, 2.13, 1.07, 3.03, 3.07, 3.10, 2.20, 2.15b, 1.10 obstructions, 1.20 tools,
2.01 lemmas, and the 2.19(a) cubulated composition. None of them is an answer to a list problem, so the
list-answer items above took precedence. A least-fixpoint pass over the graph at `f1caaea0ab` found no
`requires: []` route firing into a `zaremsky-*` root and no established root in this scope beyond those
recorded in part 1 and here.
