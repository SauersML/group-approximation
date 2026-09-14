# SK verify 13, part 4: the "Other finite fields" subsection for rev4 (sk-general-statement)

Lane sk-verify-13 (wave 10), 2026-09-13. Queue line 7. Target: `research/artifacts/sk-general-statement-proposal-2026-09-13.md`
(d7ef2a68fd), §(b) LaTeX (20 lines) and §(f) derivations. Main asked me to focus on the unreviewed parts: the LaTeX itself,
and the extension from n = 3 to n ≥ 3 for the PSL_{nN}(F_q) marked limit and the expanders.

I checked every sentence of the subsection by hand against the rev4 draft
`sk/lanes/sk-general-statement/rev4-base.tex` (md5 eee41cb5…, identical to `sk/drafts/rev4.tex`): finite models l.143–199,
simplicity l.201–258, rank two l.260–283. The component theorems already have reviews (proposal §(e)). I did not redo
those; I checked that the text instantiates them correctly.

## 0. Verdict

**PASS-WITH-FIXES.** The mathematics is correct: every claimed property for n ≥ 2, and the marked limit of PSL_{nN}(F_q)
with expanders for n ≥ 3.

Two sentences of the rev4 proof are specific to F_2, and "the proofs above apply … and three changes" carries them over
silently. These are G1 and G2 below. Each costs one line. G3 is recommended at 0 lines; G4–G6 are optional wording.

**Compile, spot-checked on MSI.** `/scratch.global/sauer354/sk/sk-general-statement/rev4-fq.log`: 0 errors, 0 overfull,
0 undefined, 8 pages. `rev4-fq.tex` md5 47bf8f27… matches the proposal, and the diff against the base is exactly the
subsection inserted after l.284.

## 1. The statement
- **(T).** For n ≥ 3, `R = LC(X,F_q) ⋊ Z` is finitely generated as a ring, by `u^{±1}`, the `e_a` and a generator of
  `F_q` over `F_p`, so EJZ applies. For n = 2, rev4 l.260–274 uses only full idempotents and EJZK relative (T), with nothing
  specific to the field.
- **Finitely generated.** For n ≥ 3 through the generators; for n = 2 because a countable Kazhdan group is finitely
  generated.
- **Infinite.** `e_12(LC(X,F_q))` is infinite and `Z` is finite.
- **Centre.** "Z consists of scalar matrices" claims only `Z ⊆ F_q^×I_n` (F5-compliant); see G3.
- **Simple modulo `Z`.** §2.
- **LEF.** §3.
- **Scope.** The expander clause is claimed for n ≥ 3 only (F4-compliant). No "n = 2 loses (T)".

## 2. Simplicity: the three named changes

**Change 1.**
- rev4 l.210–222 with "equals a nonzero constant on U" gives `g = cI_n` with `c ∈ LC(X,F_q)^×`.
- Commuting with `e_ij(e_Vu)` gives `ce_Vu = e_Vuc = e_V(c∘T^{-1})u`, so `c = c∘T^{-1}` on every small `V`. The set where they
  differ is clopen and contains no small set, so it is empty and `cu = uc`.
- Then `c` is central in `R`, so `cI_n ∈ Z(G)`.
- The rationale is right: `cI_n` commutes with every `e_ij(e_V)` for every unit `c`, so the roots `e_V` alone cannot
  separate noncentral scalars over `F_q`.

**Change 2** (margin `m = w+1`, `h = e_ij(e_Vu^c)`, `c ∈ {0,1}`).
- The `ε_ab`, `|a|,|b| ≤ m`, are matrix units: `V ∩ T^tV = ∅` for `0 < |t| ≤ 2m`. They are nonzero and linearly independent,
  and `S ≅ M_{2m+1}(F_q)`.
- **Product formula.** `fu^a(e_Vu^c)f′u^b = fe_{T^aV}(f′∘T^{−a−c})u^{a+c+b} ∈ F_qε_{a,−(b+c)}`.
  - `f∘T^a` is constant on `V` (`|a| ≤ w`), and `(f′∘T^{−a−c})(T^av) = (f′∘T^{−c})(v)` is constant on `V` (`|c| ≤ 1 ≤ m`).
  - The second indices lie in `[−m, w]`.
- **k − I and k^{-1} − I.** `s = e_Vu^c = ε_{0,−c}`.
  - `k − I_n = (ghg^{-1} − h)h^{-1}` with `h^{-1} = I − sE_ij`. Products `ε_abε_{0,−c}` keep second index `−c ∈ [−m, w]`.
  - `k^{-1} − I_n = h(gh^{-1}g^{-1} − h^{-1})`. Products `ε_{0,−c}ε_ab = δ_{−c,a}ε_{0,b}` keep `b ∈ [−m, w]`.
  - Both lie in `M_n(S)`, so `k ∈ H` by rev4 l.246–247.
- **Not scalar.** No entry of `k − I_n` involves second index `m`, so `κ` fixes the `n` basis vectors at the top level. If
  `κ` is scalar, it is `I`, so `k = 1`, which contradicts the choice of `h`.
- **Quasisimple step.**
  - Put `S_1` = the image of `SL_d(F_q)`. It lies in `G`: transvections `e_pq(λε_ab)`, with within-block ones as commutators
    through `p′ ≠ p`.
  - `k ∈ H` normalizes `S_1`, and `K ⊴ G`, so `[k,σ] ∈ K ∩ S_1`.
  - If `K ∩ S_1 ⊆ Z(S_1)`, then `[k,στ] = [k,σ]·σ[k,τ]σ^{-1} = [k,σ][k,τ]`, a homomorphism from a perfect group
    (`d = n(2w+3) ≥ 6`) to an abelian one, so it is trivial. Then `κ` centralizes `SL_d(F_q)` and is scalar, a contradiction.
  - A noncentral normal subgroup of the quasisimple `S_1` is `S_1`. So `e_pq(e_V) = e_pq(ε_00) ∈ K`.
- **Level step.** rev4 l.252–258 (n ≥ 3) and l.276–281 (n = 2) are field-free: additivity, commutators, the ring identity
  `1 − ∏(1 − e_{T^{a_i}V})`, and the Peirce propagation. `V ≠ X`, since `V ∩ TV = ∅`.

So every normal `K ⊄ Z` equals `G`, and `G/Z` is simple.

**Change 3, and the extension to n ≥ 3.**
- `F = F_q⟨τ_±, τ_a⟩`. `ρ_ℓ` is `F_q`-linear, and the matrix units give onto `M_{N_ℓ}(F_q)`.
- `EL_n(M_N(F_q)) = SL_{nN}(F_q)`, since transvections generate and in-block ones are commutators, for n ≥ 2.
- **Central iff scalar image.** For words of length at most `λ`, with finitely many words and the `q` values `μ ∈ F_q`:
  - if `g = μI_n` in `G`, the entries of `w_F − μI_n` vanish under `π`, and `φ_ℓ∘π = ρ_ℓ` on them for large `ℓ` gives a
    scalar image;
  - if the image is `μI`, the nonvanishing of `φ_ℓ` (rev4 l.170–172) forces `π(w_F − μI) = 0`, so `g` is scalar and
    central.
  - This holds uniformly for all large `ℓ`.
- `Z(SL_m(F_q))` is exactly the scalar matrices in `SL_m(F_q)`. So a word is trivial in `G/Z` iff it is trivial in
  `PSL_{nN_ℓ}(F_q)`: marked convergence. `PSL_m(F_q)` is simple for `m ≥ 3`.
- **Expanders (n ≥ 3).**
  - `EL_n(F)` is generated by `e_ij(1)`, `e_ij(λ_0)` and `e_ij(τ)`, where `λ_0` generates `F_q` over `F_p`: monomials and
    powers `λ_0^k` come from commutators, and sums from additivity.
  - It has (T) by EJZ, so its finite quotients `SL_{nN_ℓ}(F_q)` have a uniform spectral gap on these images (Margulis).
  - A function on `PSL` pulls back to `SL` with the same Rayleigh quotient, so the gap passes to the `PSL` quotients.
  - Dropping `e_ij(1) = ∏_ae_ij(τ_a)` changes the constant by a bounded factor.

## 3. LEF for n = 2
The `e_ij(τ)` do not generate `EL_2(F)`. But LEF needs only entrywise models: `φ_ℓ` on the finitely many entries of a finite
subset and its products, together with change 3's scalar criterion, gives injective partial models into
`PGL_{2N_ℓ}(F_q)`. rev4 l.282–283 already says this for `F_2`, and the subsection claims only LEF for n = 2. Correct.

## 4. Fixes (verbatim)

**G1 (must, +1 line): `H ⊆ G` is F_2-only.**
- rev4 l.232–235 say that `H` lies in `G` because the transvections generate it. Over `F_q`, `q > 2`, transvections generate
  only `SL_d(F_q)`, so the sentence does not carry over. The subsection uses only `S_1 ⊆ G`.
- Replace `level, so $k\in H\cong\GL_d(\F_q)$ is not scalar.` with
  `level, so $k\in H\cong\GL_d(\F_q)$ is not scalar; the transvections now place only the copy of $\SL_d(\F_q)$ in $G$.`

**G2 (must, +1 line): the inverse formula.**
- rev4 l.245–246 give `k^{-1}−I_3=h(ghg^{-1}−h)`, which uses `h^{-1} = h`. Over `F_q` this is false, and rev4 l.246–247 need
  `k^{-1} − I` in `M_n(S)`.
- Replace `$k-I_n=(ghg^{-1}-h)h^{-1}\in M_n(S)$ has vanishing columns at the top` with
  `$k-I_n=(ghg^{-1}-h)h^{-1}$ and $k^{-1}-I_n=h(gh^{-1}g^{-1}-h^{-1})$ lie in $M_n(S)$, and $k-I_n$ has vanishing columns at the top`.

**G3 (recommended, 0 lines): scalar centre.** The statement's "Z consists of scalar matrices" needs `c` constant.
- Replace `then $g=cI_n$ with $cu=uc$, so $g\in Z$.` with `then $g=cI_n$ with $cu=uc$, so $c\in\F_q$ by minimality and $g\in Z$.`

**G4 (optional, wording).** "as a nonconstant unit of $\LC(X,\F_q)$ commutes with every $e_{ij}(e_V)$" compares a ring
element with a matrix. Use: "as $cI_n$ commutes with every $e_{ij}(e_V)$ for each unit $c$ of $\LC(X,\F_q)$".

**G5 (optional, wording).** "define small sets and the $\epsilon_{ab}$ with $w+1$ in place of $w$" should also name `d`,
which becomes `n(2w+3)`: "define small sets, the $\epsilon_{ab}$ and $d$ with $w+1$ in place of $w$".

**G6 (optional, wording).** Parallel to Theorem 1, l.82: "for $n\ge3$ it is the limit of groups $\PSL_{nN}(\F_q)$ in the
same way". This keeps "with respect to the images of a fixed generating set" without repeating it. The marking of
`EL_n(F)` then includes `e_ij` of the field generator. The phrase "a generator of $\F_q$ added to $u^{\pm1}$ and the $e_a$"
covers this if read for the $\tau$'s as well.

**Doctrine.** It uses "so", has no "hence", and the semicolons separate independent clauses. It never says "with the same
proof" (decision 23).

## 5. Status
- The subsection's LaTeX and its n ≥ 3 PSL_{nN}(F_q) marked limit and expanders: PASS-WITH-FIXES (G1, G2), reviewed here.
- There is no Cairn claim node for the generalization. It rests on the reviewed component nodes in proposal §(e) plus this
  review.
