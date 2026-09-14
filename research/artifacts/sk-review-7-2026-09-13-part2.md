# SK review 7, part 2: the one-page §1 candidate, and rev3's §2 "LEF groups"

Lane `sk-verify-7`, 2026-09-13 ~20:20 CDT. Two items:
- (A) my queue item 1: sk-simpler-onepage's candidate §1;
- (B) the coordinator's request, after the ~20:00 restart: review the §2 LEF text of rev3.

I re-derived every step before reading the owners' verification notes.

Sources (none of these files is on main yet):
- (A) `sk/lanes/sk-simpler-onepage/research/artifacts/sk-simpler-onepage-proposal-2026-09-13{,-part2}.md` and
  `sk/lanes/sk-simpler-onepage/tex/cand-sec1.tex` (139 lines, md5 9f849a92…), which replaces rev3's §1. The proposal
  is not landed: the fleet stop interrupted its owner.
- (B) `sk/drafts/rev3.tex`, as assembled at 19:55 (md5 99aab8a5…, = `base-rev3.tex`), §2 l.254–344.
  - The part files updated at 20:00 (`rev3-part{A,B,C}.tex`, concatenated md5 316d5f57…) differ from the 19:55 assembly
    in §1 wording, the questions paragraph and the bibliography only.
  - §2 is unchanged, so this verdict applies to the current parts. If the re-assembled rev3.tex changes §2, I review
    the diff.

## 0. Verdicts

| Item | Verdict |
|---|---|
| (A) sk-simpler-onepage candidate §1: ring and (T), seam construction, models, marked limit, h-step, ring A and H, k ∈ H, level ideal, moved OA paragraph | PASS; notes N1–N5 |
| (B) rev3 §2 Corollary (LEF iff subgroup of an infinite f.g. simple Kazhdan LEF group) and proof | PASS; notes W6–W7 |
| (B′) rev3 §2 second corollary (one host containing every f.p. RF and every f.g. linear group) | PASS (concurrence; the formal owner is sk-verify-4) |

No FAIL, no GAP.

## 1. (A) The candidate §1, step by step
- **Ring and (T).**
  - `(fu^i)(f′u^j) = f u^i f′ u^{-i} u^{i+j} = f(f′∘T^{-i})u^{i+j}` and `ue_Uu^{-1} = e_{TU}`.
  - `u^je_au^{-j} = e_{[x_{-j}=a]}`; the products are the cylinder indicators.
  - `1 = Σ_ae_a` removes the generator 1. EJZ applies to the finitely generated ring.
  - Checked.
- **Seam (S1).**
  - By minimality the forward orbit of `x` is dense, so every word of `X` occurs in some prefix `x_{[0,M)}`.
  - `x_{[-ℓ,ℓ]}` recurs at arbitrarily large `p`.
  - For the `p`-periodic `y` agreeing with `x` on `[0,p)`:
    - `t ∈ [p,p+ℓ]` gives `y_t = x_{t-p} = x_t` from `x_{[p-ℓ,p+ℓ]} = x_{[-ℓ,ℓ]}`;
    - `t ∈ [-ℓ,0)` gives `y_t = x_{t+p} = x_t` from the same equality.
  - A window centered in `[0,p)` lies in `[-ℓ,p+ℓ)`, so it is a word of `X`. Every word of `X` occurs inside `x_{[0,p)} = y_{[0,p)}`.
  - The least period `N_ℓ` carries all `p_X(2ℓ+1)` windows, and bounded complexity forces a finite subshift.
  - Checked. The condition `p > 2ℓ` is not needed but is harmless.
- **Models and marked limit.** This is rev2's text, already PASSed in sk-review-2 part 2 with the repairs applied.
  - I re-checked `PD_ℓ(f)P^{-1} = D_ℓ(f∘T^{-1})`.
  - The disjoint supports once `N_ℓ > 2|j|`.
  - Surjectivity of `ρ_ℓ`: least period gives distinct shifts, windows of length `N_ℓ` separate positions, and `P` gives all matrix units.
  - `φ_ℓ∘π = ρ_ℓ` on bounded degree for large `ℓ`.
  - Triviality of words transfers both ways, and finitely many words per radius.
  - Checked.
- **h-step.** Identical to rev3's topologically free version.
  - For `c = Σc_tu^t`: `ce_V = Σc_te_{T^tV}u^t` and `e_Vc = Σe_Vc_tu^t`.
  - A nonzero `c_t` equals 1 on a clopen `U`. A small `V ⊆ T^{-t}U` or `V ⊆ U` witnesses `ce_V ≠ 0` or `e_Vc ≠ 0`, by uniqueness of coefficients.
  - The off-diagonal entries vanish from `g_{pi}e_V = 0`.
  - In `g_{ii}e_V = e_Vg_{jj}` the nonconstant coefficients sit on the disjoint `T^tV` and `V` (0 < |t| ≤ w ≤ 2w), and the constant coefficients agree on a dense family, hence everywhere.
  - `cc^{-1} = 1` gives `c` nowhere zero, so `c = 1`.
  - Checked. My part-1 notes W1–W3 are all reflected.
- **Ring A and group H (S2).**
  - `ε_{ab}ε_{a′b′} = e_{T^a(V∩T^{a′-b}V)}u^{a-b+a′-b′}`, which is 0 unless `a′ = b` because `|a′-b| ≤ 2w`.
  - Equal exponents with different `a` have disjoint supports, so the `(2w+1)^2` nonzero matrix units are independent and `A ≅ M_{2w+1}(F_2)` with unit `e = e_{⋃_aT^aV}`.
  - Since `(1-e)y = y(1-e) = 0` for `y ∈ M_3(A)`, the map `y ↦ (1-e)I_3 + y` is an injective homomorphism on `GL_3(A) ≅ GL_d(F_2)`.
  - Transvections between different rows map to `e_{pq}(ε_{ab})`. Those within a row are commutators through another row.
  - Checked.
- **k ∈ H (S3).**
  - `k - I_3 = (ghg^{-1}-h)h` and `k^{-1} - I_3 = h(ghg^{-1}-h)` lie in `M_3(A)`, using `fu^ae_Vf′u^b ∈ {0, ε_{a,-b}}`.
  - With `a = k-I_3` and `b = k^{-1}-I_3`, `kk^{-1} = I_3` gives `a+b+ab = 0`. Since `ea = a` and `eb = b`, `(eI_3+a)(eI_3+b) = eI_3`.
  - A one-sided inverse in the finite-dimensional algebra `M_3(A)` is two-sided, so `y ∈ GL_3(A)` and `k = (1-e)I_3 + y ∈ H`.
  - Checked.
- **Level ideal.** Unchanged from rev3. Checked.
- **Brown's formulation.**
  - Infinite simple gives ICC: a finite class gives a finite-index centralizer, whose core is `G`.
  - Not residually finite.
  - `L(G)⊗̄R ⊂ R^ω⊗̄R ⊂ R^ω`.
  - Kirchberg Thm 1.1; LLP [Ozawa p. 527].
  - Moving it after Simplicity removes the use of simplicity before its proof. Checked.

**Notes.** None changes the verdict.
- **N1 (structure).** The `□` now closes the proof after "Brown's formulation", but that paragraph is not part of Theorem 1's statement.
  - Option 1: end the proof after the level ideal and make the paragraph an unnumbered remark after the proof.
  - Option 2: keep it inside the proof and say in the theorem's last sentence that G answers Brown's form.
- **N2 (letter clash).** `p` is the seam position in "Finite models" and a row index (`g_{pi}`, `e_{pq}`) in "Simplicity". Use `m` for the seam position, as rev3 does.
- **N3 (optional).** "satisfy `yy′ = eI_3`" relies on one-sided inverses being two-sided in `M_d(F_2)`. Write "`yy′ = y′y = eI_3`", since both identities follow from `kk^{-1} = k^{-1}k = I_3`.
- **N4 (compatibility with §2).** The candidate introduces `A ≅ M_{2w+1}(F_2)` and `|a|,|b| ≤ w`. §2's substitution rule must also send `{a : |a| ≤ w}` to the ball `B_w` and `2w+1` to `|B_w|`, so `d = 3|B_w|`. This is the same gap as W7 below for rev3's own §1, and the same fix covers both.
- **N5 (rebase).** The candidate was cut from the 19:55 assembly. The 20:00 partA adds:
  - "By minimality the forward orbit of $x$ is dense";
  - `\cite{MorseHedlund38}` for bounded complexity;
  - "the shifts $T^ty_\ell$, $0\le t<N_\ell$, are distinct";
  - `\cite[Theorem~1.1]{EJZ}` for (T) of `EL_3(F)`.

  Merge these credits into the candidate before adoption.

## 2. (B) rev3 §2, step by step
- **Overgroup.**
  - `γ ↦ (φ_n(γ))_ω` is injective into `∏_ωQ_n`.
  - Doubling on `Q_n×{1,2}` makes each permutation a square pattern of two equal cycle structures, hence even.
  - Ore Thm 1 gives coordinatewise commutator witnesses in `Sym`.
  - A countable subgroup of an algebraic ultraproduct of finite groups is LEF.
  - `Δ = Δ_0 × Z` is infinite and LEF, with `S ⊆ [Δ_0,Δ_0] ≤ [Δ,Δ]`.
  - Checked. The factor `Z` exists to make `Δ` infinite, which the freeness argument needs.
- **Host and generation.**
  - `(δ,f)(δ′,f′) = (δδ′, f + δf′)`, so `L ≅ F_2≀Δ`.
  - Conjugating the flip at `e` by `δ` gives the flip at `δ` (`(δ1_e)(h) = [h=δ]`), so `L` is generated by `Δ` and one flip.
  - `u_δ e_{\{x(e)=1\}} u_δ^{-1} = e_{\{x(δ)=1\}}`, and these cylinders generate `LC(Z,F_2)`.
  - Checked.
- **Minimal and topologically free.**
  - The orbit contains the dense set `x + ⊕F_2`.
  - `δ = e`, `f ≠ 0` has no fixed point.
  - For `δ ≠ e` and a cylinder over finite `W`, choose `h ∉ W ∪ δW ∪ supp f`, possible because `Δ` is infinite.
  - Then `h, δ^{-1}h ∉ W` and `h ≠ δ^{-1}h`. So a point of the cylinder has `x(h) ≠ x(δ^{-1}h)`, and `(ℓx)(h) = x(δ^{-1}h) + f(h) = x(δ^{-1}h) ≠ x(h)`.
  - Checked. My part-1 note W4 is reflected.
- **Simplicity by the §1 proof.**
  - Points with trivial stabilizer in `B_{2w}` form the complement of a finite union of closed sets with empty interior, so they are dense.
  - A small `V` exists inside every nonempty clopen set, and §1's argument transfers with `u_ℓ`, `ℓV` and products in `L`.
  - This is what sk-review-7 part 1 established for `tower-simplicity-holds-for-topologically-free-actions`.
  - Checked; see W7 for the missing substitutions.
- **Finite models.**
  - The configuration attached to `(c,q)` is `x_{c,q}(h) = c(qψ_n(h))`.
  - For `ℓ = (δ,f)` and large `n`, `x_{σ_ℓ(c,q)}(h) = c(qψ_n(δ^{-1})ψ_n(h)) + Σ_{h′∈supp f}[ψ_n(h) = ψ_n(h′)] = x_{c,q}(δ^{-1}h) + f(h) = (ℓx_{c,q})(h)`, by partial multiplicativity and injectivity of `ψ_n` on the ball.
  - `σ_ℓ` is a bijection.
  - `σ_{ℓ_1}σ_{ℓ_2} = σ_{ℓ_1ℓ_2}` for large `n`. I checked both components, using `supp(δ_1f_2) = δ_1supp f_2`, `ψ_n(δ_2^{-1})ψ_n(δ_1^{-1}) = ψ_n((δ_1δ_2)^{-1})`, and that sums of indicators mod 2 agree because `ψ_n` is injective.
  - Covariance: `P_ℓD_n(f)P_ℓ^{-1} = D_n(f∘ℓ^{-1})` near `e`.
  - Every configuration is a pattern of the full shift, so `D_n` is well defined.
  - The map is a unital ring homomorphism into `∏_ωM_{|E_n|}(F_2)`, and units of `M_3` of the ultraproduct are the ultraproduct of the `GL_{3|E_n|}(F_2)`.
  - The kernel of `G →` the ultraproduct is normal and misses `e_{12}(1)`, so simplicity of `G` makes it trivial. This avoids needing simplicity of `R`, which covers my part-1 note W5.
  - Checked.
- **Embedding.**
  - Over `F_2`, `e_{12}(c)e_{21}(c^{-1}) = [[0,c],[c^{-1},1]]` and `·e_{12}(c) = [[0,c],[c^{-1},0]]`. Times `[[0,1],[1,0]]` this gives `diag(c,c^{-1})`.
  - `diag(a,a^{-1},1)diag(b,b^{-1},1)diag((ba)^{-1},ba,1) = diag(aba^{-1}b^{-1}, a^{-1}b^{-1}ba, 1) = diag([a,b],1,1)`.
  - So `ℓ ↦ diag(u_ℓ,1,1)` is a homomorphism sending commutators, and so `[L,L]`, into `G`. `Γ ≤ [Δ,Δ] ≤ [L,L]` with `Δ = {(δ,0)}`.
  - The false map `diag(a,a^{-1},1)` is not used as a homomorphism.
  - Checked.
- **(B′) universal host.**
  - F.g. linear groups are RF (Malcev) and countable up to isomorphism: they are subgroups of `GL_n` over f.g. commutative rings, which are quotients of `Z[x_1..x_m]` by finitely generated ideals.
  - F.p. groups are countable up to isomorphism.
  - A countable direct sum of RF groups is RF. Wilson Thm A gives a 2-generator RF overgroup, RF implies LEF, and the first corollary applies.
  - Checked.

**Notes.**
- **W6.** "generated by the units $u_s$ of the generators $s$ of $L$": ring generation needs `u_s^{-1}` as well. Write "the units $u_s^{\pm1}$" or take a symmetric generating set. (`u_a^{-1} = u_a` for the flip.)
- **W7.** The substitution list ("$u_\ell$ for $u^t$, $\ell V$ for $T^tV$, products in $L$ for sums of exponents, word length for $|t|$") leaves out the index set of the tower. Add "the ball $B_w$ for $\{a:|a|\le w\}$, so $d=3|B_w|$".
  - The `ε`-product rule then reads `ε_{αβ} = e_{αV}u_{αβ^{-1}}` with `α^{-1}α′ ∈ B_{2w}`.
  - Independence uses `αV ∩ α′V = ∅` for `α ≠ α′` in `B_w`.
  - The k-step uses `β^{-1} ∈ B_w` by symmetry of the ball. With this line the "word for word" rule is literally true. One line.
