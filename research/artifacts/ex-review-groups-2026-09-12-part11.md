# EX review, groups: part 11. Strong Atiyah hosts, and the post-review extras of the Pestov 9.1 group

Lane `ex-verify-groups`, 2026-09-13, ~02:00 CDT. Index: `ex-review-groups-2026-09-12.md`.

**Pointers for the coordinator's priority list.**
- ex-left-orderable-nonsofic's disjunction `non-rf-hyperbolic-group-or-unique-product-nonsofic-group` and
  `rf-hyperbolic-rigid-pair-host-gives-up-nonsofic-group` (the Delzant input) PASSED in part 2 §2.2 (a86f286657).
- `finite-simple-groups-converge-to-simple-kazhdan-group` was reviewed in part 8 §8.6. It had a GAP: the
  marking for non-prime `q`, corrected forward on both nodes in fbdc5f7011.

## 11.1 ex-atiyah-torsion-free: `two-variable-kun-thom-actor-satisfies-strong-atiyah` (004ae54ac2). PASS

**Step 1 (specialization).**
- There exist `u_1, u_2 ∈ 1 + pZ_p` algebraically independent over `Q`, since the countable algebraic closure
  of `Q(u_1)` misses some element.
- `ψ : x_i -> u_i` is an injective ring map `R -> Z_p`. `ψ(f) ≡ f(1,1) mod p`, so `ψ(K) <= CS(1,r,p)`, which is
  torsion-free for odd `p`.
- Farkas–Linnell Theorem 1.1, with Jaikin-Zapirain base change as quoted in the import, gives Strong Atiyah
  over `C` for `K`.

**Step 2 (free quotient).** `Γ_2(p)` is torsion-free for `p >= 3`. It injects into
`PSL_2(Z) = Z/2 * Z/3` and acts freely on the Bass–Serre tree, so it is free, hence locally indicable.

**Step 3.** Jaikin-Zapirain–López-Álvarez Proposition 6.5 (verbatim import, credited to Henneke–Kielak).
The domain consequence follows by embedding finitely generated coefficient fields in `C`.

**Step 4 (compression pattern).**
- `Γ_0` has finite index in `EL_r(Z[x_1,x_2])`, so it has (T) by Ershov–Jaikin-Zapirain, `r >= 3`.
- `α_A` for nonnegative `A` preserves polynomial rings and `K`.
- The image ring of `α_(A_1)` is spanned by `x_1^a x_2^b` with `a >= pb`, and it misses the entry `p x_2` of
  `e_12(p x_2) ∈ Γ_0`. So the compression is strict.
- Ping-pong shows `A_1, A_2` generate a free monoid.

Calibration, correctly recorded: the two-compressor non-Ore shape does not by itself force an Atiyah failure.

## 11.2 ex-atiyah-torsion-free: `double-ascending-hnn-strong-atiyah-reduces-to-kernel-tree` (004ae54ac2). PASS (reduction)

- **Splitting.** `π` is a retraction, and `s ↦ t_s` is a section, so `<t_s> ≅ F(S)` and `E = N x| F(S)`.
- **Torsion-free.** A finite subgroup fixes a vertex of the Bass–Serre tree, so it lies in a conjugate of
  the torsion-free `Γ`.
- **Kernel tree.**
  - `N \ T` is the Cayley tree of `F(S)`, and it lifts to a subtree.
  - The structure theorem gives the colimit of `Γ_w` with edge `{w, ws^-1}` carrying `Γ_w`, which sits in
    `Γ_(ws^-1)` as `t_(ws^-1) φ_s(Γ) t_(ws^-1)^-1`.
- **Growth by leaves.**
  - A child leaf's edge group is its whole vertex group, so the amalgam is trivial.
  - A parent leaf gives `N_Y *_(Γ_w) Γ_l` over a compressed copy.
- **Equivalences.** They follow from the induction formula, directed unions, and Proposition 6.5 for the free
  quotient.

Item 5 is correctly conditional on the open permanence `strong-atiyah-kazhdan-edge-amalgam-permanence`. This
is a reduction, not a theorem about the Fournier–Facio group, which has (T) and no locally indicable
quotient.

## 11.3 ex-kazhdan-simple-hyperlinear: `simple-kazhdan-lef-group-c-star-fails-llp` (da907cdf0f). PASS, conditional on imports

- `S` is infinite simple, so it is not residually finite. It is Kazhdan and LEF, hence hyperlinear (part 1).
- `llp-non-rf-kazhdan-group-is-non-hyperlinear` (baseline import) then excludes LLP for `C*(S)`.
- Kirchberg's theorem, as recalled in Thom 0810.2180 Theorem 1.1, gives that a Kazhdan group has the
  factorization property iff it is residually finite, so `S` lacks it.
- The Ozawa quote (math/0306067) is the source of Pestov's "Cf. Ozawa" in 9.1. The node is correct that `S`
  realizes that remark explicitly.

## 11.4 ex-kazhdan-simple-hyperlinear: `subshift-elementary-group-word-problem-degree` (a73f7f76cf). PASS

- **`WP <=_T L(X)`.** Entries are `Σ F_j u^j` with radius-`r` window tables. Products are local, and a table
  vanishes iff it vanishes on `L_(2r+1)(X)`, which the oracle decides. Scalars are detected the same way.
- **`L(X) <=_T WP`.**
  - `χ_w = Π_i u^-i χ_[a=w_i] u^i` is the cylinder of `w`, nonzero iff `w ∈ L(X)`.
  - `e_12(χ_w)` is a computable group word: `[e_13(a), e_32(b)] = e_12(ab)` and
    `[e_31(χ), e_12(u^i)] = e_32(χ u^i)`.
  - A nontrivial root is not scalar, so the same holds modulo the centre.
- **Sturmian degrees.** The rotation coding gives `L(X_α) <=_T α`. Balance of factors (`|#1 - nα| < 1`)
  gives `α <=_T L(X_α)`.
- **Classes.** Isomorphic finitely generated groups have Turing-equivalent word problems, which gives
  uncountably many classes of infinite LEF Kazhdan groups without finite quotients.
