# Adversarial check: every free centre-by-metabelian group is linear (bh-verify-cbm, 2026-09-18)

**Claim checked:** `free-centre-by-metabelian-groups-are-linear`. For every `n`,
`C_n = F_n/[F_n'', F_n]` is linear over `Q(x_1..x_n)`, residually nilpotent and residually finite, so it is in
`B_A`. The chain was landed by bh-free-28 (c20193cd0, 386fd7a93, e732575e5, 93c623957, d7009bd9b, a5552e32f).

**Nodes read** (at origin/main 2d0ca54dc):
- `free-centre-by-metabelian-linear-modulo-exterior-square-kernel`: the construction.
- `free-centre-by-metabelian-corner-kernel-is-the-torsion`: `K_n = T_n`, `K_3 = 0`, the structure of `T_n`.
- `gupta-torsion-element-survives-modulo-gamma-seven` and its `-citation`.
- `free-centre-by-metabelian-linearity-via-gamma-seven-quotient`: the route.
- `free-centre-by-metabelian-rank-two-linearity-proof` and `free-centre-by-metabelian-groups-linear-iff-residually-finite`.

## Verdict: PASS, with one false lemma repaired

- **The main theorem stands:** linear in characteristic 0, residually nilpotent, residually finite, in `B_A`, for every `n`.
- **The false lemma** is in route step 3: "every nontrivial subgroup of a cyclic group of even order contains
  its involution". That is false, since `Z/3 ≤ Z/6`.
- **With Kuz'min's `d = 2`** (cited, not read), step 3 holds as written, and so does the stated bound
  `T_n ∩ γ_7(C_n) = 1`.
- **Without Kuz'min,** §5 gives a repair that uses only the Gupta–Levin lemmas that were read at source. It
  proves the theorem with `γ_c` for some finite `c ≥ 7` in place of `γ_7`.
- **What I did:** I recorded this as an Attempts note on the route node. I changed no mathematics in anyone's text.

## 1. Construction and kernel = torsion (item 1 of the brief)

Notation: `F` is free on `x_1..x_n`, `G = Z^n`, `R = ZG`, `t_i = x_i − 1`, `P = R^n`, and
`M = F'/F'' = ker(P → R, e_j ↦ t_j)` via the Magnus map `b`.

- **The corner block.** Write the product law for the blocks `[[I_n, α, γ], [0, g, β], [0, 0, I_n]]`. It gives
  the recursion `α(uv) = α(v) + α(u) g(v)`.
  - `b̃_j(w) := \overline{b_j(w^{-1})}` satisfies the same recursion, with `b̃_j(x_i) = −x_i δ_ij`.
  - So `α_j = −x_j^{-1} b̃_j`. On `F'` this gives `α_j = x_j^{-1} \overline{b_j}`, which checks.
  - The commutator of two elements with `g = 1` has corner `α(u)β(v)^T − α(v)β(u)^T`.
  - So on `F''` the corner is `Φ(b ∧ b)` with `Φ(β ∧ β')_{jk} = x_j^{-1}(\bar β_j β'_k − \bar β'_j β_k)`, as claimed.
- **`Φ` is injective on `(Λ²P)_G`.** `G` acts freely on unordered pairs of distinct `Z`-basis vectors: `g`
  swapping `m f_i` and `m' f_j` forces `g² = 1`. So `(Λ²P)_G` is free abelian on the orbit classes.
  - The images of those classes have pairwise disjoint (position, monomial) supports, above the diagonal,
    below it and on it. Checked.
- **Identification with coinvariants.** `F''/[F'', F] ≅ (Λ²_Z M)_G` holds because `F'` is free, so
  `γ_2/γ_3 = Λ²` of its abelianization, and the `F`-action factors through `G`. Checked.
  - Hence `K_n = ker((Λ²M)_G → (Λ²P)_G)`.
- **`T_n ⊆ K_n`.** If `ρ(w)^m = 1`, then `g^m = 1`, so `g = 1`. Then `m N + C(m,2) N² = 0` with `N² = 0` off
  the corner, which forces `α = β = 0` and then `γ = 0`. So the image is torsion-free. `T_n` lies in
  `F''/[F'', F]`, because `F/F''` is torsion-free.
- **`K_3 = 0`, the new step.** I re-derived every line.
  - `D u = u × t` is Koszul `d_2`. Since `t` is a regular sequence, `D(N) = M` and `ker D = R t`.
  - `(Λ²R^k)_G ≅ Sk_k` via `S(u,v) = ū v^T − v̄ u^T`. Diagonal entries are `λ − λ̄`, because `G` is torsion-free.
  - Right-exactness gives `(Λ²M)_G = Sk_3/W` with `W = {S(t, v)}`.
  - `D^T = −D`, so the kernel condition `D̄ X D^T = 0` is the node's `D̄ X D = 0`.
  - The columns of `XD` lie in `ker D̄ = R t̄`, which gives a Koszul 1-cocycle in `N' = R^3/R t̄`.
  - `H^1(t; N') ≅ H_2(G; N') = 0` from `0 → R → R^3 → N' → 0`.
  - So `X = β t^T + t̄ μ^T`. Skew-hermitian forces `a = β̄ + μ = c t` with `c ∈ R`: `gcd(t_i) = 1`, and `c̄ = −c`.
  - Hence `X = S(t, −β̄ + λ t) ∈ W`, with `c = λ − λ̄`. I verified this last identity by expansion. **PASS.**
- **Step 3 for all `n`.** The filtration of `Λ²P` gives `0 → M⊗I → Q → Λ²I → 0`, where `Q = Λ²P/Λ²M`.
  - `M` is a `Z`-direct summand of `P`, because `P/M = I` is free abelian.
  - `Λ²P` and `Λ²R` are `ZG`-free, and `M ⊗ ZG` is induced.
  - Dimension shifting gives `H_1(M⊗I) ≅ H_2(M) ≅ H_3(I) ≅ H_4(G) = Λ^4`, `H_2(Λ²I) ≅ Λ^4` and `H_1(Λ²I) ≅ Λ^3`.
  - So `Λ^4 →δ Λ^4 → K_n → Λ^3` is exact.
  - The retraction and inclusion naturality arguments hold: `r_S` induces coordinate projections on `Λ^3` and
    `Λ^4`. They kill the `Λ^3` part, using `K_3 = 0`, and make `δ` the scalar `d`.
  - So `K_n ≅ (Z/d)^C(n,4)`, with `(r_S)_S` an isomorphism onto `⊕ T_4`. **PASS.**

## 2. The Gupta–Levin input (item 2)

I read Gupta–Levin, Illinois J. Math. 30 (1986), from the Project Euclid PDF, pp. 258–261 and 266–267. The
page images were read directly.
- **p. 260 (i).** `K_6(F)` is the fully invariant closure of `u_6`.
  - `u_6` is six weight-6 terms `[f_{1τ}, f_{2τ}; f_{1τ}, f_{2τ}, f_{3τ}, f_{4τ}]`, with `1τ < 2τ` and `3τ < 4τ`.
  - It is multiplied by eight weight-7 terms of the shape `[f_a, f_b, f_c; f_a, f_b, f_d, f_c]`, which lie in `γ_7(F)`.
  - The node's "product of 12 commutators of weight 6" is a miscount (6 of weight 6 plus 8 of weight 7; the citation node's "six further terms" should read eight). This
    is harmless; see the next point.
- **p. 261, Lemma 2.2.** Credited to C. K. Gupta: (i) `F ∩ (1+faf) = K_6(F)[F'', F]`; (ii) `K_6 ⊆ [F'', F]`
  iff rank `≤ 3`; (iii) `u² ∈ [F'', F]` for `u ∈ K_6`. The quotations match.
- **p. 266, Lemma 4.4.** The statement matches the citation node verbatim. The proof on p. 267 assumes
  `u ∈ 1 + r + f^7`, reduces to a component equation, and shows it has no integral solution. I read it and
  found no gap at the level of the argument.
  - The weight-6 part of `u_6` is exactly a product of distinct lemma-type terms. So Lemma 4.4 applies to it
    directly, and `u_6 ∉ 1 + r + f^7`, since the weight-7 factors lie in `1 + f^7`.
  - This bypasses the full-invariance argument in the citation node, which is also valid.
- **The derivation in the citation node.** It is correct:
  - `[F'', F] γ_7(F) ⊆ 1 + r + f^7`, where the `ab − 1` identity uses that `r` is an ideal;
  - the retraction to `F_4` fixes `u_6`;
  - `[F_4'', F_4] γ_7(F_4) ⊆ [F'', F] γ_7(F)`.

  So `u_6` has order 2 in `C_4` and lies outside `γ_7(C_4)`. **PASS.**

## 3. Torsion structure (item 3)

- **Internally proved:** `T_n = K_n ≅ (Z/d)^C(n,4)`, with `d` even and `d ≠ 0`. Evenness comes from `u_6`.
  `d = 0` would make `K_4 ≅ Z` torsion-free, a contradiction.
- **Not internally proved:** `d = 2`. That is Kuz'min 1977, `T_n ≅ H_4(F/F') ⊗ Z/2`. I checked it only through
  secondary statements, a 2023 *Comm. Algebra* abstract and the 1986 introduction (elementary abelian
  2-subgroups). It is standard, and consistent with the internal rank `C(n,4)`. Not read at source.

## 4. The final embedding (item 4), and the flaw

- **The embedding argument.** `ker(C_n → ρ_n(C_n) × C_n/γ_c(C_n)) = T_n ∩ γ_c(C_n)`. The retraction argument
  from `n ≥ 5` down to `n = 4` is correct for any fixed `c`.
- **The flaw.** For `c = 7`, route step 3 needs `T_4 ∩ γ_7(C_4) = 1`. The node derives this from "every
  nontrivial subgroup of a cyclic group of even order contains the involution", which is false.
  - The step is valid once `|T_4|` is a power of 2. So it holds under Kuz'min's `d = 2`.
- **The remaining steps hold.** The linearity step (`ρ_n` over `Z[x^±]`, `C_n/γ_c` polycyclic, hence
  `Z`-linear by Auslander–Swan), Mal'cev, and the `B_A` step via the characteristic-0 linear node are correct.

## 5. Kuz'min-free repair (proved here, elementary from the inputs above)

1. **Only involutions survive every `γ_c`.** Let `θ` be Hurley's map.
   - `θ(γ_c(F)) ⊆ 1 + P_{≥c}`, and `θ` kills `[F'', F]`. So `∩_c γ_c(C_n) ⊆ ker(θ|C_n)`.
   - By Lemma 2.2(i), `ker(θ|C_n) = K_6(F_n)[F'', F]/[F'', F]`.
   - By 2.2(iii), and because `K_6 ⊆ F''` is central mod `[F'', F]`, this is elementary abelian of exponent 2,
     and it lies in `T_n`.
2. **`n = 4`.** `T_4` is cyclic, so its exponent-2 subgroups have order at most 2.
   - So `ker θ ∩ T_4 = {1, u_6}`, which is nontrivial because `u_6 ∉ [F'', F]`.
   - Since `u_6 ∉ γ_7(C_4)`, we get `T_4 ∩ ∩_c γ_c(C_4) = 1`.
3. **All `n`.** Retractions give `T_n ∩ ∩_c γ_c(C_n) = 1`, and then `∩_c γ_c(C_n) = 1` by step 1. So `C_n` is
   residually nilpotent, with no use of `d = 2`.
4. **Some finite `c` suffices.** `T_n` is finite, so the chain `T_n ∩ γ_c` stabilizes at `1` for some `c`.
   Then `C_n ↪ ρ_n(C_n) × C_n/γ_c(C_n)`, and both factors are linear. `c = 7` exactly when `T_4 ∩ γ_7 = 1`,
   for instance if `d = 2`.

**Robustness.** The theorem (linear, RN, RF, `B_A`) needs only four inputs: `K_n = T_n` (proved and
re-checked), Hurley's `θ` with `Ker θ = faf`, Lemmas 2.2(i),(iii) and Lemma 4.4. All four were read at source
today.

## 6. Priority (bounded: 5 web and arXiv queries plus 2 page fetches)

- **Kofinas, arXiv:2603.27648 §2.3 (read in HTML).** "Although this fails for n≥4, it is true for n=3". This
  is about faithfulness of Hurley's embedding, not about residual nilpotence being open.
- **C. K. Gupta 1973, abstract.** For `n ≥ 4`, `C_n/H_n` is 3×3-linear with `H_n` finite. So the whole
  question was residual separation of a finite central `H_n`.
- **Update (same day): both 1976 papers were fetched through MSI and read.**
  - N. D. Gupta–Wehrfritz, Arch. Math. 27 (1976) 449–455, doi:10.1007/BF01224698, md5 `3b7401f7…`.
  - N. D. Gupta–Levin, Comm. Algebra 4 (1976) 249–270, doi:10.1080/00927877608822105, md5 `2ffc8d47…`.
  - Copies are in `$GQ/src/bh-verify-cbm/` and `gqsrc/bh-verify-cbm/`.
- **The theorem is known.** Gupta–Wehrfritz p. 454, Remark 3: "Every free centre-by-metabelian group of
  finite rank has a faithful representation of finite degree (depending on the rank) over the ring R_0". Their
  facts (ii) and (iii) on p. 454 are credited to C. K. Gupta 1969/1973:
  - the torsion is elementary abelian of rank `C(r,4)`, which confirms `d = 2` independently of Kuz'min;
  - `F/[F'', F]` is residually a finite 2-group.
- **Gupta–Levin 1976** is about separating laws for the nilpotent quotients, so it is not relevant here.
- **Verdict on priority.** bh-free-28's chain is a new, explicit proof of a 1976 theorem: an explicit
  corner representation, a homological kernel computation, and a nilpotent patch. It is not a new result. The
  node's priority line is updated to say so.

## Lesson for general BH

- **What the method is.** Linearity here comes from a two-part template. First, an explicit representation
  whose kernel is computed exactly by group homology (Koszul resolutions plus coinvariants of exterior powers).
  Second, patching the finite central kernel with a nilpotent (finite-type) quotient that detects it.
- **What it transfers to.** Any explicit host (linear, RSG, full group) whose kernel on `G` is a finite normal
  `K` gives BH for `G` exactly when some finite, or `B_A`, quotient of `G` is injective on `K`. The kernel's
  homological description decides whether such a quotient exists.
- **Where it stops.** The limits of this method are exactly the groups whose finite central kernel dies in every
  finite quotient: Deligne lattices, `Q_{g,c}`, and bh-lattices' finite central extensions. So the general BH
  frontier here is closure of `B_A` under finite central extensions that are not residually separated, not the
  representation theory.
