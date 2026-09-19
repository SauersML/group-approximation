---
rg: 2
id: artin-2x2-dead-joins-sigma1-iff-k-q-odd-family-proof
kind: route
title: "Classification of Sigma^1 at the dead character of 2x2 dead joins: positive twisted Alexander rank from explicit matrix representations, plus the odd K_q membership"
target: artin-2x2-dead-joins-sigma1-iff-k-q-odd-family
requires:
  - artin-k4-odd-family-dead-characters-lie-in-sigma1
artifacts:
  - experiments/artin-join-sigma1-2026-09-17/general_constructions.py
  - experiments/artin-join-sigma1-2026-09-17/general_constructions.log
  - experiments/artin-join-sigma1-2026-09-17/certify_witness.py
  - experiments/artin-join-sigma1-2026-09-17/certify_witness.log
---

**Imported inputs** (verbatim; the same two imports as
`artin-k4-odd-family-dead-characters-lie-in-sigma1-proof`).

- **(I1) Sikorav.** A. Suciu, arXiv:2010.07499, abstract: "The
  Bieri-Neumann-Strebel-Renz invariants Σ^q(X,ℤ)⊂H^1(X,ℝ) of a connected, finite-type
  CW-complex X are the vanishing loci for Novikov-Sikorav homology in degrees up to
  q". We use `q = 1`, `X` the presentation complex below.
- **(I2) Bieri–Renz**, as stated in K. Almeida, arXiv:1605.00271v1, §1.1: "Theorem 1.2
  ([8]). Let G be a group of homological type F Pm and H be a subgroup of G containing
  the commutator [G, G]. Then H is of type F Pm if and only if S(G, H) := {[χ] ∈ S(G) |
  χ(H) = 0 } ⊂ Σ m(G, Z)." We use `m = 1`, `H = ker χ`, so `S(G, H) = {[χ], [-χ]}`.

**Notation.**
- `G = A_Γ` as in the target; `S_k(z) = 1 + z + ... + z^{k-1}`.
- `X` is the presentation 2-complex: generators `a, b, c, e`; relators `[a,b]`,
  `[c,e]` and `r_xy = (xy)^k (yx)^{-k}`, `k = h_xy`, for the four cross edges.
- `N_χ` is the Novikov ring: formal sums `Σ n_g g` such that for every `s` only
  finitely many `g` with `n_g != 0` have `χ(g) < s`.
- A *twisted module*: `F` a field of characteristic 0, `ρ : G -> GL_n(F)`, and
  `M = F(t)^n` (row vectors) with `v·g = t^{χ(g)} v ρ(g)`. Write `A, B, C, E` for
  `ρ(a), ρ(b), ρ(c), ρ(e)`, and `r(ρ) = dim_{F(t)} H_1(G; M)`.

(4) implies (1), (2), (3) is the required claim: it is stated for `(2, 2, 2, q)` with
`q` odd, and the label-preserving relabelings `a <-> b` and `c <-> e` fix `χ` and act
transitively on the four cross edges, so they move the odd half to any edge. It
remains to prove: if (4) fails, then `[χ], [-χ] ∉ Σ^1` and `ker χ` is not finitely
generated. By (I2) the last part follows from the first. The proof has three steps.

- **Step A.** Some twisted module with `r(ρ) > 0` forces `[χ], [-χ] ∉ Σ^1`.
- **Step B.** `r(ρ)` is computed by a small linear system.
- **Step C.** When (4) fails there is a `ρ` with `r(ρ) > 0`.

**Step A (positive twisted rank is an obstruction).** Let `r(ρ) > 0`.
- *Completion.* Put `M_+ = F((t))^n` and `M_- = F((t^{-1}))^n`, with the same formula
  for the action. Each is a field extension of `F(t)`, hence flat, and
  `M_± ⊗_{ZG} C_*(X̃) = (M ⊗_{ZG} C_*(X̃)) ⊗_{F(t)} F((t^{±1}))`. So
  `dim H_1(G; M_±) = r(ρ) > 0`.
- *Novikov action.* The rule `v·(Σ n_g g) = Σ n_g t^{χ(g)} v ρ(g)` makes `M_+` a
  right `N_χ`-module extending its `ZG`-module structure.
  - For each `k`, the coefficient of `t^k` is a finite sum over `χ(g) = k`.
  - Only finitely many `g` in the support have `χ(g) < 0`, so the exponents are
    bounded below.
  - Products in `N_χ` are convolutions, and they match products of series.
  - Likewise `M_-` is a right `N_{-χ}`-module.
- *Split exactness.* Suppose `H_0(G; N) = H_1(G; N) = 0` for `N = N_{εχ}`, in the
  convention of `artin-k4-odd-family-dead-characters-lie-in-sigma1-proof`, Step 1:
  the complex is `D = N ⊗_{ZG} C_*(X̃)`, made of free left `N`-modules.
  - Then `D_1 -> D_0` is onto a free module, so it splits. Its kernel `Z_1` is a
    direct summand of `D_1`, hence projective.
  - `D_2 -> Z_1` is onto a projective module, so it splits too.
  - Hence `M' ⊗_N D` is exact in degrees `0` and `1` for every right `N`-module `M'`.
    For `M' = M_ε` (with `M_1 = M_+`, `M_{-1} = M_-`) this reads `H_1(G; M_ε) = 0`.
    That contradicts the completion bullet.
  - So Novikov–Sikorav homology in degrees `<= 1` is nonzero for both `N_χ` and
    `N_{-χ}`.
- *Other side.* The anti-involution `g -> g^{-1}` of `ZG` carries `N_χ` onto `N_{-χ}`
  and exchanges left and right module conventions, as in Step 4 of the proof cited
  above. So the non-vanishing holds for both signs in the other convention too.
- By (I1), in whatever sign and side convention it is stated, `[χ] ∉ Σ^1` and
  `[-χ] ∉ Σ^1`. ∎(A)

**Step B (computing `r(ρ)`).** For `x ∈ {a,b,c,e}`, `x - 1` acts on `M` by the matrix
`t^{±1} ρ(x) - I`. Its determinant, as a polynomial in `s = t^{±1}`, has constant
term `(-1)^n`, so `x - 1` acts invertibly. Step 2 of
`artin-k4-odd-family-dead-characters-lie-in-sigma1-proof` uses only three things:
- that `a - 1`, `c - 1`, `1 - c` and `1 - e` act invertibly;
- that `a` commutes with `b` and `c` with `e`;
- the Fox rows.

So it applies verbatim to the right module `M` in place of `N`. (Its Fox rows are
derived for every half `k`: the `x`-entry of `r_xy` is
`S_k(xy) - S_k(yx) y = (1 - y) S_k(xy)`.) It gives

    H_1(G; M) ≅ M / Σ_{xy} M·(1 - y) S_k(xy)(x - 1),   x ∈ {a, b}, y ∈ {c, e}.

Since `1 - y` is invertible, `χ(xy) = 0` and `χ(x) = 1`, the subspace
`M·(1 - y) S_k(xy)(x - 1)` is the row space of `P_xy = S_k(XY)(tX - I)`. So

    (★)  r(ρ) = n - rank vstack(P_ac, P_bc, P_be, P_ae)
              = dim_{F(t)} { p ∈ F(t)^n : P_xy p = 0 for all four cross edges }.

The artifact computes `r(ρ)` a second way, as `4n - n - rank d_2` from the full
twisted Fox matrix of `X`, without using (★). The two agree on every witness it
certifies.

**Symmetries.** The relabelings below induce isomorphisms of `2x2` dead joins,
possibly with different halves:
- `α : a <-> b` and `β : c <-> e` fix `χ`;
- `γ : a <-> c, b <-> e` sends `χ` to `-χ`.

They generate the dihedral group of the square `a–c–b–e`, which acts transitively on
the vertices, on the edges, and on the pairs of opposite edges. `H_1` is transported
along an isomorphism. Replacing `χ` by `-χ` twists the scalars of `M` by the field
automorphism `t -> t^{-1}` of `F(t)`. So `r(ρ)` is invariant, and so are condition
(4) and the case conditions below. We may therefore normalise by these symmetries.

**Step C (witnesses when (4) fails).** Let `F = Q(ζ_L)`, `L` the lcm of the halves.
The roots of `S_h` are the `h`-th roots of unity other than `1`, and there are `h - 1`
of them.

*1-dimensional witnesses.* For `n = 1` every choice of scalars is a representation,
because `G^{ab}`-valued maps satisfy all relators. By (★), `r(ρ) = 1` iff
`S_k(ρ(x)ρ(y)) = 0` on every cross edge. (This is the commutative ring witness.)

*The cases.* Call a cross edge *short* if its half is `2`.
- **Case I: some vertex has both incident halves `>= 3`.** Normalise it to `e`, so
  `h_ae, h_be >= 3`.
  - If the halves are `(2, 2, 3, 3)`, use the scalars `a = b = 1`, `c = -1`,
    `e = ω` with `ω^2 + ω + 1 = 0`. The products are `-1, -1, ω, ω`, so each is a
    root of its `S_k`.
  - Otherwise use Construction 1.
- **Case II: every vertex lies on a short edge.** The short edges then cover the
  4-cycle. So either all four are short, or three are, or they form a perfect
  matching. Two adjacent short edges cover only three vertices.
  - *Four short edges:* `a = b = 1`, `c = e = -1`; every product is `-1` and
    `S_2(-1) = 0`.
  - *Exactly three:* the fourth half `q` is even, since (4) fails. Normalise that
    edge to `ae`, and use the same scalars. `S_q(-1) = 0` for even `q`.
  - *Perfect matching:* normalise (by `β`) to `h_ac = h_be = 2`, so the halves are
    `(2, q, 2, p)` with `q, p >= 3`.
    - If `q = p`, take a primitive `p`-th root `ζ` and the scalars `a = 1`, `c = -1`,
      `e = ζ`, `b = -ζ^{-1}`. The products are `ac = -1`, `bc = ζ^{-1}`, `be = -1`,
      `ae = ζ`.
    - If `q > p`, apply `α` and then `β`. This sends `(2, q, 2, p)` to `(2, p, 2, q)`.
    - If `3 <= q < p`, use Construction 2.

**Construction 1 (`n = 2`; `h_ae, h_be >= 3`, halves not `(2, 2, 3, 3)`).**

*Choice of roots.* Choose
- `ζ_1` a root of `S_{h_ac}` and `ζ_2` a root of `S_{h_bc}`;
- `x_1 != x_2` roots of `S_{h_ae}` and `y_1 != y_2` roots of `S_{h_be}` (possible,
  as `h_ae, h_be >= 3`);

with `Δ = ζ_1^2 y_1 y_2 - ζ_2^2 x_1 x_2 != 0`. This is possible:
- If `h_ac >= 3`, then `ξ` and `ξ^2` (`ξ = e^{2πi/h_ac}`) are roots with different
  squares. Fixing the other choices, at most one value of `ζ_1^2` gives `Δ = 0`.
  The case `h_bc >= 3` is the same.
- Otherwise `ζ_1 = ζ_2 = -1` and `Δ = y_1 y_2 - x_1 x_2`.
  - If `h_ae >= 4`, the pairs `{ξ, ξ^2}` and `{ξ, ξ^3}` (`ξ = e^{2πi/h_ae}`) have
    products `ξ^3 != ξ^4`, and one of them avoids `y_1 y_2`.
  - The case `h_be >= 4` is the same.
  - What is left is `h_ae = h_be = 3`, i.e. the excluded `(2, 2, 3, 3)`. There the
    only pair is `{ω, ω^2}`, so `Δ = 0` is forced.

*The matrices.* Put `α = x_1 x_2 / ζ_1` and `β = y_1 y_2 / ζ_2`, and
`A = diag(ζ_1, α)`, `B = diag(ζ_2, β)`, `C = I`. Solve
`ζ_1 u + α w = x_1 + x_2` and `ζ_2 u + β w = y_1 + y_2`; the determinant is
`ζ_1 β - α ζ_2 = Δ / (ζ_1 ζ_2) != 0`. Put `E = [[u, 1], [uw - 1, w]]`, so `det E = 1`.
- `AE` has trace `ζ_1 u + α w = x_1 + x_2` and determinant `ζ_1 α = x_1 x_2`. So its
  characteristic polynomial is `(z - x_1)(z - x_2)`, with distinct roots.
- Hence `(z - x_1)(z - x_2)` divides `S_{h_ae}(z)` and `z^{h_ae} - 1`. So
  `S_{h_ae}(AE) = 0` and `(AE)^{h_ae} = I`.
- Likewise `S_{h_be}(BE) = 0` and `(BE)^{h_be} = I`.

*Relations.*
- `[a,b]`: `A` and `B` are diagonal.
- `[c,e]`, `r_ac`, `r_bc`: `C = I` is central.
- `r_ae`: `(EA)^h = A^{-1}(AE)^h A = I = (AE)^h`. The relation `r_be` is the same.

*The witness.* `P_ae = P_be = 0`. `P_ac = S_{h_ac}(A)(tA - I)` and
`P_bc = S_{h_bc}(B)(tB - I)` are diagonal with first entry `S(ζ_i)(tζ_i - 1) = 0`. So
`p = e_1` satisfies (★) and `r(ρ) >= 1`. ∎

**Construction 2 (`n = p`; halves `(2, q, 2, p)`, `3 <= q < p`).**

*Permutations.* Index the basis by `Z/p` and let `M_σ e_i = e_{σ(i)}`, so
`M_σ M_π = M_{σ∘π}`. Let
- `f(i) = i + 1`, a `p`-cycle;
- `τ = (0 q)`, a transposition;
- `d = τ ∘ f^{-1}`, so `d(i) = τ(i - 1)`.

Then `d(1) = q` and `d(i) = i - 1` for `2 <= i <= q`, so `d` has the `q`-cycle
`(1 q q-1 ... 2)` on `{1, ..., q}`. Its other cycle is `{0, q+1, ..., p-1}`.

*The representation.* `A = I`, `C = -I`, `B = -M_d`, `E = M_f`.
- `A` and `C` are central, so every relation except `r_be` holds.
- `r_be` (`k = 2`): `(BE)^2 = M_{d∘f}^2 = M_τ^2 = I`. Also `(EB)^2 = M_{f∘d}^2 = I`,
  because `f∘d = f τ f^{-1}` is a transposition.

*The blocks.*
- `P_ac = (I + AC)(t - 1) = 0`.
- `P_ae = S_p(M_f)(t - 1) = (t - 1) J`, where `J` is the all-ones matrix.
- `P_bc = S_q(M_d)(-t M_d - I)`, since `BC = M_d`.
- `P_be = (I - M_τ)(-t M_d - I)`, since `BE = -M_τ`.

*The witness.* Let `v = e_1 - e_2` and `p = -(t M_d + I)^{-1} v`. The inverse exists:
the determinant is `1` at `t = 0`. Then `(-t M_d - I) p = v`, and:
- `P_bc p = S_q(M_d) v = 0`. `M_d` acts on `span(e_1..e_q)` as a `q`-cycle, so
  `S_q(M_d)` is the all-ones matrix there, and `v` has coordinate sum `0`.
- `P_be p = (I - M_τ) v = 0`, because `τ` fixes `1` and `2` (here `q >= 3` is used).
- `P_ae p = (t - 1) J p = 0`. Indeed `J M_d = J` gives `J (t M_d + I)^{-1} = (t+1)^{-1} J`,
  and `J v = 0`.

So `r(ρ) >= 1`. For `q = 2` the step with `τ` fails, as it must: `(2, 2, 2, p)` with
`p` odd is the odd `K_q` family. ∎

**Conclusion.** If (4) fails, Step C gives `ρ` with `r(ρ) > 0`. Step A then gives
`[χ], [-χ] ∉ Σ^1`, and (I2) gives that `ker χ` is not finitely generated. If (4)
holds, the required claim gives membership for both signs, and (I2) gives that
`ker χ` is finitely generated. ∎

**Remark R1 (rings do not suffice).** Take halves `(2, q, 2, p)` with
`gcd(q, p) = 1`, for example `(2, 3, 2, 5)`. Let `R` be a ring and `ρ : G -> R^×` a
homomorphism in which all four dead-edge sums vanish, as in
`artin-sigma1-dead-edge-ring-obstruction`. Then `R = 0`:
- `1 + ρ(a)ρ(c) = 0` gives `ρ(c) = -ρ(a)^{-1}`. Likewise `ρ(e) = -ρ(b)^{-1}`.
- `y = ρ(bc) = -ρ(b)ρ(a)^{-1}` then satisfies `ρ(ae) = -ρ(a)ρ(b)^{-1} = y^{-1}`, as
  `ρ(a)` and `ρ(b)` commute.
- `S_q(y) = 0` gives `y^q = 1`, since `(y - 1) S_q(y) = y^q - 1`.
  `S_p(y^{-1}) = 0` gives `y^p = 1`. So `y = 1`.
- Then `q·1 = S_q(1) = 0` and `p·1 = 0`, so `1 = 0`.

Still `[±χ] ∉ Σ^1` by Construction 2. So the dead-edge ring criterion does not
characterise non-membership, even for these groups. The surviving criterion is
positive twisted Alexander rank. The 1-dimensional witnesses of Step C are
commutative ring witnesses. Construction 2 with `gcd(q, p) = 1` cannot be replaced
by any ring witness, commutative or not.

**Remark R2 (how the witnesses were found; not used in the proof).** The artifact
directory also contains the searches that found the first module witnesses:
- `perm_rank_search.py`: an `S_6` witness for `(2, 3, 2, 4)`;
- `signed_opposite_search.py`: signed `S_5` witnesses for `(2, 3, 2, 5)` and
  `(2, 5, 2, 3)`;
- `opposite_trivial_a_search.py` and `twisted_rank_search.py`: searches with
  `ρ(a) = 1` and over `GL_2(F_l)`.

Constructions 1 and 2 generalise what those searches found.

**Artifact checks** (`general_constructions.log`, `certify_witness.log`).
- Part A is exact, over `Q(t)`. For Construction 2 and all `3 <= q < p <= 9` it
  checks:
  - all Artin relations;
  - the cycle type of `d`;
  - that `p(t)` is nonzero and killed by all four blocks.

  The controls `(2, 2, 2, 3)` and `(2, 2, 2, 5)` give a reduced kernel of dimension
  `0`, as the odd `K_q` family requires.
- Part B is numerical, in complex floating point. It checks Construction 1 on all
  399 halves with `h_ac, h_bc ∈ [2, 6]` and `h_be, h_ae ∈ [3, 6]`, other than
  `(2, 2, 3, 3)`:
  - the relations;
  - that `e_1` is killed;
  - that the full Fox rank of `H_1` is `>= 1` at a random `t`.

  It also confirms that no admissible choice of roots exists for `(2, 2, 3, 3)`.
- The Fox part is exact. It computes the full twisted Fox matrix for Construction 2
  at `(2, 3, 2, 4)`, `(2, 3, 2, 5)` and `(2, 4, 2, 5)`, giving `r = 1, 1, 2`. It
  does the same for the `S_6` and signed `S_5` witnesses.
