# EX review, groups: part 14. Finite-dimensional nonsofic doubles, SFT crossed-product presentations, monomial models of the Kun–Thom wreath

Lane `ex-verify-groups`, 2026-09-13, ~02:40 CDT. Index: `ex-review-groups-2026-09-12.md`.

## 14.1 ex-fp-kazhdan-titz-witzel: `kun-thom-double-of-hyperbolic-pair-has-finite-cd` (19e19dbbdb). PASS

- **Nonsoficity.** The hypothesis of Kun–Thom Theorem A (import `kt-pair-group-double-is-nonsofic`) is that
  `Γ̂ <= Ĝ` are both Kazhdan, with `Γ̂` infranormal and not normal. It holds by
  `hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup`. So `D = Ĝ *_(Γ̂) Ĝ` is not sofic.
- **Torsion-free.** A finite subgroup of an amalgam is conjugate into a vertex group, and `G` is torsion-free.
- **Finite cd.**
  - A torsion-free hyperbolic group acts freely and cocompactly on a contractible Rips complex, so
    `c = cd G < ∞`.
  - Subgroups have `cd <= c`.
  - For `n + 1 > c + 1`, Mayer–Vietoris squeezes `H^(n+1)(D; M)` between zeros. So `cd D <= c + 1`.
- **Reading.** Theorem A doubles certify nonsoficity in finite cohomological dimension, unlike the
  commuting-factor and lamp certificates (part 13 §13.5–13.6). The node claims no priority, and a
  literature check was not possible there.

`cd-two-groups-have-no-infranormal-kazhdan-pairs` (a432d62afc, 366c69f26e) is OPEN with Attempts. It has no
route, so there is no verdict. Its proved pieces were checked:
- a strict compressor gives an ascending HNN extension;
- `cd H <= 2` forces `1 - φ^*` onto `H^2(Γ; A)`;
- when `H_2(Γ;Q)` is finite-dimensional, corestriction kills it, since `c φ_* = c` for an inner `c_t`.

## 14.2 ex-fp-kazhdan-ring: `sft-crossed-product-fp-iff-quantum-rigid` and `fp-subshift-crossed-products-are-sfts`. PASS at step level

Artifact `sft-crossed-product-presentation-rigidity-2026-09-13.md`, not read line by line. The node and route
outlines were re-derived.

- **Local presentations.** `A_D` imposes the length-`<= D` relations. A finitely presented `R_Ω` has
  finitely many relators, all consequences of `A_D` for large `D`. So finite presentation is equivalent to
  `A_D -> R_Ω` being an isomorphism for some `D`.
- **Only if.** A family `E` on `W` satisfying (Q1)–(Q3) defines a representation of `A_D` on finitely
  supported `W`-valued functions on `Z^2`: `e_a` acts at site `w` by `E_a(w)`, `u^g` translates, and
  `P_h^a` acts by `E_a(w+h)`. If `A_D = R_Ω`, all pattern idempotents commute in `R_Ω`, so all `E` commute.
- **If.** Left multiplication by `P_z^a` on `W = A_D` is such a family, so the `P`'s commute.
  - Stone duality makes the commutative algebra they generate a quotient of `LC(Y_D, k)`, with
    `Y_D = Ω` for `D >= r`.
  - The universal property of the algebraic crossed product inverts `A_D -> R_Ω`.
- **`fp-subshift-crossed-products-are-sfts`.** The diagonal sitewise action on `ℓ(Y_D)`-valued functions
  satisfies the relations of `A_D`. Through `A_D = R_X`, every pattern not occurring in `X` acts by zero,
  so `Y_D ⊆ X`. Hence `X = Y_D` is of finite type.
- **Scope, correctly recorded.** Neither claim produces a quantum rigid free minimal SFT. That remains the
  open gate of `fp-simple-kazhdan-linear-sofic-group-exists`.

## 14.3 ex-q34-kt-wreath-soft-kernel: `kt-wreath-monomial-models-kill-fibre-even-lamps` (28dd802138, 41947938e3). PASS at the combining step

- **Soft lamps.** `d_H <= ||.||_2^2/2` makes the permutation part a homomorphism with sofic image. So it kills
  `K_even = Rad_sof(W)` (import), and for block size 1, `ρ(K_even)` is diagonal.
- **The homomorphism.** For `F_2`-lamps, `e_Γ + e_(hh'Γ) = (e_Γ + e_(hΓ)) + (e_(hΓ) + e_(hh'Γ))`. The transport
  identity from `soft-kazhdan-central-elements-fixed-by-normal-closure` (Kun–Thom 4.1, import) is
  `ρ(e_(hΓ) + e_(hh'Γ)) = ρ(e_Γ + e_(h'Γ))`. So `f(hh') = f(h) f(h')`.
- **Conclusion.** `f` takes values in the abelian `ρ(K_even)`, and `N = EL_r(R)` is perfect, so `f = 1`. Pairs
  span the fibre-even configurations, and `G`-conjugation covers all fibres.
- **Not re-derived.**
  - The deep-congruence facts: normal closure `N`, and `s(Γ(m^k)) <= hΓh^-1` through Suslin's theorem.
  - The soft-Kazhdan import itself.
  - The trust surface of arXiv:2608.06222 travels with the claim, as the node says.
- **Consequence, correctly scoped.** The Kun–Thom wreath has no regular monomial model, which settles the model
  test on `monomially-hyperlinear-groups-are-sofic`. It gives nothing about hyperlinearity of `W`, and
  `q3-4-resolved` computes open.
