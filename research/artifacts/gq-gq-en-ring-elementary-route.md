# The elementary-group route to GL_n(Q) (lane gq-en-ring, 2026-09-17)

Target: `gl-n-q-embeds-in-fp-simple-group` (BBMZ Problem 5.3(5), literal). This lane owns
`E_N(R)` for rings `R ⊇ Q`: finite presentation via `St_N` and `K_2`, and simplicity for simple
`R`. It lands one conditional route and two established lemmas. They are lane proofs and not
independently reviewed.

## 1. What landed

| Node | Kind | Status | Content |
|---|---|---|---|
| `q-algebra-elementary-quotients-contain-gl-n-q` | claim | ESTABLISHED (elementary) | `Q ⊆ Z(R)`; `Z(E_N(R)) = E_N(R) ∩ Z(R)^x I`; `PSL_N(Q) ↪ PE_N(R)`; `GL_n(Q) ↪ PE_N(R)` for `N >= n+2`; `E_N(M_k R) = E_(Nk)(R)`, so `R ≅ M_2(R)` gives `PE_N ≅ PE_(2^j N)` |
| `rational-scalars-obstruct-fp-elementary-hosts` | claim | ESTABLISHED (obstruction) | `PE_N(R)` f.p. ⇒ `R` f.g. and `Λ_N(R) = {λ : λI_N ∈ E_N(R)}` f.g.; so `GL_N = E_N` kills it; `R^x/Z(R^x)` is never f.p. when `R^x` is f.g. or perfect |
| `q-algebra-with-fp-simple-projective-elementary-group` | claim | OPEN | one ring `R ⊇ Q` with `PE_N(R)` f.p. and simple for infinitely many `N` (one `N` if `R ≅ M_2(R)`), plus the list of necessary conditions |
| `gl-n-q-via-projective-elementary-hosts` | route | conditional | the open claim plus the embedding lemma ⇒ root |

## 2. The main finding: characteristic 0 needs a determinant

Over `F_2`, the fp simple Leavitt tensor hosts work *because* `K_1 = K_2 = 0`. Then
`GL = E = St` and the only scalars are `F_2^x = 1`. Over any ring containing `Q`, every
`λ ∈ Q^x` is a central scalar. If `λI_N` is elementary, it lies in `Z(E_N(R))`.
- A finitely generated group modulo a central subgroup is finitely presented only if that
  central subgroup is finitely generated (`fg-central-extension-of-fp-group-is-fp`).
- `Q^x` is not finitely generated.
- So any ring `R ⊇ Q` in which the rational scalars become elementary (for example
  `GL_N(R) = E_N(R)`, which is what vanishing `K_1` delivers) has `PE_N(R)` not finitely
  presented.
- The unit-group form is unconditional: if `R^x` is perfect or finitely generated, then
  `R^x / Z(R^x)` is not finitely presented.

This corrects the natural reading of the N4 spark in `gq-gq-k2-q-uniformity.md`. Killing all
Tate symbols stably, via `K_*(R) = 0` for `R ≅ R^2`, does not help, because it also makes the
rational scalars elementary. A usable ring host must keep a `K_1`-type invariant that sees
`λ^N` for all `λ` outside a finitely generated subgroup of `Q^x`.

## 3. Calibration (RULES §5; root O1–O3)

- **O1.** `E_N(R) ⊇ E_N(Q)` contains the divisible unipotents `e_12(q)`. So the non-residually-
  finite mechanism is the ring's divisibility, and it is not residually finite. Consistent.
- **O2, O3.** `SL_3(Z) ≤ E_N(R)` raises no issue: the host is not a Cantor or cube-complex
  group.
- **Distortion.** Unipotent distortion constrains nothing here. `E_N` of rings have
  distorted unipotents routinely.
- **"What does Q have that Z[1/m] lacks?"** Every prime inverted. Hence
  `fg-subrings-of-integral-form-algebras-omit-q`: the ring must be exotic, with
  multiplication producing unbounded denominators.

## 4. What the premise needs, by owner

1. A finitely generated simple ring `R ⊇ Q`. Lanes `gq-malcev-ring` and `gq-deep-ring-1`
   (operator rings with harmonic or inverse-number operators), `gq-ring-fp-simple`.
2. `Λ_N(R)` finitely generated. That is new here, and it binds item 1's constructions:
   a Toeplitz- or Leavitt-type operator ring with trivial `K_1` fails.
3. Finite presentation. For finitely presented `R` and `N >= 4`, finite normal generation
   of `ker(St_N(R) -> E_N(R))`, plus finitely generated central elementary scalars
   (`projective-elementary-fp-kernel-criterion`). The `St_N` finite-presentation statement is
   quoted in `gq-gq-k2-q-uniformity.md`. Its primary source was not read by this lane.
4. Simplicity of `PE_N(R)`. For simple rings of finite stable rank, Bass's sandwich
   classification is the classical tool. It must be read at the source before use. The
   field-coefficient Leavitt and Steinberg results on main do not cover a ring `R ⊇ Q` that
   is finitely generated.

## 5. Sparks (not pursued)

- **A finitely generated infinite division ring containing `Q`.** Whether any infinite
  division ring is finitely generated as a ring is, as far as this lane recalls, an old open
  question. It is not checked here. Such a `D` would have `PSL_N(D)` simple for `N >= 3`
  (Dieudonné). Its Dieudonné determinant must still detect `λ^N`. `D` cannot be finite-dimensional over its
  centre: by an Artin–Tate argument (as recalled), the centre would then be a finitely generated
  field, hence finite, and `D` finite by Wedderburn.
- **Relative determinant.** Build `R` as a finitely generated subring of a ring carrying a
  reduced-norm-type map to a commutative ring in which the image of `Q^x` stays free. The
  map kills `E_N(R)`, so it certifies that `Λ_N(R)` is finitely generated, as in part 5 of the
  obstruction.
