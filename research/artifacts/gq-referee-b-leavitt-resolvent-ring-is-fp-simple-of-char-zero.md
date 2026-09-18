# Referee report (citation/hypothesis lens): `leavitt-resolvent-ring-is-fp-simple-of-char-zero` and `fp-simple-ring-of-characteristic-zero-exists`

Referee: lane gq-referee-b, 2026-09-17. Reviewed:
- the claim and route `leavitt-resolvent-ring-is-fp-simple-of-char-zero(-proof)` at aaf4b1279;
- the existence node `fp-simple-ring-of-characteristic-zero-exists`;
- the two cited criterion nodes and their proofs: `leavitt-nekrashevych-completion-simplicity-criterion`
  (cda013b97) and `leavitt-nekrashevych-completion-embeds-and-is-fp` (cd95dd158).

## Verdict

**PASS** on correctness and hypothesis match.

The cited criterion is the one real trust surface. It is a lane proof, not a literature theorem, and it had no
review before this one. I checked the parts of it that this application uses (section 2 below). A1 and A2 record
this. The novelty statement stays bounded (A3).

## 1. Hypothesis match: `R_L ≅ O_ψ` for `B = Q[N][(N+c)^{-1} : c >= 1]` and `ψ(f) = diag(f(N+1), f(0))`

**The criterion's setting.** `K` is a field (`Q`) and `B` is a unital `K`-algebra. `ψ : B → M_d(B)` is a unital,
**injective** `K`-algebra homomorphism, with `d = 2`. The criterion has **no finite-generation hypothesis on
`B`**:
- the normal form of part 1 holds at level `N` for each fixed `y`;
- the saturation arguments and the minimal-support argument are all element-wise.

So the non-finitely-generated `B` is admissible.

**`ψ`. Correct.**
- `f ↦ f(N+1)` maps `B` into `B`, since poles at `−c−1` stay in the allowed set.
- `f ↦ f(0) ∈ Q`, since `N+c ↦ c ≠ 0`.
- Both are unital `Q`-algebra homomorphisms, so `ψ` is one.
- `ψ` is injective.

**`O_ψ → R_L`.**
- The integers are units in `R_L` by the `u_m` computation (checked), so `Q → R_L` is central and `R_L` is a
  `Q`-algebra.
- `Q[N] → R_L` sends every `N+c` to a unit. The image commutes with those inverses, so the map extends uniquely
  to `B`. The universal property of localization holds for maps into noncommutative rings once the image is
  commutative.
- `κ(b) = s_1 φ(b(N+1)) t_1 + s_2 φ(b(0)) t_2` is a unital ring homomorphism: the cross terms die by
  `t_1 s_2 = 0`. It agrees with `φ` on `N`, because `N = N(s_1t_1+s_2t_2) = s_1(N+1)t_1`, and on scalars. So it
  agrees on `B` by uniqueness, and covariance holds for all of `B`.

**`R_L → O_ψ`.** Covariance for `N` gives `N = s_1(N+1)t_1`, hence `Ns_1 = s_1(N+1)` and `Ns_2 = 0`.

**Both composites fix the generators.** On `B` they agree by uniqueness of localization maps.

**Ideals.** Ring ideals of a `Q`-algebra are `Q`-subspaces, so "simple as a ring" equals "simple as a
`Q`-algebra".

**Match: exact.**

## 2. The criterion's proof, as used here

Checked: `leavitt-nekrashevych-completion-simplicity-proof`, sections 1 and 3 (main direction).
- **Normal form.** The rewriting rules `b s_j = Σ s_i ψ(b)_ij` and `t_i b = Σ ψ(b)_ij t_j`, and padding. The
  coefficients are `t_μ y s_ν`.
- **Minimal support.** Shift the minimal degree to 0 with `t_α` or `s_1^{-m}`. Then `J_S` → `I_0`, a two-sided
  ideal of the core, closed under `t_i · s_j` and `s_i · t_j`. So `I_0 ∩ B` is ψ-saturated and nonzero, and
  ψ-minimality gives `1 ∈ I_0`. Aperiodicity gives `y = 1 ∈ J`.
- **Correct.** The main direction does not use the embedding theorem. It only needs that a nonzero `y_0` has a
  nonzero coefficient.
- Section 2(c) and the converse use the swindle proof of `B/I ↪ O_ψ̄`. I did not check that proof, and **this
  application does not need it**.

**Applications (§4, §5 of the route). Correct.**
- **ψ-minimality.** A nonzero `b ∈ I` gives `b(k) ∈ I ∩ Q` for all `k >= 0`, so `I = B`. This proves more: every
  nonzero ψ-invariant ideal is `B`.
- **Aperiodicity at level `L`.** The matrix-unit comparison gives `Y_{bω,ν} = δ_{νb} Y_{aω,a}`, so
  `y = Σ s_{νω} w_ω t_ν`.
- **At level `L+j`.** Padding puts the coefficient `ψ_u(w_ω)` at `(νωu, νu)`, and these index pairs are
  distinct. The comparison forces `ωu = uω'`.
- **Evaluation.** `ψ_{1^a 2 x}(w) = w(a)`, and one of the words `1^a21`, `1^a22` is not a prefix of `ω^∞`. So
  `w_ω(a) = 0` for all `a >= 0`, and `w_ω = 0`.
- **Faithfulness of coefficients.** The comparison needs `B → R_L` to be injective. The node's own model on
  `Q^(X)` gives this directly: `b` acts diagonally by `b(ℓ(ξ))`, and every `ℓ >= 0` occurs. So the swindle is not
  needed here either.
- **`k < 0`.** The anti-automorphism `s_i ↔ t_i`, identity on `B`, preserves covariance because `ψ(b)` is
  symmetric (diagonal) and `B` is commutative.
- **§6.** `M_2(R) ≅ R` via `(x_ij) ↦ Σ s_i x_ij t_j`. `SL_{n+2}(Q)` is perfect, so
  `GL_n(Q) ≤ [R^×, R^×]`. `diag(g, det g^{-1}, 1)` is non-scalar for `g ≠ 1`.

## 3. Is the criterion's source refereed?

**No.**
- The criterion is the repository's own lane proof (landed cda013b97, 2026-09-13).
- I found no earlier review artifact for it on main.
- The node says its graded-ideal part "parallels" Carlsen–Ortega, *Algebraic Cuntz–Pimsner rings* (Proc. LMS
  103 (2011); arXiv:0810.3254). That paper is refereed, but no theorem of theirs is used or quoted. The
  simplicity criterion (part 3) is not attributed to them.

**A1 (required).** Record on the criterion node that its main direction of part 3 and part 1 were checked in this
report. Record that 2(c), the converse, and the swindle behind `leavitt-nekrashevych-completion-embeds-and-is-fp`
part 2 remain unreviewed.

**A2 (recommended).** In the ring node, derive `R_L ≠ 0` and `B ↪ R_L` from the `Q^(X)` model, which is already
in the node, instead of from the embedding theorem. Then simplicity rests only on the checked parts.

## 4. Novelty (A3: keep the statement bounded)

Searched in addition to `gq-gq-lit-arxiv-priority.md` §6 (web and arXiv):
- Bokut (1976): f.g. simple envelopes.
- Belyaev (1978): f.p. envelopes, not simple.
- Evans–Mandelberg–Neff (1975). The survey `arXiv:2306.16356v3` §3 lists it only for "rings of characteristic
  p" (checked against the survey text).
- No source found stating that a finitely presented simple ring of characteristic 0 exists, or asking whether one
  does.
- **Not reachable:** the Dniester Notebook (the archive fetch was refused), the Kharlampovich–Sapir survey
  (IJAC 1995), and MathSciNet.

So:
- keep "no source found in a bounded search; possibly folklore via algebraic Cuntz–Pimsner rings";
- the existence node must **not** be described as answering a printed question;
- an expert check with MathSciNet should come before any public claim.

## 5. The existence node

The equivalences (a)⇔(b)⇔(c) of `fp-simple-ring-of-characteristic-zero-exists` are correct:
- the centre of a simple unital ring is a field;
- `e = p r = (p e) r = 0` if `p·1 = 0`.

Its ESTABLISHED status follows from the ring node, subject to A1–A3.
