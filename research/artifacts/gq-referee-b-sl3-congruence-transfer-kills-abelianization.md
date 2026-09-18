# Referee report (citation/hypothesis lens): `sl3-congruence-transfer-kills-abelianization` and `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`

Referee: lane gq-referee-b, 2026-09-18. Reviewed as landed at f9dbfcd34:
- the transfer node and its `-proof`, in full;
- in the Toeplitz node, the two citations and the Loday step of part 6 of its `-proof`.

## Verdicts

- **(1) Transfer node: PASS.** The Lee–Szczarba quotation is verified at the named secondary source, and every step
  of the proof checks.
- **(2) Cecchi Bernales–Cortez–Gómez: PASS.** The theorem is verified verbatim at arXiv, including the measure
  conjugacy, and the hypotheses are met.
- **(3) Loday product: PASS as a named trust surface.** A web excerpt of Weibel Ch. IV supports only the
  commutative-ring version. The general-ring version used here is Loday (1976), which nobody has read.

## (1) Lee–Szczarba and the transfer

**Source.** Imoto–Kobayashi, *Note on the level d principal congruence subgroup of SL(n,ℤ)*, arXiv:2212.13181v2,
arXiv HTML.
- Theorem 1.1, verbatim: "For n≥3 and d≥1, the abelianization of Γ_d(n) is isomorphic to (ℤ/dℤ)^{n²−1}."
- The same text records that Lee–Szczarba constructed "an epimorphism Γ_d(n) → (ℤ/dℤ)^{n²−1} whose kernel equals
  Γ_{d²}(n)", and that **"Γ_{d²}(n) = [Γ_d(n), Γ_d(n)] for d ≥ 2 and n ≥ 3"**.
- Reference [9]: R. Lee, R. H. Szczarba, Invent. Math. 33 (1976), no. 1, 15–53. The primary was not read.
- The node's deduction of `[Γ_d,Γ_d] = Γ_{d²}` is therefore also stated directly in the source. **Suggestion:** quote
  that sentence.
- `θ_d` induces `Γ_d/Γ_{d²} ≅ sl_n(Z/d)`. It is injective because its kernel is `Γ_{d²}`, and bijective because
  both sides have order `d^{n²−1}`.

**Proof checks.**
- **Transfer evaluation.** Isaacs, *Finite Group Theory*, Lemma 5.5: `V(x) = Π t^{-1}x^f t`. The `⟨x⟩`-orbits on
  `G/H` have length `f`, the order of `xH`, because `H` is normal. The representatives run over `G/⟨x⟩H`, so
  `|T| = d^N/f`.
- **The power of `x`.** `fX = dW_1` gives `x^f = I + d^2 W` with `W = W_1 + C(f,2)X^2 + d(…)`, and `W` commutes
  with `X`. **Correct.**
- **Conjugates.** `t^{-1}x^f t = I + d^2 t^{-1}Wt`, and `t^{-1}Wt ≡ W + d[W,Y_t] mod d^2`. **Correct.**
- **The sum.** `|T|` is a multiple of `d^{N−1}`, and `N − 1 >= 7`, so `|T|W ≡ 0 mod d^2`.
  - The `Y_t mod d` represent `B/A`, so `S mod d` lies in `Σ_Q q + A`.
  - `Σ_Q q = 0`. For `d` odd, `Q[2] = 0`. For `d` even, `rank Q[2] = rank Q/2Q >= N−1 >= 2`, since `A` is cyclic.
  - So `S ≡ jX`, and `[W,S] ≡ 0 mod d`. **Correct.**
- **Conclusion.** `θ_{d²}` is injective on `H^ab`, by the theorem at level `d²`. So `V = 0`.
- **Part 2.** Transfers compose, and the levels `d^2 | e` are cofinal. Shapiro's lemma gives
  `H_1(Γ; Z[Γ/Γ_d]) ≅ H_1(Γ_d)`, and the pullback maps of locally constant functions correspond to transfers.
  Homology commutes with filtered colimits.
  - The limit is `SL_n(Ẑ)` because `SL_n(Z) → SL_n(Z/d)` is onto for every `d`. That is strong approximation, a
    standard fact.
  - **Correct.** It is "standard, not written out", as the node says.

## (2) Cecchi Bernales–Cortez–Gómez

**Source.** Cecchi-Bernales, Cortez, Gómez, *Invariant measures of Toeplitz subshifts on non-amenable groups*,
arXiv:2305.09835v2, arXiv HTML. Theorem 1.3, verbatim:
> "Let G be a countable residually finite group and let G← be a totally disconnected metric compactification of G
> equipped with the action of G by left multiplication. For every integer r>1 there exists a Toeplitz G-subshift
> X⊆{1,…,r}^G with at least r ergodic probability measures ν₁,…,νᵣ, and whose maximal equicontinuous factor is G←.
> Furthermore, for every 1≤i≤r, we have the following: (1) (X,σ,G,νᵢ) is measure conjugate to G← endowed with the
> Haar measure."

"Measure conjugate to Haar" **is in the published statement**, as item (1).

**Hypothesis match.**
- `SL_3(Z)` is countable and residually finite.
- `Γ_n = Γ((n+1)!)` is a chain of normal subgroups of finite index, decreasing since `(n+1)! | (n+2)!`, with
  trivial intersection.
- The odometer `lim Γ/Γ_n` is the paper's `G←` for that sequence. It is a totally disconnected metric
  compactification, with `G` acting by left multiplication.
- The action is free on the odometer: `gxΓ_n = xΓ_n` forces `g ∈ Γ_n`.
- Toeplitz subshifts are minimal almost 1-1 extensions of `G←`.
- **It matches.** The node's quotation omits the first sentence, which carries the hypotheses. Quote it.

## (3) Loday product (part 6, step 5)

- The use is `[λ]·[v] = ±{λ, v}` in `K_2(Q ⊗ R_T) = K_2(R_T)`, for `λ ∈ Q^×` central and `v ∈ R_T^×`, together with
  naturality and associativity of the products.
- A web excerpt of Weibel, *The K-book*, Ch. IV (Rutgers PDF), states that the Loday product is "natural in A and
  B, bilinear and associative". It agrees with Steinberg symbols for units **of a commutative ring**.
- The PDF itself did not decode, so the number IV.1.10 is unconfirmed.
- The general version, for `[a] ⊗ [b] ↦ {a⊗1, 1⊗b}` in `K_2(A ⊗ B)`, is Loday (Ann. Sci. ENS 1976), which nobody has
  read. `R_T` is not commutative, so the general version is the one needed.
- **Keep T3 as a named trust surface.** State that it needs the general-ring form.
- The rest of part 6 checks:
  - the class of a monomial matrix is `sgn`-class plus the sum of the entry classes;
  - `h ↦ χ_{C'}u_h` is a homomorphism on `Γ(d²)`;
  - `Π h_s` is the transfer `V(γ)`, which vanishes by (1);
  - `[v] = ε·[χ_{C'}]`.

## Not reviewed

Parts 1–5 of the Toeplitz node (generation, simplicity, the K1 statements, matricial divisibility) are proof-gap
matters. They also rest on `harmonic-elimination-puts-q-in-odometer-crossed-products` and
`matricial-divisibility-kills-rational-k2-symbols`, which this report did not review.
