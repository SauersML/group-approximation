# Referee report (gq-referee-b, citation lens): torsion K_1 modulo central scalars kills scalar symbols

**Reviewed.** `torsion-k1-modulo-central-scalars-kills-scalar-symbols` and its `-proof` (lane gq-k2-q), read on
origin/main (af0cad75d).

**Verdict: PASS.** All three inputs are pinned at source:
- (C), which was unpinned, is now pinned to Weibel's *K-book*;
- (G), the lane's own read, is verified;
- (S) is my earlier pin, which applies unchanged.

Parts 1–3 are correct. The Pimsner reading is correctly marked conditional.

## (C), pinned

**Source.** C. Weibel, *The K-book*, Ch. III, §5, "Steinberg symbols", p. 42, read in the author's PDF.

- **The `⋆` pairing.** "If two matrices A, B ∈ E(R) commute, we can construct an element in K_2(R) by lifting their
  commutator to St(R). To do this, choose a, b ∈ St(R) with φ(a) = A, φ(b) = B and define A⋆B = [a, b] ∈ K_2(R).
  This definition is independent of the choice of a and b [...] The ⋆ symbol is also skew-symmetric and bilinear".
  - The same page proves `(PAP^(-1))⋆(PBP^(-1)) = A⋆B` for `P ∈ GL(R)`.
- **Definition 5.10.** "If r, s are commuting units in a ring R, we define the Steinberg symbol {r,s} ∈ K_2(R) to be
  diag(r, r^(-1), 1) ⋆ diag(s, 1, s^(-1)) = diag(r, 1, r^(-1)) ⋆ diag(s, s^(-1), 1)."
- **Example 5.10.1, p. 43.** "{r,s} = [h_12(r), h_13(s)] = [h_ij(r), h_ik(s)]", where
  `h_ij(r) = w_ij(r) w_ij(−1)`.

**Match.** This is exactly (C), and more.
- Weibel's definition holds for commuting units in **any** ring, not only a commutative one.
- So Part 1's step "`ν` and `x` lie in the commutative subring `Q̄[x^(±1)]`, where (C) identifies ..." is not needed.
  For `n = 1`, `Φ_ν(x) = diag(ν, ν^(-1), 1) ⋆ diag(x, 1, x^(-1))`, which is `{ν, x}` by Definition 5.10 directly.
  The detour is harmless.
- Part 1's `c(P,Q)` is Weibel's `⋆`, with the same lift-independence and bilinearity.

**Not pinned.** The identification of Weibel's `{r,s}` with the Dennis–Stein form `h_α(uv) h_α(u)^(-1) h_α(v)^(-1)`
(DS p. 249) is Milnor §9, which I did not read.
- The node needs only Weibel's form.
- The downstream symbol lemma, `infinitely-generated-symbols-block-fp-elementary-groups`, should use the same
  convention. If one convention is the inverse of the other, the groups generated are unchanged.

## (G), verified

Dennis–Stein, LNM 342, §15, p. 257, read at source: "It thus follows from a result of Garland [34] that K_2(O) is a
finite group [...] Quillen's localization exact sequence [73] yields 1 → K_2(O) → K_2(F) →λ ∐_𝔭 (O/𝔭)* → 1 and hence
K_2(O) = Ker λ which is known to be finite by Garland [34]."

**Match.** So `K_2(F)` is torsion for every number field `F`.

## (S), the Bass–Tate pin

Dennis–Stein §11(ii), p. 253: "K_2 of an algebraically closed field is a torsion free divisible group [...]
[5, (1.2)]". Here [5] is Bass–Tate, LNM 342. This is my pin in `gq-referee-b-algebraic-closure-kills-rational-steinberg-symbols.md`,
and it is correctly reused.

## Other inputs

- **(K) centrality.** Dennis–Stein p. 245, verified earlier. Also Weibel III, Theorem 5.2.1: "K_2(R) is an abelian
  group. In fact it is precisely the center of St(R)".
- **(W) Whitehead.** Standard. The facts `e_ij(r) = [e_ik(r), e_kj(1)]` for `n ≥ 3` and `diag(g, g^(-1)) ∈ E_(2n)` are
  elementary.
- **Filtered colimits.** Standard, and not pinned.
- **Morita invariance, a pin useful elsewhere.** Weibel III, Corollary 5.6.1: "the maps R → M_n(R) induce
  isomorphisms on K_2". This pins (M) of `euler-ring-symbols-in-small-finite-quotients` at source.

## Steps checked

- **Part 1.**
  - `A_ν` and `D_g` lie in `E_(3n)`: `D_g` is a block-permutation conjugate of `diag(g, g^(-1), I)`, and `E` is normal
    in `GL`. They commute because `ν` is central.
  - `g ↦ D_g` is multiplicative, and the result is bilinear, so `Φ_ν` is a homomorphism killing `E_n`, `n ≥ 3`.
  - Stabilization is compatible, and multiplicativity in `ν` holds.
- **Part 2.** `K_2(Q̄) = colim K_2(F)` is torsion, by (G), and torsion-free, by (S). So it is `0`.
- **Part 3.** `Φ_λ(y) = Φ_ν(y)^n = Φ_ν(ny) = Φ_ν(ι[μ]) = 0`.
- **Scope.**
  - "Only sufficient" is correctly stated.
  - The Pimsner section is labelled conditional on (P), and it uses the same (P) caveat as the gate.
