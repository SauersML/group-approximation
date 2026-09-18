# Referee report (citation/hypothesis lens): `one-steinberg-group-contains-every-gl-n-q` and route `gl-n-q-explicit-via-st-4-of-divisible-ring`

Referee: lane gq-referee-b, 2026-09-17. Reviewed: the claim, its Attempts 1 proof (a)–(e), and the route, as
landed at 27d360184.

## Verdict

- **Claim: PASS.**
- **Route: PASS conditional on A3.** The route currently rests on the unreviewed ring `D`. The already refereed
  `R_L` works in its place.

Every step of (a)–(e) checks. The cited inputs are correctly used:
- one is verified at source;
- one is a verified secondary quotation;
- the rest are classical textbook theorems that I did not read at the primary. The node itself flags this.

## Steps checked

**Cuntz families from a Leavitt pair.**
- `t_k = x_2^{k-1}x_1` for `k < m`, and `t_m = x_2^{m-1}`.
- Orthogonality `t_k^*t_l = δ_kl` follows from `y_2x_2 = 1` and `y_1x_2 = y_2x_1 = 0`.
- `Σ t_kt_k^* = 1` telescopes through `x_1y_1 = 1 − x_2y_2`.
- `ι_m` is a unital ring map because `Q` is central.
- `t_k^* ι_m(a) t_l = a_kl` gives injectivity.
- The Leavitt pair of `D`, `(w, sw; v, vt)`, is as stated. I checked it from the identities given in the node, not
  against the node for `D`.

**(a) The block map `β_k`.**
- It is a homomorphism by the block-expansion argument, which I verified in
  `gq-referee-b-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md`.
- It is an isomorphism for `k >= 2`:
  - `St_4(M_k(Q)) → SL_{4k}(Q)` is a perfect central extension;
  - `St_{4k}(Q)` is universal (`4k >= 8`);
  - an endomorphism of a perfect central extension over the identity is the identity.

**(b)**
- `b_N` is the block expansion for `q ↦ qI_N`, so it is a homomorphism.
- `b_N(y) = ∏_c ŝ_c(y)` for **every** `y`, not only for `y ∈ K_2`. The `ŝ_c` have disjoint index sets and commute
  elementwise.
- On `K_2(4m,Q)`, the index independence of symbols gives `ŝ_c = ŝ_1`.

**(c), (d), (e).**
- `t_i u_c` is a Cuntz family of size `mN`, and `ι_m = ι_{mN} ∘ j_N`.
- `β_m(x)` has finite order `N`. `β_{mN}` is injective, and the conclusion follows.

## Citations

**(1) Centrality of `K_2(n,A)` for `n >= sr(A)+2`. Verified at source.**
- Voronetsky, *Centrality of K₂-functor revisited*, arXiv:2004.08551v2, introduction, verbatim: "From surjective
  stability for K₂ (see [2]) it follows that K₂(n,A) is central if n≥sr(A)+2."
- [2] is R. K. Dennis, *Stability for K₂*, LNM 353 (1973), 85–94.
- Use: `A = M_k(Q)` with `sr = 1`, and `n = 4`. It matches.
- Simpler citation for `sr = 1`: semisimple Artinian rings have stable rank 1 (Bass). This avoids needing
  Vaserstein's formula, which I did not read.

**(2) Central closure. Verified at source (arXiv:2004.08551v2).**
- Verbatim: "It is known that St(R) is centrally closed for any unital ring R with a complete family of Morita
  equivalent orthogonal idempotents e₁,…,eₙ for n≥5."
- The matrix units of `M_{4k}(Q)` give such a family with `n = 4k >= 8`. It matches.
- Kervaire (1970) was not read.

**(3) Matsumoto, and (4) Tate. Not read at primary.**
- Search-result excerpts of Rehmann's Trieste lecture notes say:
  - "the Theorem of Matsumoto gives a presentation of K₂(n,F) for all n ≥ 3";
  - the symbols `c_ij(x,y)` "are independent of i, j for n ≥ 3".
- Rehmann's PDF did not decode, so I could not verify those words either.
- These are classical results: Milnor, *Introduction to algebraic K-theory*, §§9–12, the Matsumoto theorem and
  Tate's computation of `K_2(Q)`.
- **A1.** Cite them by theorem number from Milnor's book, marked "not re-read".
- Note: (b) does not need index independence. `ŝ_c(y) = w ŝ_1(y) w^{-1}`, where `w` lifts a block permutation
  matrix of determinant 1. The sign twist is conjugation by a lift of a diagonal sign matrix, which fixes central
  `K_2(4m,Q)` pointwise. That leaves only Matsumoto's injectivity `K_2(4m,Q) → K_2(Q)` and Tate's theorem, both
  needed in (c).
- **A2 (optional).** Make this substitution.

**(5) Krstić–McCool at rank 4.** See `research/artifacts/gq-steinberg-q-krstic-mccool-source.md` and the earlier
report. The statement is for finitely presented unital `ℤ`-algebras and `n >= 4`. `D`, with 6 generators and 7
relations, and `R_L` both qualify. It matches.

## A3 (required for the route)

- The route requires `finitely-presented-divisible-ring-engine` (`D`), which the node itself says has not been
  independently reviewed.
- The claim holds for any finitely presented `S ⊇ Q` with a Leavitt pair.
- Either:
  - re-point the route at `leavitt-resolvent-ring-is-fp-and-contains-q` (`R_L`; direct proof checked in my earlier
    report), giving the single group `St_4(R_L)`; or
  - send `D` to review first.

## Credit

The claim's credit section is accurate:
- existence is classical (Higman);
- Mikaelian arXiv:2507.04347 announces explicit overgroups for each `n`;
- the contribution is one explicit finitely presented group `St_4(S)` containing every `GL_n(Q)`.

Whether it is "natural" is for experts.
