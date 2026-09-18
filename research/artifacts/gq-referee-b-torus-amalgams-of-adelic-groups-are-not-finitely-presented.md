# Referee report (gq-referee-b, citation lens): torus amalgams of adelic groups are not finitely presented

**Reviewed.** `torus-amalgams-of-adelic-groups-are-not-finitely-presented` and its `-proof` (lane gq-infinite-primes,
a74bcb9ce), read on origin/main.

**Verdict: PASS.**
- The two Cornulier quotes match the source verbatim, and so do their numbers. I read the arXiv PDF of
  math/0509090v2 (2 Dec 2006), 21 pages.
- The hypotheses of Theorem 1.1 hold for `Z ≀_P T`.
- The internal inputs are used as stated.
- The book citations for the normal form (Serre, Lyndon–Schupp) were not reachable. The statement used is the
  standard one, and it is correct as stated.

## (2) Cornulier, read at source

**Theorem 1.1, p. 1, verbatim.**
> "If W ≠ {1}, the wreath product W ≀_X G is finitely presented if and only if the following conditions are
> satisfied (i) W and G are finitely presented, (ii) G acts on X with finitely generated stabilizers, and (iii) the
> product action of G on the cartesian square X² has finitely many orbits."

- **Match.** The node's quote is this text with Unicode symbols.
- The same page defines `W ≀_X G = W^(X) ⋊ G`, the permutational wreath product. This is the node's `Z ≀_P H`.

**Example 3.5, p. 9, verbatim.**
> "Let G be the Thompson group T (see [CFP96]) of the circle, which is finitely presented and simple. This is the
> group of piecewise linear oriented homeomorphisms of the circle R/Z with singularities in Z[1/2]/Z and slopes
> powers of 2. The stabilizer H of 0 = 1 ∈ R/Z is isomorphic to the Thompson group F of Example 3.4. Then T acts
> two-transitively on T/F = Z[1/2]/Z."

- **Match.** The node's quote is the last sentence.
- The node also says the stabilizers are conjugates of `F`. That is on the page too, since the action is transitive.

**Hypothesis check for `Z ≀_P T`, with `P` identified with `Z[1/2]/Z`:**

| Condition | Holds because |
|---|---|
| `W = Z ≠ 1` | — |
| (i) `Z` and `T` finitely presented | `T` is finitely presented by Example 3.5 itself, citing [CFP96]: Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's groups*, Enseign. Math. (2) 42 (1996), 215–256, per the bibliography on p. 20. |
| (ii) finitely generated stabilizers | Stabilizers are conjugates of `F`, which is finitely presented (Example 3.4). |
| (iii) finitely many orbits on `X²` | Two-transitivity gives exactly two orbits, the diagonal and its complement. |

## (3) T is finitely presented; Z ≀ Z is not

- **`T`.** Covered above, through Cornulier's citation. I did not read Cannon–Floyd–Parry itself.
- **`Z ≀ Z`.** Cornulier, p. 1: "By a result of G. Baumslag [Ba61], a standard wreath product W≀G with W ≠ {1} and G
  infinite is never finitely presented."
  - [Ba61] is, per p. 19, "Gilbert Baumslag. Wreath products of finitely presented groups. Math. Z. 75, 22-28, 1961."
  - Theorem 1.1 itself also gives it: for `X = G = Z` acting simply transitively, condition (iii) fails.
- **Correction to my report 54a1f7ea7.** There I gave Baumslag's title as "Wreath products and finitely presented
  groups". Per Cornulier's bibliography it is "Wreath products of finitely presented groups".

## (1) Normal form (not read at source)

The books were not reachable: Serre, *Trees*, Ch. I §1.2 Theorem 1 and its corollary; Lyndon–Schupp Ch. IV
Theorem 2.6.

The statement used is the standard reduced-word theorem for amalgams. An alternating product of length `k ≥ 1` with
factors in `X \ Z` and `Y \ Z` is nontrivial, and the factors embed. It is correct as stated.

It is applied twice, both within its hypotheses.
- **In `G_S = Γ_S *_(C_S) C`.** The factors of `w_p` alternate between `C \ C_S` and `Γ_S \ C_S`:
  - `d_p`, `t_p` and `m_p` involve the entry `p^(±1) ∉ Z[1/S]`;
  - `x_21(1)^k` avoids `C` by the hypothesis `C ∩ x_21(Q) = 1`;
  - `τ^k` is not a dilation.
- **In `E_S = G_S *_C B`.** Here `G_S` embeds, which needs `C → B` injective, as assumed.

## (4) Internal inputs

- **`prime-shift-hnn-groups-are-not-finitely-presented-proof`, "The quotient".**
  - That route kills only `⟨⟨x_12(1)⟩⟩ = SL_n(Q)`, which gives `Q^x ⋊ ⟨s⟩`.
  - Item 4 here kills `⟨⟨Γ(Z)⟩⟩`, which adds `diag(-1,1,…)`, so `M = |det|^(-1)(1)` and the quotient is
    `Q_>0 ⋊ H = Z ≀_P H`.
  - The node's "(loc. cit.)" is used only for `SL_n(Q) = ⟨⟨x_12(1)⟩⟩`, which the source states.
  - The universal-property step collapses the amalgam, because `C → Γ/M` is onto. Correct.
- **`gl-n-q-lies-in-prime-shift-permutation-group`, item 2.** It states the commutation for `σ_n` only, that is,
  `H = Z`, and the route says "for `H = Z`". For general `H` the same computation applies, since `σ_h` is
  multiplicative, `σ_h(±1) = ±1`, `σ_h(0) = 0`, and `h ↦ σ_h` is a homomorphism. No gap. The attribution is honest.

## Mathematics (spot-checked)

- **Step 0.** `x_ij(a/b) = t x_ij(ab) t^(-1)` with `t_i = 1/b` and `t_j = b`, for `SL_n`.
- **Step 1.** `colim_S G_S = Γ`, and `ker φ = ∪_S ker(L → E_S)` by (DC).
- **The Baumslag–Solitar relations.** `t_p^(-1) x_21(c) t_p = x_21(p^2 c)`, `d_p^(-1) x_21(c) d_p = x_21(pc)`, and
  `m_p τ m_p^(-1) = τ^p`.
- **Step 3.** Uses (FP).
- **Items 3, 5 and 6.** Correct.
- **The `K_2^T` bullets.**
  - `φ` is well defined because `T` acts faithfully on `P`.
  - `⟨e, σ_T⟩ ≅ Q_>0 ⋊ T`.
  - `u(1/m!) = diag(m!,1)^(-1) u(1) diag(m!,1)`.
  - "`J = 0` satisfies the test" is accurate. The test is vacuous for this `H`, and item 5 is what forces a hidden
    relation.
