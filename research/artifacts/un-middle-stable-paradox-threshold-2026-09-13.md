# UN middle, part 1: the stable paradox threshold, and where the middle really is

Lane `un-middle`, 2026-09-13. Everything here is unreviewed. Credits: Tarski's theorem in the form of
Kwaśniewski–Meyer–Prasad arXiv:2502.17190v3 Corollary 2.16; the rank-two full-defect theorem on main
(`full-defect-ring-non-mf-at-rank-two`, from the non-MF paper's `thm:full-defect-ring`); Boldrini–Prasad
arXiv:2607.01896; Ortega–Perera–Rørdam; Rainone arXiv:1502.06153; Steinberg (ample groupoid algebras).

## 0. Summary
- **Theorem 1 (stable paradox threshold).** Let `R` be a countable unital ring with `(n+1)[R] ≤ n[R]` in `V(R)`, i.e.
  `R^n ≅ R^{n+1} ⊕ Q` for some f.g. projective `Q`. Then for every `N ≥ 2n` every homomorphism from `EL_N(R)` to an MF
  group is trivial. No finite generation, simplicity or property (T) is used.
- **Proposition 2.** For a countable simple unital ring `R ≠ 0`: `R` is stably finite ⟺ `[R]` is not paradoxical in
  `V(R)` ⟺ `V(R)` has a state `ν` with `ν([R]) = 1`. The paradoxical level `p(R)` equals the least `n` with `M_n(R)` not
  directly finite.
- **Corollary 4 (groupoids).** If an ample groupoid `𝒢` with compact unit space has no invariant probability measure,
  then `p(A_k(𝒢)) < ∞`, and `EL_N(A_k(𝒢))` has full MF radical for `N ≥ 2p`. So the measure-free Boldrini–Prasad
  actions, which are the C*-level "middle" for STW XXIX, are stably paradoxical at group level. They are not a
  group-level middle.
- **The true middle** has two parts:
  - (M-i) the band `3 ≤ N < 2p(R)` over rings with `p(R) ≥ 2`; the candidate is `EL_3(L_k(2,3))`;
  - (M-ii) stably finite simple rings that do not embed in matrix ultraproducts.
  In both, neither the transport machinery nor the tower machinery applies; firewalls are in §5.

## 1. Conventions
- `V(R)` is the monoid of isomorphism classes of f.g. projective right `R`-modules under `⊕`, with the algebraic preorder
  `x ≤ y` iff `y = x + z` for some `z`. `[R]` is an order unit.
- `x ≠ 0` is *paradoxical* if `(n+1)x ≤ nx` for some `n ≥ 1` (KMP Definition 2.6). A *state* is an additive, order
  preserving `ν : S → [0,∞]` with `ν(0) = 0` (KMP Definition 2.9).
- `p(R) := min{n ≥ 1 : (n+1)[R] ≤ n[R]}`, with `p(R) = ∞` if there is none.
- `(n+1)[R] ≤ n[R]` ⟺ `R^n ≅ R^{n+1} ⊕ Q` for some f.g. projective `Q`.

## 2. Theorem 1 and its proof
**Step 1: a one-sided inverse in `S = M_n(R)` with full complement.** Fix an isomorphism `θ : R^n → R^n ⊕ P`, where
`P = R ⊕ Q` (regroup `R^{n+1} ⊕ Q`). Let `ι, π` be the inclusion of and projection onto the summand `R^n`, and
`ι_P, π_P` those for `P`. Put `s := θ^{-1} ι` and `t := π θ` in `S = End(R^n_R)`. Then `ts = πι = 1`, and
`e := 1 − st = θ^{-1} ι_P π_P θ` is an idempotent with image `≅ P`.

Fullness: let `α : P → R` and `β : R → P` be the projection onto and inclusion of the summand `R`, so `αβ = 1_R`. Let
`ε_i : R → R^n` and `δ_i : R^n → R` be the `i`-th coordinate inclusion and projection. Put `x_i := ε_i α π_P θ` and
`y_i := θ^{-1} ι_P β δ_i`, both in `S`. Since `π_P ι_P = 1_P`,

```text
x_i e y_i = ε_i α (π_P ι_P)(π_P ι_P) β δ_i = ε_i α β δ_i = ε_i δ_i = e_ii ,
```

so `1_S = Σ_i x_i e y_i ∈ S e S`. Hence `S(1 − st)S = S`.

**Step 2: rank two.** `S` is a countable unital ring with `ts = 1` and `S(1−st)S = S`, so by
`full-defect-ring-non-mf-at-rank-two` every homomorphism from `EL_2(S)` to an MF group is trivial.

**Step 3: blocks.** Let `N ≥ 2n`. The ring embedding `M_2(S) → M_N(R)`, which places a `2n×2n` matrix in the upper left
corner and `1` elsewhere on the diagonal, restricts to an injective homomorphism `EL_2(S) → EL_N(R)`. It sends
`e_12(X)` to the block matrix `1 + Σ_{a,b≤n} X_ab E_{a,n+b} = Π_{a,b} e_{a,n+b}(X_ab)`. The factors commute because
`E_{a,n+b} E_{a',n+b'} = 0` (as `n+b ≠ a'`), so the image lies in `EL_N(R)`; the same holds for `e_21`.

**Step 4: normal generation.** Let `φ : EL_N(R) → M` with `M` MF. By Steps 2–3, `φ(e_{1,n+1}(r)) = 1` for all `r ∈ R`,
since `e_{1,n+1}(r)` is the image of `e_12(r E_11)`. For `k ≠ l`, `w_kl := e_kl(1) e_lk(−1) e_kl(1) ∈ EL_N(R)` acts as
a signed transposition. So for any `i ≠ j` there is a signed permutation `w ∈ EL_N(R)` with
`w e_{1,n+1}(r) w^{-1} = e_ij(±r)`. Hence `φ` kills every elementary generator and is trivial. ∎

**Calibrations.**
- `L_k(1,m)`, `m ≥ 2`: `R ≅ R^m = R^2 ⊕ R^{m−2}`, so `p = 1` and `N ≥ 2`. This is exactly the rank-two theorem.
- Leavitt algebras of module type `L_k(m,n)`, `2 ≤ m < n`: the defining isomorphism gives
  `R^m ≅ R^n = R^{m+1} ⊕ R^{n−m−1}`, so `p ≤ m` and `N ≥ 2m`.
- The Pestov ring `LC(X,F_q) ⋊ Z` embeds unitally in `∏_ω M_N(F_q)`. Normalized matrix rank gives a state on `V(R)` with
  value 1 at `[R]`, so `[R]` is not paradoxical (easy direction of Tarski), and Theorem 1 says nothing, as it must, since
  `EL_3` is LEF.
- Fields: `V(k) = N` with `[k] = 1`, and `(n+1) ≤ n` never holds.

## 3. Proposition 2: simple rings
Let `R ≠ 0` be countable, simple and unital.
- (b)⟺(c): Tarski's theorem (KMP Corollary 2.16), applied to `y = [R] ≠ 0` in `V(R)`.
- (a)⇒(b): if `(n+1)[R] ≤ n[R]`, then `R^n ≅ R^n ⊕ (R ⊕ Q)`, so `M_n(R)` has `ts = 1 ≠ st`, contradicting (a).
- (b)⇒(a): suppose `M_n(R)` is not directly finite. Then `R^n ≅ R^n ⊕ P` with `P ≠ 0` f.g. projective.
  - The trace ideal of `P` is a nonzero two-sided ideal, hence `R`. So `1 = Σ_{i≤k} f_i(p_i)` with `f_i ∈ Hom(P,R)`.
  - Then `P^k → R`, `(q_i) ↦ Σ f_i(q_i)`, is onto and splits, so `R ⊕ Q' ≅ P^k`.
  - Iterating the isomorphism, `R^n ≅ R^n ⊕ P^k ≅ R^n ⊕ R ⊕ Q'`, so `(n+1)[R] ≤ n[R]`, contradicting (b).
- The same argument shows `p(R) = min{n : M_n(R) not directly finite}`.
  - In particular a simple Dedekind-infinite ring has `p = 1`, consistent with
    `simple-dedekind-infinite-ring-elementary-full-mf-radical`.

## 4. Corollary 4: ample groupoids with no invariant measure
**Setting.**
- `𝒢` is a second countable ample groupoid with compact unit space `X`, and `k` a countable field.
- `R = A_k(𝒢)` is its Steinberg algebra, spanned by `1_B` for compact open bisections `B`.
- An invariant probability measure is a Borel probability `μ` on `X` with `μ(r(B)) = μ(s(B))` for every compact open
  bisection `B`.

**Claim.** If none exists, then `p(R) < ∞`, so `EL_N(R)` has full MF radical for `N ≥ 2p(R)`.

**Proof.** Let `ν` be a state on `V(R)` with `ν([R]) = 1`.
- Define `m(U) := ν([1_U R])` for compact open `U ⊆ X`.
- Additive: disjoint `U, V` give `1_{U⊔V} R = 1_U R ⊕ 1_V R`.
- Finite and monotone: `m(X) = 1`.
- Invariant: `1_B 1_{B^{-1}} = 1_{r(B)}` and `1_{B^{-1}} 1_B = 1_{s(B)}`, so `1_{r(B)} R ≅ 1_{s(B)} R` and
  `m(r(B)) = m(s(B))`.
- So `m` is a finitely additive probability on the clopen algebra of the compact zero-dimensional space `X`.
- It is countably additive there by compactness, so Carathéodory extends it to an invariant Borel probability,
  contrary to hypothesis.

Hence `V(R)` has no state at `[R]`; by Tarski `[R]` is paradoxical, and Theorem 1 applies. ∎

**Consequences.**
- The Cuntz groupoid has no invariant measure, so `p = 1`.
- Minimal subshift groupoids have invariant measures, so Corollary 4 is silent there.
- Boldrini–Prasad's measure-free minimal topologically free `F_∞`-actions (their Corollary 6.12, per
  `ex2-rr0-clopen-type`) give rings with `p < ∞`, hence full MF radical of `EL_N` from `N = 2p`.
  - Their C*-algebras are neither stably finite nor, a priori, purely infinite (the XXIX design,
    `cantor-crossed-product-with-finite-type-is-mixed`).
  - At group level that mixedness is invisible beyond the threshold.
  - These rings are not finitely generated, so EJZ does not apply. The full MF radical conclusion needs no (T).
- Not claimed: a converse. An invariant measure need not give matricial towers.

## 5. The true middle: what the machinery gives, firewalls, candidate objects
### (M-i) the band `3 ≤ N < 2p(R)`, `p(R) ≥ 2`
- **Transport, as printed, is silent.** For `j ≤ N/2 < p`, `M_j(R)` has no `ts = 1` whose complement `1 − st` is full.
  A full complement gives `R^j ≅ R^j ⊕ P` with `R` a summand of `P^k`, and the §3 iteration then gives
  `(j+1)[R] ≤ j[R]`, contradicting `j < p`. So neither `thm:full-defect-ring` nor the rank-two theorem applies to any
  `M_j(R)` whose `EL_2` fits inside `EL_N(R)`. For simple `R` this is plain direct finiteness of `M_j(R)`.
- **Towers are silent.** `V(R)` has no state at `[R]`, so there is no normalized Sylvester rank function and no unital
  embedding of `R` in `∏_ω M_K(k)`. Any MF approximation of `EL_N(R)` must come from something other than a ring
  approximation.
- **Candidate: `R = L_k(2,3)`, `N = 3`.**
  - Recalled, not verified: Cohn's theorem that `L(m,n)` with `m ≥ 2` is an `(m−1)`-fir, so `L(2,3)` is a domain, directly
    finite, with `p = 2`.
  - `EL_3(L_k(2,3))` is finitely generated with property (T) (EJZ), while `EL_4(L_k(2,3))` has full MF radical by
    Theorem 1.
- **Module-isomorphism route.**
  - `R^3 ≅ R^4` gives `A ∈ M_{3×4}(R)` and `B ∈ M_{4×3}(R)` with `AB = 1_3`, `BA = 1_4`, and a group isomorphism
    `Φ : GL_4(R) → GL_3(R)`, `g ↦ AgB`.
  - `Φ(e_ij(r)) = 1 + a_i r b_j`, where `b_j a_i = 0`.
  - If `Φ(EL_4(R)) ∩ EL_3(R)` contains one transvection `e_ij(r)` with `RrR = R`, then `EL_3(R)` has full MF radical.
    The firewall sits exactly here: is `1 + v r w` (with `v` unimodular and `wv = 0`) elementary in rank 3 over this ring?
  - For noncommutative rings `E_n` need not be normal in `GL_n` (Gerasimov, recalled), so this is a real question and not
    automatic.
- **New object if false in the other direction.** A finitely generated Kazhdan group `EL_3(R)` with a nontrivial MF
  quotient, sitting inside `EL_4(R)`, which has none. The exact ring property producing it: `R` directly finite with
  `R^2 ≅ R^2 ⊕ R`.

### (M-ii) stably finite simple rings that are not matricial
- States on `V(R)` exist (Proposition 2), but they need not be Sylvester rank functions, and rank functions need not be
  approximable by matrix ranks.
- **Firewall.** No one-sided compression of the form `ts = 1 ≠ st` exists in any `M_n(R)`. A non-MF proof would need
  group compressions `uLu^{-1} ⊊ L` not induced by ring isometries. An MF or LEF proof would need approximations that are
  not towers.
- This is where the converse question (U3, lane `un-converse`) lives.
