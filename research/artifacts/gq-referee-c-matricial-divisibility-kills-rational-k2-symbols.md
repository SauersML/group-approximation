# Referee report (gq-referee-c): matricial-divisibility-kills-rational-k2-symbols

- **Node:** `research/matricial-divisibility-kills-rational-k2-symbols.md` and its `-proof` route, landed
  865c4774a by lane `gq-en-ring`.
- **Lens:** independent re-derivation. In particular, I re-derive the fact (D), which the author cited from
  memory, at Milnor level.
- **Verdict: PASS.** (D) is correct. Below is a Steinberg-group proof of exactly the case the node uses. It needs
  only three theorems from Milnor, *Introduction to Algebraic K-theory*.

## 1. The three inputs

- **(M1)** `K_2(B) = ker(St(B) -> E(B))` is central in `St(B)` for every ring `B` (Milnor, Theorem 5.1).
- **(M2)** `St(B) -> E(B)` is the universal central extension of `E(B)` (Milnor, Theorem 5.10; Kervaire).
- **(M3) Tate.** `K_2(Q) ≅ {±1} ⊕ ⊕_(p odd) F_p^x` is a torsion group (Milnor, Theorem 11.6).
  - The node writes `(Z/4)^x` for the first summand. That is `≅ Z/2`, so it is correct.

## 2. Re-derivation of (D) in the form used

**The maps.**
- `δ : B -> M_n(B)`, `b ↦ b I_n`.
- The block map `β : St(M_n(B)) -> St(B)`, `x_ij(a) ↦ ∏_(s,t) x_((i,s),(j,t))(a_st)`.

**β is an isomorphism** (Morita invariance of `K_2`).
- `β` is a homomorphism. It is the stable form of the block expansion checked in
  `gq-referee-c-leavitt-pairs-embed-sl-n-q-in-steinberg-groups.md` §2(b).
- It covers the identification `E(M_n(B)) = E(B)` of block matrices.
- Both groups are universal central extensions of that one group, by (M2). So `β` is an isomorphism and
  restricts to `K_2(M_n(B)) ≅ K_2(B)`.

**β δ_* = multiplication by n on K_2(B).**
- For `z ∈ K_2(B)`, `β(St(δ)(z)) = ∏_(c=1..n) ŝ_c(z)`. Here the `ŝ_c` are the `n` block index embeddings; they
  have disjoint indices and commuting images.
- **`ŝ_c(z) = ŝ_1(z)`.**
  - Let `ω ∈ St(B)` lift the permutation matrix `P` that swaps block 1 and block `c`. `P` is elementary after
    stabilization.
  - `f_1 = ω ŝ_1(·) ω^(-1)` and `f_2 = ŝ_c` agree modulo `K_2(B)`. So `f_1 f_2^(-1)` takes values in the centre
    `K_2(B)`, by (M1).
  - It is therefore a homomorphism from the perfect group `St_r(B)` (`r >= 3`) to an abelian group, so it is
    trivial.
  - Hence `ŝ_c = ω ŝ_1 ω^(-1)`, and on the central `K_2`, `ŝ_c(z) = ŝ_1(z) = z`.
- So `β δ_*(z) = z^n`. Since `β` inverts the corner-embedding Morita map, this is the node's `δ_* = n·μ`.

## 3. The node's proof

- Let `z ∈ K_2(Q)` have order `t`, by (M3). Choose `n` with `t | n` and `φ : M_n(R_n) ≅ R`.
- `m I_n` is invertible and central, so every integer is a unit of `R_n`. Hence there is `j_n : Q -> R_n`.
- By uniqueness of unital maps out of `Q`, `ι = φ δ j_n`.
- Let `w = (j_n)_* z`. Then `β δ_*(w) = w^n = (j_n)_*(z^n) = 1`. Since `β` is injective, `δ_*(w) = 1`, and so
  `ι_*(z) = φ_*(1) = 1`. ✓
- The `K_1` remark is also correct: `diag(λ, …, λ)` has class `n[λ]`.

## 4. Calibration

- **`U_Q = colim M_(n!)(Q)`.** Here `K_2(U_Q) = colim(K_2(Q), ×(n+1)) = K_2(Q) ⊗ Q = 0`, consistent with the
  claim.
- **Why "every t" is needed.** Take `colim M_(3^k)(Q)`, where only 3-power divisibility holds. Then `K_2` is
  `K_2(Q)[1/3] ≠ 0`, and `{-1,-1}` survives. The same happens for `L_Q(1,3)`
  (`gq-referee-c-one-steinberg-group-contains-every-gl-n-q.md` §4). So the hypothesis cannot be weakened to
  divisibility by one prime.
- **O1.** Not engaged.

## 5. Scope (not a defect)

- The claim is about the unit's copy of `Q`. Its consequences for the candidate host
  `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational` are not reviewed here. Two things would need checking
  there:
  - that the congruence-block isomorphisms `R ≅ M_n(R_n)` are **unital**, for `n` divisible by every integer;
  - that full corners also pass (`full-corners-must-kill-rational-k2-symbols`).
