# sk-open-4 dictionary, part 1: the algebraic K-theory of R_X, the half-orbit index, and the stable groups

Lane sk-open-4, 2026-09-13. Unreviewed until a verifier PASSes it.

**Setting.**
- (X,T) is an infinite minimal Cantor system; every infinite minimal subshift qualifies. q is a prime power.
- A = LC(X,F_q), σ(f) = f∘T^{-1}, and R_X = A[u,u^{-1};σ] = LC(X,F_q) ⋊_T Z, with u f u^{-1} = σ(f). The note has q = 2 and G_X = EL_3(R_X).
- K^0(X,T) = C(X,Z)/(1 − T_*)C(X,Z) with T_* f = f∘T^{-1}. It is the group underlying the Herman–Putnam–Skau dimension group, and it is torsion-free.

## 1. Theorem K (algebraic K-theory of R_X)
For i ≥ 1:

    K_0(R_X) ≅ K^0(X,T)                    (existing node subshift-crossed-product-k0-is-coinvariant-group)
    K_1(R_X) ≅ (K^0(X,T) ⊗ F_q^×) ⊕ Z
    K_2i(R_X) ≅ Z/(q^i − 1)
    K_2i+1(R_X) ≅ K^0(X,T) ⊗ Z/(q^{i+1} − 1)

Equivalently, K_n(R_X) ≅ (K^0(X,T) ⊗ K_n(F_q)) ⊕ K_{n−1}(F_q) for n ≥ 1.

Over F_2:

    K_1 ≅ Z,  K_2 = 0,  K_3 ≅ K^0(X,T)/3,  K_4 ≅ Z/3,  K_5 ≅ K^0(X,T)/7,  K_6 ≅ Z/7, ...

**Proof.**
- **Step 1 (the fibration).** Word for word as Steps 1–3 of `subshift-crossed-product-k0-is-coinvariant-group-proof`:
  - A is a directed union of finite products of fields, and it is regular supercoherent;
  - σ is a unital automorphism;
  - ABC Theorem 3.6 with A = Z, plus Lemma 7.2 (`abc-twisted-laurent-k-theory-fibration`), give for every n the exact sequence
    `K_n(A) --(1−σ_*)--> K_n(A) --> K_n(R_X) --> K_{n−1}(A) --(1−σ_*)--> K_{n−1}(A)`.
  - So `0 → coker(1−σ_* | K_n(A)) → K_n(R_X) → ker(1−σ_* | K_{n−1}(A)) → 0` is exact.
- **Step 2 (coefficients).**
  - K-theory preserves filtered colimits of rings (quoted in the ABC node). A = colim_P A_P with A_P ≅ F_q^P over finite clopen partitions P.
  - So K_n(A) = colim_P K_n(F_q)^P = LC(X, K_n(F_q)). Here σ_* is composition with T^{-1}, by naturality in the ring maps A_P → A_{T P}.
- **Step 3 (invariants and coinvariants).** Let M be a discrete abelian group.
  - An invariant locally constant f: X → M is constant on the dense orbits, so it is constant. Hence ker(1−σ_* | LC(X,M)) = M.
  - LC(X,M) = colim_P (Z^P ⊗ M) = C(X,Z) ⊗ M, and ⊗M is right exact. Hence coker(1−σ_* | LC(X,M)) = K^0(X,T) ⊗ M.
  - Step 5 of the K_0 route shows that the images of 1 − σ_* and 1 − T_* coincide.
- **Step 4 (Quillen).** K_0(F_q) = Z, and for i ≥ 1, K_{2i−1}(F_q) = Z/(q^i − 1) and K_{2i}(F_q) = 0. This is Quillen's computation, imported by `quillen-k-theory-of-finite-fields`.
- **Step 5 (assembly).**
  - n = 2i ≥ 2: the cokernel term is K^0 ⊗ K_{2i}(F_q) = 0 and the kernel term is K_{2i−1}(F_q). So K_{2i}(R_X) ≅ Z/(q^i − 1).
  - n = 2i + 1 ≥ 3: the kernel term is K_{2i}(F_q) = 0. So K_{2i+1}(R_X) ≅ K^0 ⊗ Z/(q^{i+1} − 1).
  - n = 1: 0 → K^0 ⊗ F_q^× → K_1(R_X) → Z → 0 splits because Z is free.
  - In every other degree one of the two terms vanishes, so no splitting question arises. ∎

**Model tests.**
- **X = one point** (outside the theorem, but Steps 1–5 apply with ker = coker = K_n(F_q)). This gives K_n(F_q[t^{±1}]) = K_n(F_q) ⊕ K_{n−1}(F_q), which is Bass–Heller–Swan ✓.
- **X = a periodic orbit of length p.** R_X ≅ M_p(F_q[t^{±1}]) (§3 of part 2) and K^0 = Z. The formula gives K_n(F_q) ⊕ K_{n−1}(F_q), which is Morita invariance plus Bass–Heller–Swan ✓.
- **Sturmian X_α.** K^0 = Z + αZ ≅ Z², so over F_2, K_3(R_X) ≅ (Z/3)².

**Credit and novelty.** This is a routine combination of ABC's algebraic Pimsner–Voiculescu fibration with Quillen. The analog for C(X) ⋊ Z (K_0 = K^0, K_1 = Z) is Pimsner–Voiculescu and Putnam. The bounded check covered main only: no node computes K_n for n ≥ 1. No literature search was made for a published algebraic statement, so it should be credited as "follows from ABC and Quillen".

## 2. Theorem I (half-orbit index), q = 2
Fix x ∈ X and V = F_2^{(Z)} with basis δ_n. Put π(f)δ_n = f(T^n x)δ_n and π(u)δ_n = δ_{n+1}.
- **The representation.**
  - π(u)π(f)π(u)^{-1} = π(f∘T^{-1}), so π is a representation of R_X.
  - It is faithful: for r = Σ f_j u^j ≠ 0, some f_j is nonzero on a clopen set that the dense orbit meets, so π(r)δ_n ≠ 0 for some n.
  - π(r) has bounded propagation: δ_n ↦ span{δ_{n+j} : |j| ≤ w}.
- **The index.**
  - Let P be the coordinate projection onto V_+ = span{δ_n : n ≥ 0}, applied entrywise on V^k.
  - For M ∈ GL_k(R_X) put T_M = Pπ(M)P on V_+^k. Then T_M T_{M^{-1}} = I − Pπ(M)(1−P)π(M^{-1})P, and bounded propagation makes the correction finite rank.
  - So T_M is invertible modulo finite rank, and the algebraic Fredholm index ind(M) = dim ker T_M − dim coker T_M is defined.
  - ind is additive (T_{MN} = T_M T_N + finite rank; algebraic index additivity), stable under diag(M,1), and invariant under finite-rank perturbation.

**Theorem I.** ind: GL(R_X) → Z factors through an isomorphism K_1(R_X) → Z, with ind(u) = −1.

**Proof.**
- **ind vanishes on elementary matrices.** For i ≠ j, (Pπ(rE_ij)P)² = (Pπ(r)P)² ⊗ E_ijE_ij = 0. So T_{e_ij(r)} = I + nilpotent is invertible and has index 0.
- **The value on u.** T_u is the unilateral shift on V_+: injective with cokernel span{δ_0}, so ind(u) = −1.
- **Conclusion.** ind is a surjective homomorphism K_1(R_X) → Z. By Theorem K over F_2, K_1(R_X) ≅ Z, and a surjective endomorphism of Z is bijective. ∎

**Consequences.**
- (a) If ind(M) ≠ 0 then M ∉ EL_n(R_X) for every n. For example diag(u,1,1) ∉ G_X.
- (b) diag(M, I_m) ∈ EL_{n+m}(R_X) for some m iff ind(M) = 0.
- (c) **Topological full group.**
  - γ ∈ [[T]] with γ = T^{n_γ} has the unit a_γ = Σ_k u^k χ_{\{n_γ = k\}}, and π(a_γ)δ_n = δ_{σ(n)} with σ(n) = n + n_γ(T^n x).
  - For a bijection of Z with bounded displacement, T_{a_γ} has kernel span{δ_n : n ≥ 0, σ(n) < 0} and cokernel span{δ_m : m ≥ 0, σ^{-1}(m) < 0}. So ind(a_γ) = −φ(σ), where φ(σ) is the flux across 0.
  - The flux is the same across every cut, so Σ_{n=a}^{b} (σ(n) − n) = φ·(b − a) + O(w²). By Birkhoff at a μ-generic point, φ = ∫ n_γ dμ = I(γ), the Giordano–Putnam–Skau index.
  - So **ind(a_γ) = −I(γ)**, and diag(a_γ,1,1) ∉ G_X whenever I(γ) ≠ 0. The embedding γ ↦ diag(a_γ, a_γ^{-1}, 1) (Whitehead) avoids this; sk-subgroups owns that embedding.

## 3. Theorem S (the stable elementary group), q = 2
For EVERY homeomorphism T of a Cantor set X (minimality not needed):
- K_2(R_X) = 0. So St(R_X) → E(R_X) is an isomorphism, and E(R_X) is centrally closed: H_2(E(R_X);Z) = 0.
- For minimal X, H_3(E(R_X); Z) ≅ K_3(R_X) ≅ K^0(X,T)/3K^0(X,T).

**Proof.**
- In Step 1 the cokernel term is K_2(A) = LC(X, K_2(F_2)) = 0 and the kernel term is K_1(A) = LC(X, F_2^×) = 0. So K_2(R_X) = 0 for any T.
- K_2(R) = ker(St(R) → E(R)), and St(R) is the universal central extension of E(R), so H_2(E(R);Z) ≅ K_2(R) (Kervaire). Hence St(R_X) = E(R_X) with trivial Schur multiplier.
- H_3(St(R);Z) ≅ K_3(R) (Gersten) gives the last isomorphism.
- Citations are to be quoted verbatim from Weibel's K-book (chapters III and IV) in the `-citation` route. ∎

**Blind spot (firewall F1).** Theorems K, I and S depend only on the abstract group K^0(X,T).
- For irrational α and β, the Sturmian rings have isomorphic K-groups, isomorphic stable Steinberg groups' H_2 and H_3, and the same index.
- But X_α and X_β are strongly orbit equivalent only when Z + αZ = Z + βZ inside R, by Giordano–Putnam–Skau (unital ordered K^0).
- So these invariants cannot see the order on K^0, the SOE class, or the conjugacy class.
