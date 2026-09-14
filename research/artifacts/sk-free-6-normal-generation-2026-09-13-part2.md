# sk-free-6 part 2: normal generation in the finite simple models, and the map of the boundedness question (2026-09-13)

Lane sk-free-6. Part 1: `research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md` (Theorems A, B, Corollary C, Open D).

## 1. Theorem B_fin (the finite simple models see the same numbers)
**Setting** (the note's models). y_ℓ is a periodic word of least period N = N_ℓ whose (2ℓ+1)-windows are the (2ℓ+1)-words of X. D_ℓ(f) ∈ M_N(F_2) is the diagonal matrix of f along the shifts of y_ℓ, for f depending on the window [−ℓ, ℓ], and ρ_ℓ is the model map with ρ_ℓ(e_ij(f)) = e_ij(D_ℓ(f)) in SL_{3N}(F_2).

For a clopen V ≠ ∅ determined by the window [−ℓ, ℓ], let m = m_ℓ(V) = rank D_ℓ(χ_V) be the number of positions i ∈ Z/N whose shifted window of y_ℓ lies in V. In a group S, for g ≠ e, ν^S_g(h) is the least number of S-conjugates of g^{±1} with product h.

**Theorem B_fin.** Suppose m ≥ 1. With g = e_12(D_ℓ(χ_V)) and h = e_12(I_N) in S = SL_{3N}(F_2):

  N/m ≤ ν^S_g(h) ≤ ⌊N/m⌋ + 2,

with ν^S_g(h) = N/m when m divides N. Every limit point of m_ℓ/N_ℓ as ℓ → ∞ is μ(V) for some T-invariant μ. So for uniquely ergodic X,

  lim_ℓ ν^{SL_{3N_ℓ}(F_2)}_{ρ_ℓ(e_12(χ_V))}(ρ_ℓ(e_12(1))) · μ(V) = 1,

matching the limit group, where ν_{e_12(χ_V)}(e_12(1)) ∈ [1/μ(V), ⌊1/μ(V)⌋ + 3] (part 1, Theorem B).

**Proof.**
- **Lower bound.** Matrix rank over F_2 is conjugation-invariant and subadditive, so rk(h − I) ≤ ν·rk(g − I), i.e. N ≤ νm.
- **Upper bound.** Partition Z/N into q = ⌊N/m⌋ groups of size m plus a remainder of size r < m.
  - For a group with coordinate projection P_t: pick σ ∈ GL_N(F_2) with σ D_ℓ(χ_V) σ^{-1} = P_t (a permutation matrix). Then diag(σ,σ,σ^{-2}) ∈ SL_{3N}(F_2) conjugates g to e_12(P_t).
  - For the remainder P′ (rank r < m): choose P″ ⊇ P′ conjugate to D_ℓ(χ_V). Then e_12(P′) = [e_13(P′), e_32(P″)] (commutator formula, P′P″ = P′), which is 2 conjugates of g^{±1}, since e_32(·) is a permutation conjugate of e_12(·).
  - e_12(I_N) = ∏_t e_12(P_t)·e_12(P′) gives ν ≤ q + 2, and ν ≤ q when r = 0.
- **Limits.** Let η_ℓ = N_ℓ^{-1} Σ_{i∈Z/N_ℓ} δ_{S^i y_ℓ} be the periodic-orbit measure on A^Z, where S is the shift.
  - η_ℓ is shift-invariant, and m_ℓ/N_ℓ = η_ℓ([V]) for the cylinder set [V] ⊆ A^Z that defines V.
  - A cylinder [v] with v ∉ L(X) gets η_ℓ([v]) = 0 once 2ℓ+1 ≥ |v|, since all windows of y_ℓ of length ≤ 2ℓ+1 are words of X.
  - So every weak* limit of η_ℓ is invariant and supported on X. ∎

**Remark (normal generation numbers pass to the limit).** A marked limit of finite groups controls only relations of bounded length. Normal generation numbers involve conjugators of arbitrary length, so in general they are not continuous in the space of marked groups. For G_X they are continuous along the note's models, within an additive constant 3 on the G_X side and 2 on the model side, whenever X is uniquely ergodic.
- For non-uniquely-ergodic X, the models can be chosen to approximate any ergodic μ: take closed walks in the Rauzy graphs with the right frequencies.
- The limit group G_X instead sees sup_μ 1/μ(V), the worst case over the simplex. The models' numbers depend on the chosen y_ℓ; the group's number does not.

**Model test.** For the Fibonacci subshift (μ[1] = (3−√5)/2) with V = [1] and y_ℓ a Fibonacci word f_k: N = F_k and m = F_{k−2}, so N/m → φ² = 1/μ[1] ✓.

## 2. Open D, sharpened
**Question.** Is λ^c, the conjugation-invariant root length on G_X, bounded? Equivalently, is G_X bounded in the sense of Burago–Ivanov–Polterovich?

### 2.1 Odometer-type reduction (a test case)
- For the 2-adic odometer, the ring is ⋃_n M_{2^n}(F_2[t^{±1}]) (`minimal-cantor-crossed-product-has-stable-rank-at-most-two`, attempt 1). So EL_3 of it is ⋃_n SL_{3·2^n}(F_2[t^{±1}]), since F_2[t^{±1}] is Euclidean and E = SL.
- Bounded root length there is equivalent to a uniform bound, independent of n, on writing every element of SL_{3·2^n}(F_2[t^{±1}]) as a product of 3×3 *block* elementary matrices with 2^n×2^n blocks.
- Obstruction: sr(M_k(F_2[t^{±1}])) = 2 for every k, so block Gauss reduction gets stuck at a 2×2 block matrix [[A11,A12],[A21,A22]]. For diag(a,1) ⊕ diag(b,0)-type columns no block operation X ↦ A11 + XA21 makes A11 invertible. The determinant obstruction is that of sr 2.
- Classical input to check: bounded elementary generation of SL_n(F_q[t]) for n ≥ 3. Recalled as known through Carter–Keller-type results for Dedekind rings of arithmetic type; not verified.
- The odometer is not a subshift, but Toeplitz subshifts are almost 1-1 extensions of odometers. So the test case is relevant; it does not settle the subshift case.

### 2.2 The cut lemma and banded matrices with banded inverses
The cut lemma of part 1 §4 writes h ∈ G_X as (≤ 28 root elements)·(Peirce transvection ≤ 18)·(remainder).
- In the orbit representation, the remainder is a block-tridiagonal bi-infinite F_2-matrix over the induced system with a banded inverse.
- **Strang's theorem** on banded matrices with banded inverses (G. Strang 2011, "Fast transforms: banded matrices with banded inverses", recalled; with Olshevsky and Zhlobich) factors such a finite matrix into block-diagonal factors with small blocks at two alternating offsets. The number of factors depends on the bandwidth, and the only infinite obstruction is the shift index.
- Our factors are EL_3(A_Y) and EL_3(A_{Y′}) for two cut systems. Their blocks are long (heights ≫ w), and the number of factors must be independent of w.
- The long-block version of Strang's theorem (O(1) factors when the blocks are much longer than the bandwidth and the index is 0) is exactly what Open D needs. It fails for the naive corrected compression, whose inverse wraps around blocks, but the wrap-around of diag(u,u^{-1},1) is handled by a Whitehead element.

**Worked example (diag(u,u^{-1},1)).**
- Let v_B be the cyclic shift in each block. H_1 := diag(v_B, v_B^{-1}, 1) ∈ GL_3(A_Y) = EL_3(A_Y).
- H_1^{-1} diag(u,u^{-1},1) = diag(c, c′, 1), where c (component 1) is the induced shift on block tops, and c′ (component 2) is the inverse induced shift on block bottoms.
- A level permutation w ∈ GL_1(A_Y) swapping tops and bottoms inside each block gives c′ = w c^{-1} w^{-1}.
- So diag(c,c′,1) = diag(1,w,1)·diag(c,c^{-1},1)·diag(1,w^{-1},1). That is 2 elements of EL_3(A_Y) and one Whitehead element (6 root elements).
- **Pattern to prove in general:** the wrap-around remainder of an index-0 element is a bounded product of Whitehead elements over induced units, up to EL_3(A_Y)-factors. Status: open.

### 2.3 Stable rank one would reduce Open D to units
If sr(R_X) = 1:
- GL_3(R_X) = (≤ 10 root elements)·diag(1,1,GL_1(R_X));
- Open D reduces to bounded root length of diag(1,1,v) for units v of index 0;
- K_2(3,R_X) = 0, by van der Kallen's injective stability K_2(n,R) → K_2(n+1,R) for n ≥ sr(R)+2 (recalled). This closes `aperiodic-subshift-ring-unstable-k2-vanishes` for minimal X and gives G_X ≅ St_3(R_X).

For the exchange ring R_X (`minimal-cantor-crossed-product-is-an-exchange-ring`), sr 1 is equivalent to internal cancellation of idempotents (H.-P. Yu, J. Pure Appl. Algebra 98 (1995), recalled). That follows from:
1. every idempotent of M_n(R_X) is equivalent to a diagonal idempotent diag(χ_{U_1},…,χ_{U_n});
2. diagonal idempotents with the same class in K_0(R_X) = K^0(X,T) are equivalent via level permutations in Kakutani–Rokhlin towers (clopen sets in X×{1..n} with equal K^0-class are equidecomposable by the ample groupoid; standard for Cantor minimal Z-systems, recalled).

Item 1 is the crux. A corrected compression of an idempotent is an idempotent of EL-type in A_Y. The defect is localized at the block ends, but whether the correction can be chosen end-local is the idempotent analogue of the wrap-around issue in 2.2.

## 3. Credit additions (bounded)
- P. A. Dowerk and F. Le Maître, "Bounded normal generation is not equivalent to topological bounded normal generation", arXiv:1801.01329 (abstract read). Examples come from derived L¹ full groups, which are Polish; it gives no measure-count formula.
- Part 1's operator-algebraic analogues: Dowerk–Thom arXiv:1506.08549 and arXiv:1606.00409.
- Liebeck–Shalev, covering numbers of finite simple groups (Annals 2001, recalled): N/m is the Liebeck–Shalev scale log|S|/log|g^S| up to constants for these block transvections. Theorem B_fin is the exact linear-algebra version with additive error 2.

## 4. Nodes
- `finite-models-transvection-covering-converges-to-measure` (claim) + `-proof` (route), requires [transvection-normal-generation-recovers-invariant-measures, finite-simple-groups-converge-to-simple-kazhdan-group].
- Open D: the Attempts of `subshift-el-groups-have-bounded-conjugation-invariant-norms` get the odometer reduction, the Strang long-block formulation, and the idempotent crux for sr 1.
