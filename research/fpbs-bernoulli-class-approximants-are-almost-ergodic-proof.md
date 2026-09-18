---
rg: 2
id: fpbs-bernoulli-class-approximants-are-almost-ergodic-proof
kind: route
title: The Kesten gap of the Bernoulli Koopman representation, read at two-piece statistics, forces almost expansion, an ergodic atom of almost full mass, and the reductions to ergodic approximants
target: fpbs-bernoulli-class-approximants-are-almost-ergodic
requires:
  - kesten-amenable-stabilizer-uniform-gap
  - burton-kechris-tempered-actions-koopman-bernoulli
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - burton-kechris-weak-class-limits-are-ultraproducts
---

Notation is that of the claim. Invariant sets are taken modulo null sets. A set invariant mod 0
agrees mod 0 with the strictly invariant set ∩_{γ∈Γ} γ^b A. Matrices are compared in the max
norm. C_{F,2}(a) is the closure of the set of matrices M^A(a) = (μ(γ^a A_i ∩ A_j))_{γ∈F, i,j<2},
where A_0 = A and A_1 = X∖A. This is the convention of
`burton-kechris-weak-class-limits-are-ultraproducts`, with the first n elements of the
enumeration replaced by F.

**Step 0 (d is controlled by the topology).** Since M^A(b) ∈ C_{F,2}(b), we get
dist(M^A(b), C_{F,2}(s)) ≤ d_H(C_{F,2}(b), C_{F,2}(s)), so d(b) is at most this Hausdorff
distance. Choose n with F ⊆ {γ_0,…,γ_{n−1}}. The coordinate projection
[0,1]^{n×2×2} → [0,1]^{F×2×2} is 1-Lipschitz, and it maps C_{n,2}(a) onto C_{F,2}(a): the image
of a compact set is compact, and it contains the realised matrices densely. A 1-Lipschitz map
does not increase Hausdorff distance, so d(b) ≤ d_H(C_{n,2}(b), C_{n,2}(s)). If b̃_n → s̃, the
right-hand side tends to 0 by the definition of the topology, and so d(b_n) → 0.

**Step 1 (a gap for indicators of the shift).** For f ∈ L²_0(X^s) and κ^s(γ)f = f∘(γ^{−1})^s,

  Σ_{σ∈S} ‖f − κ^s(σ)f‖² ≥ κ‖f‖².                                            (1)

Proof. Apply (KAG2) of `kesten-amenable-stabilizer-uniform-gap` with the amenable subgroup
H = {e}: it gives Σ_σ ‖g − λ(σ)g‖² ≥ κ‖g‖² for every real g ∈ ℓ²(Γ). The operators λ(σ) commute
with complex conjugation, so the left-hand side splits as the sum of the same expressions for
Re g and Im g. Hence the inequality holds for complex g. It passes to orthogonal direct sums
term by term, so it holds on ∞·λ_Γ, and it is invariant under unitary equivalence. By
`burton-kechris-tempered-actions-koopman-bernoulli`, κ^s_0 ≅ ∞·λ_Γ, which gives (1).

For a Borel B ⊂ X with p = μ(B), take f = 1_B − p. Then ‖f‖² = p(1−p), κ^s(σ)f = 1_{σ^s B} − p,
and ‖f − κ^s(σ)f‖² = μ(B Δ σ^s B). So

  Σ_{σ∈S} μ(B Δ σ^s B) ≥ κ p(1−p).                                          (2)

**Step 2 (proof of (A)).** Let A ⊂ X be Borel with t = μ(A), write d = d(b), and let τ > 0. By
the definition of d(b) and of C_{F,2}(s) as a closure, there is a Borel B ⊂ X with p = μ(B) such
that ‖M^A(b) − M^B(s)‖_∞ ≤ d + τ. Two entries of these matrices are used.

- γ = e, i = j = 0 gives |t − p| ≤ d + τ.
- γ = σ ∈ S ⊆ F, i = j = 0 gives |μ(σ^b A ∩ A) − μ(σ^s B ∩ B)| ≤ d + τ.

Measure preservation gives μ(A Δ σA) = 2(μ(A) − μ(σA ∩ A)), and the same for B. Hence
|μ(A Δ σ^b A) − μ(B Δ σ^s B)| ≤ 4(d + τ). Also |p(1−p) − t(1−t)| = |p − t|·|1 − p − t| ≤ d + τ.
Summing over σ and using (2),

  Σ_σ μ(A Δ σ^b A) ≥ κ p(1−p) − 4|S|(d+τ) ≥ κ t(1−t) − (κ + 4|S|)(d + τ).

Let τ → 0. This is (A).

**Step 3 (proof of (B)).** If A is b-invariant, the left-hand side of (A) is 0, so
t(1−t) ≤ (κ + 4|S|)d/κ = c·d. Suppose c·d < 2/9, and let η be the smaller root of
η(1−η) = c·d. The map x ↦ x(1−x) is increasing on [0,1/2] and equals 2/9 at 1/3, so η < 1/3.
Since 1 − η ≥ 1/2, η ≤ 2η(1−η) = 2c·d. Because x(1−x) > c·d strictly between the two roots
η and 1−η, **every invariant set has measure ≤ η or ≥ 1−η.**

*Atom lemma.* Let 𝓛 be the family of invariant sets of measure ≥ 1−η. It contains X. It is
closed under finite intersections: μ(E ∩ E') ≥ 1 − 2η > η because η < 1/3, and E ∩ E' is
invariant, so μ(E ∩ E') ≥ 1−η. Let m = inf{μ(E) : E ∈ 𝓛}. Choose E_k ∈ 𝓛 with μ(E_k) → m and
replace E_k by E_1 ∩ … ∩ E_k, which is still in 𝓛. Then A = ∩_k E_k is invariant with
μ(A) = m ≥ 1−η, so A ∈ 𝓛 and A has minimal measure in 𝓛. Let F ⊆ A be invariant.

- If μ(F) ≥ 1−η, then F ∈ 𝓛, so μ(F) ≥ m = μ(A), and μ(A∖F) = 0.
- If μ(F) ≤ η, then A∖F is invariant with μ(A∖F) ≥ 1 − 2η > η. So A∖F ∈ 𝓛 and
  μ(A∖F) ≥ μ(A), which gives μ(F) = 0.

So every invariant subset of A is null or conull in A, and b|_A is ergodic. This proves (B).

**Step 4 (proof of (C)).** Let b be free, A as in (B), and e = b|_A on (A, μ_A). Then e is
measure preserving because A is invariant. It is free because b is free almost everywhere, and
it is ergodic by Step 3. The space (A, μ_A) is standard and non-atomic because μ is non-atomic.
Fix a measure-preserving isomorphism (A, μ_A) ≅ (X, μ), so that e ∈ A(Γ,X,μ). The sets C_{n,k}
do not depend on this choice.

*Statistics.* The action e is free, so by `abert-weiss-free-actions-weakly-contain-bernoulli`
s ≼ e. The criterion of `burton-kechris-weak-class-limits-are-ultraproducts` gives
C_{n,k}(s) ⊆ C_{n,k}(e). Hence d_H(C_{n,k}(e), C_{n,k}(s)) = sup_{x∈C_{n,k}(e)} dist(x, C_{n,k}(s)),
and it suffices to bound dist(M^P(e), C_{n,k}(s)) for realised matrices, then pass to closures.
Let P = (P_0,…,P_{k−1}) be a Borel partition of A, and let P' be the partition of X with
P'_0 = P_0 ∪ (X∖A) and P'_i = P_i for i ≥ 1. Since A is invariant, γ^b P'_i ∩ P'_j equals
(γ^e P_i ∩ P_j) ∪ [i=j=0](X∖A), so

  μ(γ^b P'_i ∩ P'_j) = μ(A)·μ_A(γ^e P_i ∩ P_j) + [i=j=0]·μ(X∖A).

Each entry therefore changes by (1−μ(A))·|[i=j=0] − μ_A(γ^e P_i ∩ P_j)| ≤ η. So
dist(M^P(e), C_{n,k}(s)) ≤ η + dist(M^{P'}(b), C_{n,k}(s)) ≤ η + d_H(C_{n,k}(b), C_{n,k}(s)), which
gives the stated bound (with room to spare: 2η).

*Cost.* Let Φ = (φ_j) be a graphing generating R_b with Σ_j μ(dom φ_j) ≤ C_μ(b) + ε. A is
invariant, so A is a union of R_b-classes. The restrictions φ_j|_{dom φ_j ∩ A} take values in A,
and they generate R_b ∩ (A×A) = R_e, because every R_b-path between points of A stays in A.
Their μ_A-cost is Σ_j μ(dom φ_j ∩ A)/μ(A) ≤ (C_μ(b) + ε)/(1−η). Let ε → 0. This proves (C).

**Step 5 (proof of (D)).** Let b_n be free with b̃_n → s̃. By Step 0, d(b_n) → 0, so for all
large n we have c·d(b_n) < 2/9 and η_n = η(b_n) ≤ 2c·d(b_n) → 0. Let e_n be the free ergodic
action given by (C). For fixed n', k, Step 4 gives

  d_H(C_{n',k}(e_n), C_{n',k}(s)) ≤ d_H(C_{n',k}(b_n), C_{n',k}(s)) + 2η_n → 0,

so ẽ_n → s̃. Also C(e_n) ≤ C(b_n)/(1−η_n).

1. Restricting the hypothesis to ergodic sequences gives one direction. For the other, suppose
   liminf_n C(b_n) < C(s) for some free b_n with b̃_n → s̃. Pass to a subsequence along which
   C(b_n) converges to the liminf. Then liminf C(e_n) ≤ lim C(b_n)/(1−η_n) < C(s), with e_n free
   and ergodic, and ẽ_n → s̃.
2. Again one direction is immediate. For the other, let b_n be free with b̃_n → s̃ and
   C(b_n) < C(Γ) + ε_n, where ε_n → 0. The class space is metrizable, so such a sequence exists
   whenever s̃ lies in every closure named in the hole. Then ẽ_n → s̃ and
   C(Γ) ≤ C(e_n) ≤ (C(Γ) + ε_n)/(1−η_n) → C(Γ). The lower bound holds because C(Γ) is the
   infimum of the costs of free actions.
3. Let b_n be free with b̃_n → s̃ and C(b_n) ≤ C(s) − 2δ. Then for large n,
   C(e_n) ≤ (C(s) − 2δ)/(1−η_n) ≤ C(s) − δ, because C(s) is finite (Γ is finitely generated).
   By Step 0 applied to e_n, d(e_n) → 0, and (A) holds for each e_n.

Remark, not used in the proof: the claim excludes amenable Γ, where ρ = 1 and κ = 0. For such Γ
every free action is weakly equivalent to s, so (D) says nothing new there.

**Step 6 (the obstruction).** Let A be Borel with t = μ(A) ∈ [η, 1−η], η ≤ 1/2, and
Σ_σ μ(A Δ σ^b A) ≤ τ. On [η, 1−η] we have t(1−t) ≥ η(1−η). Then (A) gives
τ ≥ κ η(1−η) − (κ + 4|S|) d(b), which rearranges to the stated lower bound on d(b). An invariant
convex mixture t·a + (1−t)·s has an invariant set of mass t, so τ = 0 and
d ≥ κ t(1−t)/(κ + 4|S|). By Step 0 it stays at a fixed Hausdorff distance from s̃ at every
window n' with F ⊆ {γ_0,…,γ_{n'−1}} and k = 2. ∎

**Scope.** Nothing here bounds the coarse modulus of
`fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap`. Ergodic approximants with uniform
Kesten expansion can still carry cheap graphings whose witness windows diverge, so the target
hole stays open.
