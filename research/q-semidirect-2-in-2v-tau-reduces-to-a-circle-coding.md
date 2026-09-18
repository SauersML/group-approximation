---
rg: 2
id: q-semidirect-2-in-2v-tau-reduces-to-a-circle-coding
kind: claim
title: The centralizer of the 2V_tau odometer is fibered, Q semidirect <2> acts on the Cantorized 2-adic solenoid through s and the baker map, and embedding it in 2V_tau reduces to one binary coding of the circle blown up at Q/Z
requires:
  - odometer-2v-is-fp-simple-and-contains-bs12
  - odd-roots-of-the-2v-tau-odometer-have-doubling-conjugators
distinct_from:
  lifted-odd-roots-of-the-odometer-doubled-by-the-baker-map: that is the OPEN target; this proves the fibered-centralizer reduction, gives the canonical solenoid model with all cocycles solved, and proves that the odd mixed-radix odometer cannot carry it.
  odd-roots-of-the-2v-tau-odometer-have-doubling-conjugators: that settles each odd q with a q-dependent doubling element; this treats all q at once.
---

**ESTABLISHED** (lane proof, bh-free-30, 09-18; elementary; not reviewed; no priority claimed). Notation as in `odd-roots-of-the-2v-tau-odometer-have-doubling-conjugators`: s(x,y) = (x+1, y), u(x, y_0y) = (y_0 + 2x, y), and x ∈ Z_2.

## 1. The centralizer of s is fibered

**Claim.** C_{2V_τ}(s) = {(x + k(y), gy) : k ∈ C(C, Z), g ∈ V}.

**Proof.**
- **h is fibered.** The odometer τ is minimal, so the s-orbit closures are the fibers C × {y}. A homeomorphism h commuting with s permutes them, so h(x,y) = (h_y(x), g(y)) with g a homeomorphism of C.
- **Each h_y is a translation.** h_y commutes with τ, so h_y(n) = n + h_y(0) on the dense set Z. By continuity, h_y(x) = x + β(y) with β: C → Z_2 continuous.
- **β is integer-valued and locally constant.** On a small brick uC × wC, an element of 2V_τ has the form (u x', w y') ↦ (u'τ^n(x'), w'y'); this is the local form of the topological full group of the self-similar product action. Comparing u + 2^{|u|}x' + β with u' + 2^{|u'|}(x'+n) for all x' forces |u| = |u'| and β = u' − u + 2^{|u|}n ∈ Z, constant on the brick.
- **g ∈ V.** g is locally the prefix replacement w ↦ w'. By compactness it has finitely many pieces. ∎

**Consequence.** Any q-th root of s commutes with s, so it lies in C(s). Any u' with u's u'^{-1} = s² has u^{-1}u' ∈ C(s). So the ansatz r = (x + k, ρ) and u' = u∘c of the target node is fully general for embeddings of Q ⋊ ⟨2⟩ with 1 ↦ s.

## 2. The solenoid model (all cocycles solved)

**Setup.**
- Let Σ = (Z_2 × R)/⟨(1, −1)⟩, the 2-adic solenoid, with coordinates [(x,t)], t ∈ [0,1).
- Let X′ be the circle R/Z blown up at every point of Q/Z, and Σ′ = Z_2 × X′.
- For a ∈ Q, put T_a[(x,t)] = [(x, t+a)], that is, T_a(x,y) = (x + ⌊ỹ + a⌋, y + a).
- Put M[(x,t)] = [(2x, 2t)], that is, M(x,y) = (2x + bit(y), 2y mod 1), where bit(y) = [ỹ ≥ 1/2].

**Checks.**
- T and M are continuous on Σ′, because every jump sits at a rational y.
- T_{a+b} = T_a T_b and M T_a M^{-1} = T_{2a}, so a ↦ T_a together with M gives a faithful action of Q ⋊ ⟨2⟩.
- T_1 = s.
- In the binary coding of y, M is exactly the inverse baker map u. So ⟨s, u⟩ ⊂ 2V_τ is this action restricted to Z[1/2] ⋊ ⟨2⟩, read through the dyadic Cantorization.

**Theorem.** Suppose X′ carries a binary tree structure 𝒯, a nested binary partition into intervals, under which every rotation R_a (a ∈ Q_odd/Z) and the doubling map D(y) = 2y are local 𝒯-similarities, that is, piecewise canonical maps between cones. Then Q ⋊ ⟨2⟩ ≤ 2V_τ.

**Proof.** Transport 𝒯 to the standard tree of C.
- T_a = (x + ⌊ỹ + a⌋, R_a y) lies in 2V_τ: ⌊ỹ + a⌋ is locally constant, and R_a ∈ V.
- M = u_𝒯 ∘ c with c(x, y) = (x, ι_{bit(y)}(D y)). Here ι_b is the canonical map onto the b-th root cone, and c ∈ 2V_τ because D is a local similarity.
- M normalizes the T's as computed above. ∎

In this model j = 0 and k_a = ⌊ỹ + a⌋. The e-conditions and the cocycle hold automatically.

## 3. The odd mixed-radix odometer cannot carry it (proved)

Let X_odd be the circle blown up only at Q_odd/Z, with L = Q_odd/Z acting by rotations. This is the odometer on a mixed-radix tree over the odd primes.

**Claim.** No continuous σ′: X_odd → X_odd satisfies σ′R_a = R_{2a}σ′ for all a ∈ L. So there is no g ∈ V with gR_ag^{-1} = Ψ_{f_a}(R_{2a}) on this L-space.

**Proof.**
- **σ′ is circle doubling.** Put φ(t) = πσ′(t) − 2t on the non-blown-up points; it is continuous and L-invariant. L is dense, so φ ≡ c. Hence πσ′ = 2π + c.
- **Pick a bad point.** Fix a blown-up point y ∈ Q_odd/Z. The two solutions of 2z + c = y differ by 1/2 ∉ Q_odd/Z, so one of them, z, is not blown up.
- **σ′ is discontinuous at z.** σ′(z ± ε) → y^±, which are two different points of X_odd. ∎

So the transverse space must be blown up at all of Q/Z, as X′ is.

## 4. A necessary condition on 𝒯 (proved)

𝒯 must use infinitely many distinct split ratios. With finitely many rational ratios, every cut point lies in a finite union of translates of Z[1/N], so not every point of Q/Z is a cone boundary. The dyadic tree makes D a local similarity but not R_{1/3}; mixed-radix odd trees do the reverse.

## The canonical route is dead (by `rational-rotations-and-doubling-have-no-common-tree-coding`)

A local 𝒯-similarity, as defined in §2 (piecewise induced by isomorphisms of cone subtrees), is exactly a `T`-almost-automorphic map in the sense of bh-free-16's theorem, applied to the binary tree coding 𝒯 of X′ = D. The theorem's own calibration says binary almost-automorphisms are exactly the pieces of Thompson's V. So the two notions coincide; neither is weaker.

The theorem says:
- if the doubling branches (d = 2) are almost-automorphic, then R_{1/p} is almost-automorphic for only finitely many primes p;
- but §2 needs every odd p.

So no such 𝒯 exists, and the hypothesis of the §2 theorem is never satisfied. Any embedding Q ⋊ ⟨2⟩ ≤ 2V_τ with 1 ↦ s therefore needs, by §1, a free action ρ of Q_odd/Z on C by elements of V, and a g ∈ V with σ∘g∘ρ(a) = ρ(2a)∘σ∘g, such that (C, ρ, σ∘g) is **not** topologically conjugate to (X′, rotations, doubling). §3 excludes one more natural candidate. Whether an exotic pair exists is OPEN.
