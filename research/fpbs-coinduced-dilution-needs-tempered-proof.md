---
rg: 2
id: fpbs-coinduced-dilution-needs-tempered-proof
kind: route
title: Restrict to H to get cheapness through the induction formula, and carry Koopman coefficients into the ultraproduct by normalized sums over cosets
target: fpbs-coinduced-dilution-needs-tempered
requires:
  - gaboriau-induction-formula-complete-section
  - fpbs-factor-lift-cost-monotone
  - burton-kechris-weak-class-limits-are-ultraproducts
  - cgdls-ultraproduct-cost-equals-combinatorial-cost
  - burton-kechris-tempered-actions-koopman-bernoulli
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - cost-is-constant-on-weak-equivalence-classes
---

Notation is as in the target. Inner products are linear in the first variable, and
κ^b(γ)f = f∘b(γ)^{−1}. Write V = Γ/H, |V| = [Γ:H], and y = (y_c)_{c∈V} ∈ X^V.

**Step 1: D_H(a) is a free p.m.p. action.** Action property:
(g·(h·y))_c = a(g)(h·y)_{g^{−1}c} = a(g)a(h) y_{h^{−1}g^{−1}c} = (gh·y)_c. Each g permutes the
coordinates and applies the measure-preserving a(g) to each one, so μ^V is preserved.

Freeness: fix g ≠ e. If g fixes every c ∈ V, then g·y = y forces y_c = a(g)y_c, a null event
because a is free. Otherwise pick c with g^{−1}c = d ≠ c. Then g·y = y forces y_c = a(g)y_d.
The coordinates y_c, y_d are independent with non-atomic law μ, so this event is null. Γ is
countable, so D_H(a) is essentially free, and E_H(a) is free because it has the free factor
D_H(a). The space X^V is standard non-atomic, so both actions lie in FR(Γ,X,μ) up to
isomorphism.

**Step 2: identification with CIND.** Use the standard model of co-induction. CIND_H^Γ(c), for
c ∈ A(H,X,μ), acts on maps f : Γ → X with f(γh) = c(h)^{−1}f(γ), by (g·f)(γ) = f(g^{−1}γ). The
measure is transported from X^T along f ↦ f|_T, for a transversal T ∋ e. For c = a|H put
y_c = a(t_c)f(t_c), where t_c ∈ T represents c. This is independent of the representative,
since a(th)f(th) = a(t)a(h)a(h)^{−1}f(t). Applying a(t_c) coordinatewise preserves μ^T. Next,
(g·f)(t_c) = f(g^{−1}t_c) = f(t_d h) = a(h)^{−1}f(t_d), where d = g^{−1}c and t_c = g t_d h. So
the new coordinate is a(t_c)a(h)^{−1}f(t_d) = a(g)a(t_d)f(t_d) = a(g)y_d. This is the formula
of D_H(a).

**Step 3: cheapness (a).** Γ is finitely generated, so H is finitely generated and all costs
below are finite.
- The coordinate map π(y) = y_{eH} is H-equivariant: for h ∈ H,
  π(h·y) = a(h)y_{h^{−1}H} = a(h)π(y), and π_*μ^V = μ. Both D_H(a)|H and a|H are free.
  `fpbs-factor-lift-cost-monotone` for the countable group H gives C(D_H(a)|H) ≤ C(a|H).
- Let b be a free p.m.p. action of Γ on (Z,ν), and b′ = b × (Γ ↷ Γ/H). Put Y = Z × {eH},
  of measure 1/|V|. Transitivity on Γ/H makes Y a complete section. (z,eH) and (z′,eH) are
  R_{b′}-equivalent iff z′ = b(g)z for some g with gH = H, i.e. g ∈ H. So R_{b′}↾Y is R_{b|H}
  with normalized measure ν. `gaboriau-induction-formula-complete-section` gives
  C(b′) − 1 = (C(b|H) − 1)/|V|.
- Apply this with b = D_H(a) and with b = a. It gives C(E_H(a)) − 1 ≤ C(a × Γ/H) − 1. Now
  a × Γ/H → a is a factor map of free actions, so by `fpbs-factor-lift-cost-monotone`,
  C(a × Γ/H) ≤ C(a). Hence C(E_H(a)) ≤ C(a).

**Step 4: the witness lemma (b).** Let b_u = ∏_n b_n/u on (X_u, μ_u), with
b_u(γ)[x_n]_u = [b_n(γ)x_n]_u. Put K = sup_n ‖ξ_n‖_4^4.

*4a. Bounded internal functions.* If f_n ∈ L^∞(X_n) with sup_n ‖f_n‖_∞ ≤ M, then the internal
function f_u = [f_n]_u, defined by taking the u-limit of values, is μ_u-measurable. It
satisfies ∫ f_u \bar g_u dμ_u = lim_u ∫ f_n \bar g_n dμ_n. This follows from
Theorem 2.29(1) in `cgdls-ultraproduct-cost-equals-combinatorial-cost`, by approximating f_n,
g_n uniformly in n by simple functions with values on a fixed finite grid, using
[A_n]_u ∩ [B_n]_u = [A_n ∩ B_n]_u. Also κ^{b_u}(γ)f_u = [κ^{b_n}(γ)f_n]_u.

*4b. Truncation.* For M > 0 let f^M_n = ξ_n·1_{|ξ_n| ≤ M}. By Chebyshev,
‖ξ_n − f^M_n‖_2² ≤ ∫_{|ξ_n|>M} |ξ_n|² ≤ K/M². Put f^M_u = [f^M_n]_u. By 4a,
‖f^M_u − f^{M′}_u‖_2 = lim_u ‖f^M_n − f^{M′}_n‖_2 ≤ √K(1/M + 1/M′). So f^M_u → ξ_u in
L²(X_u,μ_u) as M → ∞. Also ‖ξ_n‖_2 ≤ K^{1/4}. For γ ∈ Γ,
|⟨κ(γ)ξ_n,ξ_n⟩ − ⟨κ(γ)f^M_n,f^M_n⟩| ≤ 2K^{1/4}√K/M, uniformly in n. So
⟨κ^{b_u}(γ)ξ_u, ξ_u⟩ = lim_M lim_u ⟨κ(γ)f^M_n, f^M_n⟩ = φ(γ). Finally,
|∫ f^M_n dμ_n| = |∫(f^M_n − ξ_n)| ≤ √K/M, so ∫ξ_u dμ_u = 0 and ξ_u ∈ L²_0(X_u).

*4c. Passing to s.* Fix F ⊂ Γ finite and ε > 0, and put F′ = F ∪ F^{−1} ∪ {e}. Simple functions
are dense in L²(X_u,μ_u), so choose f = Σ_{i<k} α_i 1_{A_i}, with (A_i) a μ_u-measurable
partition and ‖f − ξ_u‖_2 < δ. Then ⟨κ^{b_u}(γ)f, f⟩ = Σ_{i,j} α_i \bar α_j μ_u(b_u(γ)A_i ∩ A_j).
The hypothesis b_u ≃ s means, in the statistics form of
`burton-kechris-weak-class-limits-are-ultraproducts` (§2.2), that C_{n,k}(b_u) = C_{n,k}(s)
for all n,k. This is read for measurable partitions of the Loeb space, as in Step 1 of
`fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap-proof`.
So there is a Borel partition (B_i) of the Bernoulli space with
|μ(s(γ)B_i ∩ B_j) − μ_u(b_u(γ)A_i ∩ A_j)| < δ′ for γ ∈ F′ and all i, j. Take
h = Σ α_i 1_{B_i} and η = h − ∫h.
- The coefficients ⟨κ(γ)h,h⟩ and ⟨κ(γ)f,f⟩ differ by at most k²·max|α_i|²·δ′ on F′.
- ∫f = Σα_i μ_u(A_i) and ∫h = Σα_i μ(B_i) differ by at most k·max|α_i|·δ′ (use γ = e, i = j).
- |∫f| ≤ δ, since ∫ξ_u = 0.
- ‖f‖_2 ≤ ‖ξ_u‖_2 + δ.

Choose δ, then δ′ small in terms of k and max|α_i|. Then |φ(γ) − ⟨κ^s(γ)η,η⟩| < ε on F,
with η ∈ L²_0(s).

**Step 5: normalized sums over cosets.** Let ξ ∈ L^∞(X,μ) with ∫ξ = 0, and put
F_H(y) = |V|^{−1/2} Σ_{c∈V} ξ(y_c) on X^V.

- *Coefficients.* κ^{D}(γ)F_H(y) = F_H(γ^{−1}·y) = |V|^{−1/2} Σ_c ξ(a(γ)^{−1}y_{γc})
  = |V|^{−1/2} Σ_c (κ^a(γ)ξ)(y_c). The coordinates are independent with law μ, and both
  κ^a(γ)ξ and ξ have mean 0, so the cross terms c ≠ c′ vanish. Hence
  ⟨κ^{D_H(a)}(γ)F_H, F_H⟩ = ⟨κ^a(γ)ξ, ξ⟩ for all γ, and ∫F_H = 0.
- *Fourth moment.* Write ξ = ξ_1 + iξ_2 with ξ_j real, bounded and mean zero. For iid mean-zero
  real Z_c, E(Σ_c Z_c)^4 = |V|E Z^4 + 3|V|(|V| − 1)(E Z²)² ≤ 4|V|²‖Z‖_∞^4. So, by Minkowski,
  ‖F_H‖_4 ≤ 4^{1/4}(‖ξ_1‖_∞ + ‖ξ_2‖_∞), independently of H.
- *Lifting to E_H(a).* Composing F_H with the factor map E_H(a) → D_H(a) keeps the
  coefficients, the mean and the L⁴ norm.

**Step 6: the obstruction (c).** Suppose s̃ is an accumulation point of (b̃_n). Choose a
non-principal u with lim_{n∈u} b̃_n = s̃. By Theorem 10.2 in
`burton-kechris-weak-class-limits-are-ultraproducts`, ∏_n b_n/u ≃ s. For bounded mean-zero ξ,
Step 5 gives ξ_n = F_{H_n} (or its lift) with sup_n ‖ξ_n‖_4 < ∞ and
⟨κ^{b_n}(γ)ξ_n, ξ_n⟩ = ⟨κ^a(γ)ξ,ξ⟩ for all n. Step 4 shows that ⟨κ^a(γ)ξ,ξ⟩ is approximable on
finite sets by single coefficients of κ^s_0.

For arbitrary ξ ∈ L²_0(X,μ), approximate it in L² by bounded mean-zero functions, since
truncate-and-recentre converges. The coefficient functions then converge uniformly on Γ. So
every coefficient of κ^a_0 is so approximable. Since κ^s_0 ≅ ∞·λ_Γ
(`burton-kechris-tempered-actions-koopman-bernoulli`, Convention), κ^a_0 ≼ λ_Γ, i.e. a is
tempered.

**Step 7: (d) and the remarks.**
- *(d).* Assume a ≼ CIND_{H_n}^Γ(a|H_n) ≅ D_{H_n}(a) for all n (Step 2). D_{H_n}(a) is a factor
  of E_{H_n}(a), so a ≼ b_n in both cases. With u as in Step 6, weak containment of a in every
  b_n passes to b_u: a partition of X realizing a point of C_{n,k}(a) up to 1/m in b_m, for
  u-many m, gives an internal partition realizing it exactly. So a ≼ b_u ≃ s. By
  `abert-weiss-free-actions-weakly-contain-bernoulli`, s ≼ a, so ã = s̃, and
  `cost-is-constant-on-weak-equivalence-classes` gives C(a) = C(s).
- *Non-tempered free actions.* For non-amenable Γ, κ^{i_Γ × s}_0 contains the invariant
  functions of the i_Γ coordinate, hence the trivial representation, which is not weakly
  contained in λ_Γ. Tempered actions are closed downward under ≼
  (`burton-kechris-tempered-actions-koopman-bernoulli`). So no free a ≽ i_Γ × s is tempered,
  in particular not a_∞,Γ.
- *(T) and (K) give the target.* Given ε, (T) gives a tempered free a with C(a) < C(Γ) + ε,
  (K) gives E_{H_n}(a)~ → s̃, and (a) gives C(E_{H_n}(a)) ≤ C(a). If C(Γ) < C(s), choose
  C(a) < C(s): the costs stay ≤ C(a) along a sequence converging to s̃, which violates lower
  semicontinuity at s̃.
