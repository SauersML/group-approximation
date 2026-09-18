---
rg: 2
id: fpbs-coinduced-dilution-needs-tempered
kind: claim
title: Diluting a cheap free action by co-induction from finite-index subgroups keeps the cost but can reach the Bernoulli class only if the action is tempered
distinct_from:
  fpbs-bernoulli-weak-class-cheap-approximability: that is the open approximation statement; this proves that the natural cheap approximants obtained by co-inducing restrictions to finite-index subgroups keep the cost bound, and that a Bernoulli limit forces the diluted action to be tempered.
  fpbs-bernoulli-class-cost-jump-is-cgdls-ultraproduct-gap: that computes the cost of the ultraproduct along s̃-convergent sequences; this constrains the Koopman representation of the ultraproduct through fourth-moment-bounded vectors.
  burton-kechris-tempered-actions-koopman-bernoulli: that imports the definition of tempered actions; this proves a transfer of non-tempered Koopman coefficients into every ultraproduct of diluted actions.
---

**ESTABLISHED.** Let Γ be an infinite finitely generated group, a : Γ ↷ (X,μ) a free p.m.p.
action on a standard non-atomic space, and s a nontrivial Bernoulli shift of Γ.

**Diluted actions.** For a finite-index subgroup H ≤ Γ put V = Γ/H and let D_H(a) be the
action of Γ on (X^V, μ^V) given by (g·y)_c = a(g) y_{g^{−1}c}. Put E_H(a) = D_H(a) × (Γ ↷ Γ/H),
with the uniform measure on Γ/H. D_H(a) is isomorphic to the co-induced action
CIND_H^Γ(a|H).

(a) **Cheapness.** D_H(a) and E_H(a) are free, and C(E_H(a)) ≤ C(a).

(b) **Koopman witness lemma.** Let b_n be p.m.p. actions of Γ on standard spaces and u a
    non-principal ultrafilter with ∏_n b_n/u ≃ s. Let ξ_n ∈ L²_0(b_n) with
    sup_n ‖ξ_n‖_4 < ∞, and φ(γ) = lim_{n∈u} ⟨κ^{b_n}(γ)ξ_n, ξ_n⟩. Then for every finite F ⊂ Γ
    and ε > 0 there is η ∈ L²_0(s) with |φ(γ) − ⟨κ^s(γ)η,η⟩| < ε for all γ ∈ F.

(c) **Obstruction.** Let (H_n) be any sequence of finite-index subgroups, and b_n = D_{H_n}(a)
    or b_n = E_{H_n}(a). If s̃ is an accumulation point of (b̃_n) in F̃R(Γ,X,μ), then a is
    tempered: κ^a_0 ≼ λ_Γ.

(d) **Link with Kechris's co-induction problem.** If a ≼ CIND_{H_n}^Γ(a|H_n) for all n (the
    finite-index case of Burton–Kechris Problem 3.24, where Γ ↷ Γ/H_n is amenable), then
    s̃ is an accumulation point of (b̃_n) only if ã = s̃, and then C(a) = C(s).

**What is killed.** Dilution by co-induction is the one natural operation that keeps the cost
of a fixed cheap action while spreading it over independent coordinates. By (c), for a
non-tempered cheap a it never produces approximants of s̃. This holds for every sequence of
finite-index subgroups, including Farber chains, and for both co-induced and induced forms.
The invariant is the Koopman coefficient ⟨κ^a(γ)ξ,ξ⟩. It is carried by the normalized sum
|V|^{−1/2} Σ_c ξ(y_c), which is bounded in L⁴, so it survives in the ultraproduct. The step
where the approach dies is κ^{b_u}_0 ≼ κ^s_0 ≅ ∞·λ_Γ. For non-amenable Γ every free
a ≽ i_Γ × s, including a_∞,Γ, is not tempered. So by this mechanism
`fpbs-bernoulli-weak-class-cheap-approximability` can only come from tempered cheap actions,
and by (d) only against a negative answer to the finite-index case of Problem 3.24.

**Surviving shape.** A proof of the target by dilution needs both of the following:
- (T) inf{C(a) : a free and tempered} = C(Γ), i.e. C(ã^temp_∞,Γ) = C(Γ);
- (K) for every free tempered a with C(a) < C(Γ) + ε, some sequence (H_n) has
  E_{H_n}(a)~ → s̃.

Each can fail on its own. (T) is a fixed-price question inside the closed tempered classes.
(K) contradicts the finite-index case of Problem 3.24 whenever ã ≠ s̃. Conversely,
(T) and (K) together give the target for Γ, and a failure of
`fpbs-bernoulli-weak-class-cost-lsc` whenever C(Γ) < C(s).

Proof: `fpbs-coinduced-dilution-needs-tempered-proof`.
