---
rg: 2
id: spin-m-trapping-factors-through-string-bordism
kind: claim
title: Every lambda-mod-m bordism detector of unitary commutators factors through string bordism, so a Spin_m-visible c-fold commutator needs a string-visible stable commutator map
distinct_from:
  spin-trapping-blind-to-fourfold-commutators-in-every-rank: That kills spin bordism (m = 1) at depth three through ko-module splittings; this compares all m at once with string bordism, where no splitting is known and nu, kappa and kappa-bar survive.
  unitary-word-transfer-to-simple-ah-via-trapping: That turns one Spin_m-visible word into a simple AH algebra; this gives a necessary condition, independent of m, for such a word to be a nested commutator.
---

Let G = U(N) with N >= 1. Let cbar_c: G^{∧c} -> G be the c-fold nested
commutator map, (g_{c−1}, ..., g_1, h) -> [g_{c−1}, [..., [g_1, h]...]],
and s_c = Sigma^∞ cbar_c. Let MString = MO<8> be the Thom spectrum of
BString -> BO, and MSpin_m the Thom spectrum of BSpin_m -> BO, where
BSpin_m -> BSpin is the homotopy fibre of lambda mod m (2·lambda = p_1).

(a) For every m >= 1 there is a map of E_∞ ring spectra MString -> MSpin_m
    over the identity of S.
(b) Let f: A -> B be a map of spectra. If the composite
    A -f-> B -> MString ∧ B, with the unit of MString, is null, then
    MSpin_m ∧ f is null for every m >= 1.
(c) Fix c and N. Suppose MString ∧ s_c is null. Then for every m >= 1,
    every closed Spin_m-manifold M and all maps g_1, ..., g_{c−1}, h: M -> G,
    the commutator f = [g_{c−1}, [..., [g_1, h]...]] has [M, f]_red = 0 in
    Omega-tilde^{Spin_m}_{dim M}(G). So every trapped class of the transfer
    theorem (unitary-word-transfer-to-simple-ah-via-trapping), for every m,
    vanishes on the seed witnesses (f o pr_M) (+) 1_Q.
(d) Contrapositive. A class-five input for the transfer theorem in protected
    rank N, for any m, forces MString ∧ s_5 not to be null for G = U(N).

So the choice of m cannot buy depth beyond what string bordism sees in the
stable commutator map. String bordism need not be available as a trapping
detector: no step family with zero lambda-defect and odd Euler count is known
(quaternionic-flag-trapping-steps-are-never-string). The condition in (d) is
necessary and not sufficient. Proof: spin-m-trapping-string-factorization-proof.
Complete argument. Not independently reviewed.
