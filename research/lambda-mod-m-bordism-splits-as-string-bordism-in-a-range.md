---
rg: 2
id: lambda-mod-m-bordism-splits-as-string-bordism-in-a-range
kind: claim
title: For m divisible enough, lambda-mod-m bordism agrees with string bordism tensored with K(Z,4) through any given degree, so trapping towers see string-visible commutators without string steps
distinct_from:
  spin-m-trapping-factors-through-string-bordism: That shows every Spin_m detector factors through MString (a necessary condition); this shows that for highly divisible m the detector is MString itself through a range (a sufficient condition).
  quaternionic-flag-trapping-steps-are-never-string: That rules out string trapping steps from quaternionic flags; this makes string steps unnecessary, since Spin_m steps with m divisible by m_k already detect every string-visible class below degree k.
---

Let BSpin_m -> BSpin be the homotopy fibre of lambda mod m, MSpin_m its Thom
spectrum, and MString -> MSpin_m the E_∞ ring map of
spin-m-trapping-factors-through-string-bordism. Let K = K(Z, 4) and K^(k)
its k-skeleton.

(a) For every k >= 4 there is m_k >= 1 such that for every multiple m of
    m_k there is an equivalence through degree k − 1,

        MString ∧ Sigma^∞_+ K^(k)  ->  MSpin_m,

    whose restriction to MString ∧ S^0 is the ring map. So MString is a
    retract of MSpin_m through degree k − 1. Example: m_4 = 24, and
    pi_3 MSpin_m ≅ Z/24 once 24 | m.
(b) For every multiple m of m_k, every space or connective spectrum X and
    every n < k, the map MString_n(X) -> MSpin_m_n(X) is split injective,
    naturally in X.
(c) Transfer. Let M be a closed string manifold, u_1, ..., u_s in C(M, M_N)
    unitaries and w a word with f = w(u_1, ..., u_s). If the reduced class
    of f_*[M] in MString~_{dim M}(U(N)) is nonzero, then for every multiple
    m of m_{dim M + 1}, [M, f]_red != 0 in Omega-tilde^{Spin_m}_{dim M}(U(N)),
    and unitary-word-transfer-to-simple-ah-via-trapping gives a simple unital
    AH algebra in which w stays outside U_0.
(d) Trapping sees string bordism. With
    spin-m-trapping-factors-through-string-bordism: in protected rank N a
    c-fold commutator is Spin_m-visible for some m only if MString ∧ s_c is
    essential, and it is Spin_m-visible for m divisible by m_{n+1} whenever
    some string seed of dimension n has a nonzero string-bordism image.

So string (tmf-type) detection is available to trapping towers through the
quaternionic steps Gr_m(H^{m+pd}) with m divisible by m_k. No step with
lambda-defect zero is needed. The class-five problem, and the every-depth
crux, become questions about MString ∧ Sigma^∞ cbar_c.

Proof: lambda-mod-m-string-range-splitting-proof. Complete argument, using
standard parametrized Thom spectrum theory (Ando–Blumberg–Gepner–Hopkins–
Rezk) recalled without re-verifying theorem numbers. Not independently
reviewed. Novelty was checked only against the repo graph.
