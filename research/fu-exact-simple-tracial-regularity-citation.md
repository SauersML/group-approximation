---
rg: 2
id: fu-exact-simple-tracial-regularity-citation
kind: route
title: Import Fu's Theorem 1.1 and Corollary 9.2 on divisibility and real rank zero
target: fu-exact-simple-tracial-regularity-equivalences
requires: []
artifacts:
  - research/artifacts/stw18-k1-witness-tracial-divisibility-2026-09-16.md
---

**Established by citation.** Xuanlong Fu, *Divisibility and Real Rank Zero*,
[arXiv:2605.21655v1](https://arxiv.org/abs/2605.21655), submitted 2026-05-20.
This is an unrefereed preprint. The HTML full text was read on 2026-09-16.

**Theorem 1.1, verbatim:** "Let A be an algebraically simple separable
non-elementary C*-algebra with QT~(A)≠{0}. Consider the following regularity
properties: (1) Γ:Cu(A)→LAff_+(QT~(A)) is hereditary dense (see Definition
4.3). (2) A has tracial approximate oscillation zero. (3) l^∞(A)/J_A has real
rank zero. (4) A is tracially diagonally divisible (see Definition 7.1). (5) A
has Property (TM). (6) A is tracially almost divisible. (7) A is tracially
m-almost divisible for some m∈N∪{0}. (8) A is weakly tracially diagonally
divisible (see Definition 7.3). Then (1)⇒(2)⇔(3)⇒(4)⇒(5)⇒(6)⇒(7) always holds.
If in addition A is exact, then (7)⇒(8)⇒(1) holds and thus all properties are
equivalent."

**Corollary 9.2, verbatim:** "Let A be an algebraically simple separable exact
C*-algebra with QT(A)≠∅. If Cu(A) is m-almost divisible for some m∈N∪{0}, then
l^∞(A)/J_A has real rank zero." Just before it Fu recalls the definition: "for
all a∈M_∞(A) and all k∈N there is x∈Cu(A) such that kx≤[a]≤(k+1)(m+1)x ([40,
Definition 3.5])".

**Definitions, as printed:**

- **Definition 3.1.** `QT(A) = {τ ∈ QT~(A) : ‖τ|_A‖ = 1}`, where
  `‖τ|_B‖ = sup{‖τ(b)‖ : b ∈ Ped(B)^1_+}`.
- **Definition 3.3.** `‖x‖_2 = sup{‖x‖_{2,τ} : τ ∈ closure QT(A)^w}`, with
  `‖x‖_{2,τ} = τ(x*x)^{1/2}` on `Ped(A⊗K)`.
- **Definition 7.5.** "We say A has Property (TM) if for all a∈Ped(A⊗K)^1_+, all
  n∈N, all ε>0, there is a c.p.c. order zero map φ:M_n→Her(a) such that
  ‖φ(1_n)a−a‖_2<ε."
- **Definition 8.1**, citing Winter [Invent. Math. 187 (2012), Definition
  3.5(ii)]. "We say A is tracially m-almost divisible, if for all m∈N and all
  a∈M_m(A)^1_+, all n∈N, and all ε>0, there is a c.p.c. order zero map
  φ:M_n→Her(a) such that τ(1_n)≥(1/(m+1))·τ(a)−ε for all τ∈QT(A). We say A is
  tracially almost divisible, if A is tracially 0-almost divisible."

**Typographical slips in Definition 8.1.** The printed text reuses `m` for the
matrix size, and it writes `τ(1_n)` for `τ(φ(1_n))`. The target claim states
the definition in the form Fu cites, which is Winter's: arbitrary matrix size
and `τ(ψ(1_k))`. That source was read in the LaTeX of arXiv:1006.2731v2.

The reading of the typo is the only interpretive step.
