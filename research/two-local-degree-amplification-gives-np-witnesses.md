---
rg: 2
id: two-local-degree-amplification-gives-np-witnesses
kind: claim
title: An energy-monotone degree-amplifying map on 2-local Hamiltonians would put constant-gap energy estimation in NP
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
distinct_from:
  bmvz-iterable-tensor-gap-amplification: that is a proved amplifier which multiplies locality by 2t on qubits; this is the Brandao--Harrow no-go for amplifiers that keep locality two and raise degree and local dimension, which that amplifier does not attempt.
  quantum-pcp-constant-gap-local-hamiltonian: that is the conjecture at some constant locality; this is a conditional collapse for the 2-local qudit form only, under the existence of a specific kind of map.
---

**ESTABLISHED BY CITATION** (Brandao--Harrow, arXiv:1310.0017v2, Corollary 11 and
its proof in Section 6).

Suppose that for every `t>=1` there is a map `P_t` from normalized 2-local
Hamiltonians on `d`-dimensional particles to normalized 2-local Hamiltonians on
`n_t` particles of dimension `d_t` such that

1. `P_t` is computable deterministically in polynomial time;
2. `P_t(H)=E_((i,j)~G') H'_ij` with `G'` a probability distribution and `||H'_ij||<=1`;
3. the constraint graph of `P_t(H)` is regular of degree at least `deg(H)^t`;
4. `n_t<=n^(O(t))` and `d_t=d^t`;
5. `e_0(P_t(H))>=e_0(H)` if `e_0(H)>0`, and `e_0(P_t(H))<=e_0(H)` if `e_0(H)<=0`.

Then for every constant `d` and `eps>0`, deciding `e_0(H)<=0` versus
`e_0(H)>=eps` for such Hamiltonians is in NP. So, if NP is not QMA, the
2-local qudit form of the quantum PCP conjecture is false.

**Fidelity notes.** The source states item 3 as `deg(P_t(H))>=deg(H)^t`. Its
proof applies Corollary 5, which is stated for `D`-regular constraint graphs,
to `P_t(H')`, so item 3 is written here in the form the proof uses. The proof
also says it neglects discretization arithmetic; Corollary 5 already carries the
precision parameter `delta`.

**Reading.** In the source's words, quantizing the gap amplification part of
Dinur's proof in this form "would disprove the quantum PCP conjecture". The
known quantum amplifiers (AALV, BMVZ, the global tensor walk) avoid the
hypotheses by growing locality instead. The open composition step
`locality-reduction-with-amplifier-independent-loss` must also avoid them.
