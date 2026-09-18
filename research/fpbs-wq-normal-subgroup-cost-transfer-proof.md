---
rg: 2
id: fpbs-wq-normal-subgroup-cost-transfer-proof
kind: route
title: Start from a near-optimal graphing of the subgroup and add summably small pieces of every hull generator
target: fpbs-wq-normal-subgroup-cost-transfer
requires:
  - fpbs-wq-normal-hull-is-almost-malnormal
---

Complete proof. It is the proof of
`fpbs-wq-normal-price-one-subgroup-forces-price-one-proof` with one change: the
starting graphing is a near-optimal graphing of `R_H`, of any cost, instead of
a graphing of cost near one. Nothing in the absorption induction uses the value
of that cost.

**Imported fact** (Gaboriau, lecture notes on measure equivalence, cost and
L2-Betti numbers, Exercise 1.17 (i)=>(iii), as quoted in the price-one route):
if almost every class of a standard p.m.p. equivalence relation is infinite,
then for every `eps > 0` there is a complete section of measure at most `eps`.

**Setup.**
- Put `W := W(H)`; the restricted action `a|W` is free. By the construction in
  `fpbs-wq-normal-hull-is-almost-malnormal`, the transfinite chain
  `(W_beta)_(beta <= alpha)` has countable length, `W_0 = H`, `W_alpha = W`,
  `W_(beta+1) = <W_beta, S_beta>` with `S_beta` the set of `g in Gamma` such
  that `g W_beta g^(-1) ∩ W_beta` is infinite, and unions at limits. Every
  `g in S_beta` lies in `W_(beta+1) <= W`, so all group elements used below lie
  in `W`.
- For `L <= W` write `R_L` for the orbit relation of `a|L`. For infinite `L`,
  almost every `R_L`-class is infinite, since the action is free.
- If `C(a|H) = ∞` there is nothing to prove. Otherwise fix `eps > 0`.

**Graphing.**
- Choose a graphing `Phi_0` of `R_H` with cost at most `C(a|H) + eps/2`.
- Enumerate `∪_beta S_beta` as `g_1, g_2, ...`, let `beta_k` be the least
  `beta` with `g_k in S_beta`, and put
  `Sigma_k = g_k^(-1) W_(beta_k) g_k ∩ W_(beta_k)`, an infinite group.
- Choose a Borel complete section `A_k` of `R_(Sigma_k)` with
  `mu(A_k) <= eps/2^(k+1)`, and let `phi_k = g_k|A_k`.
- `Phi = Phi_0 ∪ {phi_k}` lies in `R_W` and has cost at most `C(a|H) + eps`.

**Absorption induction.** Exactly as in the price-one route (bullets
"Absorption" and "Induction: every `W_beta` is absorbed"): absorbed elements
form a subgroup closed under countable generation; `W_0 = H` is absorbed because
`Phi_0` generates `R_H`; limits are countable unions; and at a successor, for
almost every `x` choose `sigma in Sigma_k` with `sigma x in A_k`, so that
`x ~ sigma x ~ g_k sigma x = (g_k sigma g_k^(-1)) g_k x ~ g_k x`, where the first
and last steps use `sigma, g_k sigma g_k^(-1) in W_(beta_k) <= W_beta` and the
middle step is an edge of `phi_k`.

So every element of `W` is absorbed, `Phi` generates `R_W`, and
`C(a|W) <= C(a|H) + eps`. Let `eps -> 0`. The last sentence of the claim follows
because `d` generators of `H` acting on `X` form a graphing of `R_H` of cost
`d`. ∎
