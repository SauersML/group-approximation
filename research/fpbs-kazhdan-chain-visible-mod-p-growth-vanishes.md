---
rg: 2
id: fpbs-kazhdan-chain-visible-mod-p-growth-vanishes
kind: claim
title: Along every normal chain of a Kazhdan group the mod-p homology seen by the chain grows sublinearly, at all primes at once
distinct_from:
  fpbs-kazhdan-cofinal-mod-p-growth-vanishes: that bounds all of d_p(N), but only on p-Frattini closed families such as profinitely cofinal ones; this bounds the part of d_p(Gamma_n) that factors through the chain's own finite quotients, on every normal chain with no closure hypothesis, so it reaches Lackenby-tau-type and other non-cofinal chains.
  fpbs-kazhdan-no-rapid-descent: that concerns abelian p-series with rapid descent; a normal chain here may have arbitrary finite successive quotients and no descent condition.
artifacts:
  - research/fpbs-kazhdan-chain-visible-mod-p-growth-vanishes-proof.md
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

**ESTABLISHED (written deduction).** Proof in
`research/fpbs-kazhdan-chain-visible-mod-p-growth-vanishes-proof.md`.

**Definitions.** Let `(Gamma_n)` be a descending chain of finite index normal
subgroups of a group `Gamma`. No trivial intersection, cofinality or Frattini
condition is assumed. For a finite index subgroup `H`, the *visible mod-`p`
rank* is `d_p^vis(H) = dim` of the space of homomorphisms `H -> F_p` whose
kernel contains some `Gamma_m`. Equivalently:
- `d_p^vis(H) = sup_m d_p(H Gamma_m / Gamma_m)`;
- `d_p^vis(H)` is the rank of the continuous mod-`p` abelianization of the closure of `H` in the chain completion `lim Gamma/Gamma_m`.

**Theorem.** Let `Gamma` have property (T) and let `(Gamma_n)` be any descending
chain of finite index normal subgroups.
1. For every prime `p`, `d_p^vis(Gamma_n)/[Gamma:Gamma_n] -> 0`.
2. (All primes.) `sup_m d((Gamma_n/Gamma_m)^ab)/[Gamma:Gamma_n] -> 0`. Here
   `d((Gamma_n/Gamma_m)^ab)` is the minimal number of generators of the abelianization of the
   finite group `Gamma_n/Gamma_m`.

The same holds for every downward directed family of finite index normal
subgroups, with the limit taken along the directed set.

**What it kills.** Every abelian homological certificate for
`fpbs-kazhdan-positive-rank-gradient` that is read off the finite quotients
`Gamma/Gamma_m` of the chain itself. This covers any prime, any combination of
primes, and any normal chain, cofinal or not. That is the whole of survivor 1
of `research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md` for
normal chains. By Abert--Nikolov, the profinite boundary action of a normal
Farber chain has cost `1 + RG`. So a Kazhdan fixed-price counterexample built
this way must take its generators from one of three sources:
- (a) *invisible* classes of `Gamma_n`, whose kernels contain no member of the chain;
- (b) non-central abelian or non-abelian crowns of the finite quotients `Gamma_n/Gamma_m` (lane `sw-027` on twisted modules);
- (c) the gap between `d(Gamma_n)` and `sup_m d(Gamma_n/Gamma_m)`.

**Structural point.** Theorem B of the artifact needed a member of the family
inside the full mod-`p` Frattini subgroup `Phi_p(pi A)`. The new input is
this: run the Frattini step through the *visible Frattini subgroup*
`Phi^vis(H)`, the intersection of the kernels of the visible classes. It
always contains a member of the chain, and its quotient is elementary abelian of
rank `d_p^vis(H)`. So Lackenby's Theorem 5.1 applies to it. Growth inheritance
through the coprime descent is checked on a deep finite quotient `A'/Gamma_m`,
where Lackenby's Lemma 3.3 is an inequality about finite groups.

**Calibration.**
- `F_2`, along the family of all normal subgroups of `p`-power index, has `d_p^vis(N) = [F_2:N] + 1`. Every step of the proof runs, and only the Kazhdan support bound fails.
- Theorem B of the artifact is the special case of `p`-Frattini closed families, where `d_p^vis = d_p`.
- Lackenby's (tau) chains (arXiv:math/0509036) are subnormal, not normal, so the theorem does not apply to them.

**Scope.**
- Not covered: subnormal chains. The descent step needs the member `N` normal in `A'`.
- Not covered: sources (a), (b), (c) above.
- First falsifiable step toward (a): exhibit, in any finitely presented Kazhdan group, a normal chain with `(d_p(Gamma_n) - d_p^vis(Gamma_n))/[Gamma:Gamma_n]` bounded below, or show that invisible classes can be made visible by refining the chain without lowering `RG`.
