---
rg: 2
id: entropy-profile-proofs-of-bernoulli-maximality-relativize
kind: claim
title: Every entropy-profile proof of Bernoulli Rokhlin maximality also proves full relative entropy of Bernoulli extensions over every action
distinct_from:
  bernoulli-rokhlin-deficit-has-a-finitary-witness: that computes rho_q(G) as an infimum of Phi over genuine codes; this relaxes genuine codes to invariant almost-entropic profiles and bounds that relaxation above by the relative entropy over any side-information action.
  seward-direct-product-relative-rokhlin-entropy-conjecture: that is Seward's open equality h(X x Y | B(Y)) = h(X) for free X, Y; this proves that any entropy-profile proof of maximality settles its Bernoulli case for every Y at once, so such a proof is at least as strong as that case.
  weak-invariants-give-no-bernoulli-rokhlin-lower-bound: that kills lower bounds through weak-equivalence invariants of the shift; this kills nothing outright but shows that information-inequality proofs cannot tell a genuine code from a code with free side information.
  rokhlin-permanence-toolkit-certifies-only-sofic-groups: that bounds what permanence operations certify; this bounds what Shannon-type counting on one group certifies.
---

**ESTABLISHED (unreviewed)** by [[entropy-profile-proofs-of-bernoulli-maximality-relativize-proof]]. This is a barrier result. It does not refute anything, but it names the one test that would kill a whole class of proofs.

**Setting.** Let `G` be countable and `|A| = q >= 2`. The variables are `x_a` and `y_a` for `a in G`. The support of `x_a` is `{a}`, and the support of `y_a` is `aE` for a fixed finite `E`.

An **entropy profile** for `(k, E)` assigns a number `h(S)` to each finite set `S` of variables, subject to these conditions.
- **(H1)** On every finite ground set, `h` lies in the closure of the entropic cone. So `h` satisfies every Shannon and non-Shannon linear information inequality.
- **(H2)** `h(gS) = h(S)` for every `g in G`.
- **(H3)** `h({x_a : a in T}) = k |T| log q`.
- **(H4)** `h(y_g | x_(gE)) = 0`.
- **(H5)** For finite `S`, `T` and `W` with `supp S ∩ supp T ⊆ W`, `I(S ; T | x_W) = 0`.

Define

    rho^prof_q(G) = inf over k, E, F and profiles h of  (1/k) [ h(y_1) + h(x_1 | y_F) ].

The joint entropies of a genuine configuration `(k, E, F, psi)` form a profile. So `rho^prof_q(G) <= rho_q(G)`, where `rho_q(G)` is the infimum of `Phi` in `bernoulli-rokhlin-deficit-has-a-finitary-witness`.

An **entropy-profile proof** of `Phi >= c log q` on `G` is any argument that establishes `rho^prof_q(G) >= c log q`. This covers:
- derivations from linear information inequalities together with invariance, independence of the input, locality of the code and conditional independence of disjoint windows;
- auxiliary independent label fields, such as the random order of `rokhlin-window-random-order-transport-identity` (proof, Remark 2).

It does not cover arguments that use the identity of the code across sites beyond invariance of its joint law. Examples are evaluation on constant or periodic inputs, sofic microstate counting and algebraic structure of `psi`.

**Theorem.** For every p.m.p. action `G ↷ (Ω, ν)` (not necessarily free or ergodic) and every `k >= 1`,

    rho^prof_q(G)  <=  h_G( (A^k)^G × Ω | B(Ω) ) / k .

Here relative Rokhlin entropy is `inf H(P | B(Ω))` over countable partitions `P` with `σ(G·P) ∨ B(Ω) = B`. The invariant sets of the product lie in `B(Ω)`, because the shift is mixing.

**Consequences.**
1. **Relativization.** An entropy-profile proof that `G` is Rokhlin-maximal proves that `h_G((A^k)^G × Ω | B(Ω)) = k log q` for every p.m.p. action `Ω` of `G`. That is the Bernoulli case of `seward-direct-product-relative-rokhlin-entropy-conjecture`, for all `Y` at once. An entropy-profile proof of the flagship proves this for every group and every action.
2. **Only the orbit relation matters.** For free `Ω`, the relative entropy in the Theorem is an invariant of the orbit relation `R_Ω` (proof, Proposition 4). It is the relative entropy of the Bernoulli class-bijective extension of `R_Ω`.
3. **The decisive test lies over a nonsofic relation.** `kun-thom-free-nonsofic-action` gives a residually finite Kazhdan group `G_KT` with a free nonsofic action `Ω_KT`. The flagship is known for `G_KT`, which is sofic.
   - An entropy-profile proof of maximality over `G_KT`, and so any entropy-profile proof of the flagship, would prove `kun-thom-nonsofic-action-carries-full-bernoulli-entropy`.
   - That would be a lower bound over a nonsofic orbit relation. No sofic counting reaches it, since relative sofic entropy needs sofic models of `Ω_KT`.
4. **Window certificates are covered.** The minimal-window Shannon LP of `torsion-free-windows-have-minimal-shannon-certificates` uses only independent unit `x`, `y_g` a function of `x_(gE)`, translation invariance and Shannon inequalities. All of these hold for every profile. So that claim, if true, gives `h_G((A^k)^G × Ω | B(Ω)) = k log q` for every torsion-free `G` and every p.m.p. action `Ω`. That is the Bernoulli case of Seward's direct-product conjecture for all torsion-free groups.
5. **Kill criterion.** Suppose some action `Ω` of some group `G` has `h_G((A^k)^G × Ω | B(Ω)) < k log q`. Then no entropy-profile proof establishes maximality over `G`, nor the flagship.

**Calibration.** For amenable `G` the relativized statement is true: relative Kolmogorov–Sinai entropy of a direct product with a Bernoulli factor equals the base entropy. This is consistent with the Følner and codeword-Følner-ratio arguments in the graph, which are entropy-profile proofs.

**Reading.** The graph's information-inequality attempts on the flagship (reading sunflowers, codeword Følner counting, random-order transport) cannot tell a code from a code that sees free side information. Any successful proof of that kind proves the harder relative statement over every nonsofic free action of every group. A proof that uses only the flagship's own strength must use the uniformity of `psi` in a way that is not visible in joint entropies.
