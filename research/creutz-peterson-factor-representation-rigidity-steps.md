---
rg: 2
id: creutz-peterson-factor-representation-rigidity-steps
kind: claim
title: The Creutz-Peterson steps from proper outerness to finite-dimensionality of non-regular factor representations
distinct_from:
  irs-rigid-simple-dense-subgroups-act-properly-outer: that proves proper outerness for IRS-rigid simple dense subgroups; this imports the general steps of Creutz--Peterson that consume proper outerness.
  character-rigidity-equals-hyperfinite-hs-stability: that imports Dogon--Vigdorovich's equivalences for higher rank Lie lattices; this imports operator-algebraic rigidity steps for commensurators and product lattices.
---

**ESTABLISHED (literature import, unreviewed).** Creutz--Peterson, *Character rigidity for
lattices and commensurators*, arXiv:1311.4513v3 (TeX `creutzpeterson_revised2.tex`), numbered
as in that version. Here "factor representation" means `π: Λ -> U(M)` with `M` a finite factor
and `π(Λ)'' = M`. For a dense `ι: Λ -> G`, the `G`-algebra of `π` is
`M_0 = {x in M : ||π(λ_n) x π(λ_n^(-1)) - x||_2 -> 0 whenever ι(λ_n) -> e}`, with its
continuous action `α_g(x) = lim_{ι(λ) -> g} π(λ) x π(λ^(-1))`.

```text
(CP-a) Lemma 4.3. G Polish, Λ<G countable dense, every trace preserving ergodic action of G
       on a finite von Neumann algebra properly outer on Λ  =>  for every factor
       representation π of Λ the G-algebra of π is C.
(CP-b) Theorem 4.4. G Polish, Λ<G countable dense meeting every proper closed normal
       subgroup trivially, G acts ergodically on (Y,η), π a factor representation of Λ whose
       G-algebra is C, N ⊂ M a subalgebra, π not extending to L Λ ≅ M  =>
       {σ^0_λ ⊗ J E_N(π(λ)) J}' ∩ L^∞(Y) ⊗ B(L^2 N) = 1 ⊗ N.
(CP-c) Proof of Theorem 5.4, read without its hypotheses (i)/(ii): G lcsc, Γ<G a lattice,
       Λ<G countable dense containing and commensurating Γ and meeting every proper closed
       normal subgroup trivially, and every continuous ergodic trace preserving action of G on
       a finite von Neumann algebra ≠ C with separable predual properly outer on Λ.  If π is a
       factor representation of Λ not extending to LΛ ≅ M, then N = π(Γ)'' is injective.
(CP-d) Proof of Corollary 5.5. If moreover G has (T), then π(Γ) is precompact in the strong
       operator topology (Robertson, Theorem C) and N is completely atomic.
(CP-e) Proposition 6.1. G lcsc, H ◁ G closed, Γ<G a lattice with dense image in G/H, π a
       factor representation of Γ, and π(Γ_U) precompact for some compact neighbourhood U of
       the identity in G/H, where Γ_U = {γ : γH in U}  =>  the G/H-algebra M_0 has finite
       index in M; in the proof, M_0 ⊇ N' ∩ M for a finite-dimensional N ⊂ M.
(CP-f) Opening of the proof of Proposition 4.1. If α_g(x) v = v x for all x in M_0, then
       |v| in Z(M_0), v may be taken a partial isometry with v*v = vv* central,
       α_g(v*v) = v*v, and α_g(q) = q for central projections q <= v*v; if M_0 is a factor,
       v is a unitary.
(CP-g) Introduction. The characters of a countable group form a Choquet simplex whose extreme
       points correspond to representations generating a finite factor (Thoma).
```

**On the reading in (CP-c).** Creutz--Peterson do not state (CP-c) in this form. Their
Theorem 5.4 assumes either connected factors or a square-integrable lattice with a non-torsion
element. Its proof, quoted in full in the citation route, uses those hypotheses only through
Proposition 4.1, inside Lemma 4.3. Lemma 4.3 in turn applies the proper-outerness hypothesis
only to the `G`-algebra of `π`, a subalgebra of `M` with separable predual. The citation route
shows the quoted text, so the reading can be checked.

Citation: `creutz-peterson-factor-rigidity-steps-citation`.
