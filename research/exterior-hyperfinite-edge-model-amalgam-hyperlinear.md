---
rg: 2
id: exterior-hyperfinite-edge-model-amalgam-hyperlinear
kind: claim
title: If some unitary model of the base makes the subgroup algebra amenable and keeps every element outside the subgroup uniformly exterior to it, then every amalgam of the base with a product of the subgroup and a hyperlinear group is hyperlinear
distinct_from:
  amenable-edge-hnn-preserves-hyperlinearity: that is the Brown--Dykema--Jung permanence for an amenable edge GROUP, applied to the canonical group factors; this needs only an amenable edge ALGEBRA in some abstract model of the base, together with an exteriority condition, and so can apply to Kazhdan edge groups, where the canonical edge factor is as far from amenable as possible.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that characterizes hyperlinearity of the central HNN group by amalgamated freeness of one Haar unitary in a trace-preserving model over the non-amenable canonical edge factor; this is a sufficient condition using a non-canonical model whose edge algebra is amenable, where freeness comes for free from Brown--Dykema--Jung.
  amenable-kazhdan-models-absorb-compression: that shows the hypothesis of this theorem fails whenever the edge group is Kazhdan and the base contains a strict compressor of it; this is the positive permanence statement, whose live instances are incompressible pairs.
---

Let `Gamma <= G` be countable groups and let `K` be a countable hyperlinear
group.  Suppose there are a Connes-embeddable von Neumann algebra `(N_1, tau)`
with faithful normal trace and an **injective** homomorphism
`pi : G -> U(N_1)` such that

```text
(E1)  P = pi(Gamma)''  is amenable;
(E2)  ||E_P(pi(g))|| < 1   (operator norm)   for every g in G - Gamma,
```

where `E_P` is the trace-preserving conditional expectation onto `P`.

**Theorem.**  `G *_Gamma (Gamma x K)` is hyperlinear.  In particular (with
`K = C_2`) the double `G *_Gamma G` is hyperlinear, and (with `K = Z`) so is
the centralizer HNN group `<G, t | [t, Gamma] = 1>`.

(E2) can be weakened to the vanishing-free chain condition of the proof route:
for every finite sequence `g_1, ..., g_m in G - Gamma` the relative tensor
`pi(g_1)^o (x)_P ... (x)_P pi(g_m)^o` is nonzero, `x^o = x - E_P(x)`.

**Scope.**  The theorem is a genuinely unitary permanence with no permutation
counterpart: Elek--Szabo/Paunescu amalgamation for sofic groups needs the edge
GROUP amenable (Folner sets glue permutation models), whereas
Brown--Dykema--Jung needs only the edge ALGEBRA hyperfinite, and an abstract
model can make a Kazhdan group generate a hyperfinite algebra
(`kazhdan-generated-amenable-algebra-is-atomic`).  That asymmetry is the shape
Pestov's Question 3.4 needs.  However, by
`amenable-kazhdan-models-absorb-compression`, (E1)+(E2) are unsatisfiable
whenever `Gamma` is Kazhdan and `G` contains a strict compressor of `Gamma`
(then `pi(t^(-1) Gamma t) <= P` and `E_P(pi(h))` is unitary for
`h in t^(-1) Gamma t - Gamma`).  So the theorem is vacuous for Kun--Thom pairs.  It is also vacuous for the
arithmetic pair `SL_3(Z) < SL_3(Z[1/p])`, by a different mechanism:
character rigidity of the S-arithmetic group forces any model with atomic
lattice algebra to be absorbed
(`sl3-atomic-ambient-is-absorbed-by-lattice`,
`sl3-pair-tracial-models-with-atomic-lattice-algebra-are-absorbed`; the
positive hypothesis `sl3-pair-admits-exterior-atomic-model` is refuted).
Its possible instances are pairs whose ambient group admits a character
that is atomic on the subgroup but not atomic itself -- no strict
compressor and no character rigidity.
