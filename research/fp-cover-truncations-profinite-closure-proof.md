---
rg: 2
id: fp-cover-truncations-profinite-closure-proof
kind: route
title: Finite quotients of a quotient group are the open normal subgroups containing the closure of its kernel
target: fp-cover-truncations-see-kernel-iff-profinite-closures-differ
requires: []
---

Notation as in the claim. For a normal subgroup `M ◁ Γ~`, the finite
quotients of `Γ~/M` correspond to the finite-index normal subgroups of `Γ~`
containing `M`. These correspond to the open normal subgroups `V` of `Γ~^`
with `V ∩ Γ~ ⊇ M`. An open subgroup is closed, so `V ⊇ M` is equivalent to
`V ⊇ cl(M)`. Hence `(Γ~/M)^ = Γ~^/cl(M)`, and closed normal subgroups of `Γ~^`
are intersections of the open normal subgroups containing them.

**Item 1.** A homomorphism `Γ_L -> Q` with `Q` finite corresponds to an open
normal `V ⊇ cl(N_L)` of `Γ~^`, and it is nontrivial on `K_L` exactly when
`V ⊉ N`, i.e. `V ⊉ cl(N)`.
- If `cl(N_L) = cl(N)`, every open normal `V ⊇ cl(N_L)` contains `cl(N)`, so
  `K_L` dies in every finite quotient.
- If `cl(N_L) ≠ cl(N)`, then since `cl(N_L)` is the intersection of the open
  normal subgroups containing it, some such `V` does not contain `cl(N)`.
  Then `V` gives a finite quotient in which `K_L` survives.

**Item 2.** `N_L <= N_(L+1) <= N` gives `cl(N_L) <= cl(N_(L+1)) <= cl(N)`.
If `cl(N_(L+1)) ≠ cl(N)` then `cl(N_L) ≠ cl(N)`. Apply item 1 twice.

**Item 3.** `Γ_L^ = Γ~^/cl(N_L)` and `Γ^ = Γ~^/cl(N)`, and the natural map is
the quotient map by `cl(N)/cl(N_L)`. It is an isomorphism exactly when
`cl(N_L) = cl(N)`. Apply item 1.

**Consequence.** The claim's reformulation of
`sl3-polynomial-covers-have-extra-finite-quotients` is items 1--3 applied to
`Γ = SL_3(F_q[t])`, with `N_L = <<n_1, ..., n_L>>`.
