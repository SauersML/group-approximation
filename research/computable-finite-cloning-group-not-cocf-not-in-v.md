---
rg: 2
id: computable-finite-cloning-group-not-cocf-not-in-v
kind: claim
title: "Some computable cloning system on finite groups has a Thompson-like group with a finitely generated subgroup of solvable word problem that is not coCF and does not embed in V"
distinct_from:
  some-finite-cloning-system-group-is-not-locally-cocf: that is the bare existence statement of Problem 2.16 Q1 no, established by a witness built from a non-recursive set (unsolvable word problem, non-computable data); this adds computability of the cloning system and solvability of the word problem, and the obstruction is running time, not undecidability.
---

**Claim.** There is a properly graded pure binary cloning system `(G_n, ι, ρ ≡ 1, κ)` on
finite groups such that:

1. the data are computable: there is an algorithm that on input `n` outputs `G_n` (as a
   finite abelian group `(Z/2)^{D_n}` with an explicit index set `D_n`), the maps
   `ι_{n,n+1}` and `κ^n_k`;
2. `T(G_*)` is finitely generated, and its subgroup `Γ = ⟨x_0, x_1, t⟩ ≅ Z/2 ≀_{F/H} F` (for a suitable `H ≤ F`, below)
   has solvable word problem;
3. `Γ` is not coCF. Hence `T(G_*)` is not coCF, and neither `Γ` nor `T(G_*)` embeds in
   Thompson's group `V`.

So the negative answer to Zaremsky Problem 2.16 recorded in
`finite-cloning-group-with-undecidable-lamp-stabilizer` and
`finite-cloning-undecidable-lamp-stabilizer-not-in-v` is not an artefact of
non-computable input. The witness is the coset-tree cloning system of
`finite-cloning-groups-realize-every-lamplighter-over-thompson-f` for a subgroup
`H = H_S ≤ F` built from a recursive set `S` that is not decidable in time polynomial in
`i`. Complete proof: route `computable-finite-cloning-group-not-cocf-not-in-v-proof`.

**Why it matters.** A coCF group, and every finitely generated subgroup of `V`, has a
word problem decidable in polynomial time. Coset-tree cloning systems transport the running
time of an arbitrary recursive set into the word problem of `T(G_*)`. So any positive
answer to Q1 or Q2 would have to restrict the cloning systems by a complexity or
finiteness condition on the cloning maps (for example "local" or "finite-state" cloning),
not just by computability. That is where Lehnert-relevant witnesses must be sought.
