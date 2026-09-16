---
rg: 2
id: sp21-finite-congruence-kernel-forbids-p-goodness-proof
kind: route
title: Split the finite kernel off an open subgroup, find a D-dimensional uniform subgroup, and compare Lazard's cd_p with the 8-dimensional symmetric space
target: sp21-finite-congruence-kernel-forbids-p-goodness
requires: []
artifacts:
  - research/artifacts/sp21-congruence-goodness-2026-09-16.md
---

**Imported inputs.** These are statements only. The sources were not re-read in this
session, and the numbering is from memory.
- **(I1) Cartan.** `X = Sp(2,1)/(Sp(2)×Sp(1)) ≅ R^8`.
- **(I2) Strong approximation.** Platonov–Rapinchuk Theorem 7.12: `G(k)` is dense in
  `G(A_f)`, since `G_∞` is noncompact.
- **(I3) Uniform subgroups.** Lazard; Dixon–du Sautoy–Mann–Segal Corollary 8.34: every
  compact p-adic analytic group has an open uniform subgroup, which is torsion-free of the
  same dimension.
- **(I4) Lazard.** A torsion-free compact p-adic analytic group of dimension `d` has
  `cd_p = d`.
- **(I5) Closed subgroups.** Serre, *Galois Cohomology*, I §3.3: `cd_p(H) <= cd_p(G)`.
- **(I6) Simple-module test.** Serre I §3.1 and §4.1: `cd_p(G) <= n` iff `H^{n+1}(G;A) = 0`
  for all simple discrete `A` killed by `p`. For pro-p `G`, it suffices to take
  `A = Z/p`.
- **(I7) Direct limits.** Serre I §2.2: `H^q(H;A) = lim→ H^q(V;A)` over the open
  `V ⊇ H`.

**Proof.** Full details are in the artifact, §§2–3.

1. **Discrete side.** Every finite-index `Γ_1 <= Γ` acts freely, properly and
   cocompactly on `X`. By (I1), `Γ_1\X` is a closed aspherical 8-manifold. So
   `H^q(Γ_1;-) = 0` for `q >= 9`.
2. **Openness.** By (I2), `G(O)` is dense in `G(O^)`. So the closure `Γ̄_1` of a
   finite-index `Γ_1` has finite index and is open. Projecting, `Δ̄_p` is open in
   `G_p = ∏_{𝔭 | p} G(O_𝔭)`.
3. **Completions of subgroups.** The closure `V_1` of `Γ_1` in `Γ^` is open and is
   `Γ_1^`. It maps onto `Γ̄_1` with kernel `C ∩ V_1`, which is finite.
4. **Splitting.** If a surjection of profinite groups has finite kernel `K`, some open
   normal `M` meets `K` trivially. Then `M` maps isomorphically, as a topological group,
   onto an open subgroup of the target.
5. **Dimension.** An open subgroup `W` of `G(O^)` contains a basic open subgroup. That
   subgroup contains `L`: a closed copy of an open subgroup of `G_p`, with the other
   coordinates trivial. `L` is compact p-adic analytic of dimension
   `Σ_{𝔭 | p} 21·[k_𝔭:Q_p] = 21·[k:Q] = D`. By (I3) and (I4), `L` has a uniform open
   `U` with `cd_p(U) = D`.
6. **Item 1.** Apply step 4 to `Γ_1^ ->> Γ̄_1` and step 5 to `W = π(M)`. Pulling `U` back
   gives a closed subgroup `U' <= Γ_1^` with `U' ≅ U`. By (I5), `cd_p(Γ_1^) >= D > 8`.
   By (I6), some simple discrete `A` killed by `p` has `H^9(Γ_1^;A) != 0`. `A` is finite:
   the `F_p`-span of the finite orbit of one nonzero vector is `A`. Step 1 gives
   `H^9(Γ_1;A) = 0`.
7. **Item 2.** With `Γ_1 = Γ`, `U'` is pro-p of `cd_p = D > 8`, so by (I6)
   `H^9(U';F_p) != 0`. By (I7), some open `V ⊇ U'` has a class
   `β ∈ H^9(V;F_p)` with `res_{U'} β != 0`. Take `Γ_1 = V ∩ Γ`, so `V = Γ_1^`. Step 1
   gives `H^9(Γ_1;F_p) = 0`.
8. **Item 3.** `Δ̄_p` lies in a product of first congruence subgroups
   `GL_m(O_𝔭, 𝔭) ∩ G(O_𝔭)`, which are pro-p. So `π_Δ` exists, and it is onto. Apply
   step 4 to `π_Δ`, then step 5 in its `G_p` form, then (I5). This gives
   `cd_p(Δ^_p) >= D > 8`. `Δ^_p` is pro-p, so (I6) gives `H^9(Δ^_p;F_p) != 0`. Step 1
   gives `H^9(Δ;F_p) = 0`. ∎
