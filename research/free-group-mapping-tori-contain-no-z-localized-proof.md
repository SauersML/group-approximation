---
rg: 2
id: free-group-mapping-tori-contain-no-z-localized-proof
kind: route
title: Push Z_(l) up the unique ascending ray of the Bass-Serre tree, then count roots in the invertible part of the lower central quotient
target: free-group-mapping-tori-contain-no-z-localized
requires:
  - z-localized-fixes-a-vertex-or-end-of-every-tree
---

**Imports (textbook, not re-read).**
- (NS) Abelian subgroups of free groups are cyclic.
- (MW) Each `Γ_c ⊗ Q` is the degree-`c` part of the free Lie algebra on `V = F_ab ⊗ Q`, functorially in `F`. It
  embeds in `V^(⊗c)`, `Γ_c` is torsion-free, and `∩_c γ_c F = 1` (Magnus–Witt).

**The tree.**
- `t^(-1) F t = φ(F) ⊆ F`, so `F ⊆ tFt^(-1) ⊆ t^2 F t^(-2) ⊆ ...`.
- In the Bass–Serre tree, `hF ↦ htF` is the unique *up* neighbour of a vertex: `htF = h'tF` for all
  `h, h' ∈ F`, since `F ⊆ tFt^(-1)`. The down neighbours are the `h t^(-1) F`, indexed by `F/φ(F)`
  (`h t^(-1) F = h' t^(-1) F` if and only if `h'^(-1) h ∈ t^(-1) F t = φ(F)`), with stabilizers `h φ(F) h^(-1) ⊆ F`.
- A ray without backtracking therefore goes up finitely often and then down forever, or up forever. Along a
  down-going tail every stabilizer lies in one conjugate of `F`.

**Part 1.**
- By the tree lemma, `A` fixes a vertex or an end. A fixed vertex puts `A` in a conjugate of `F`, which (NS)
  forbids.
- For a fixed end, the union of the `A ∩ Stab(v_j)` along a down-going tail would again lie in a conjugate of `F`.
  So the ray goes up forever, and after conjugation `v_j = t^j F` and `A ≤ ∪_j t^j F t^(-j)`.
- Let `a ∈ A` be the element divisible by infinitely many primes. It lies in some `Stab(v_J)`, so after conjugating
  by a power of `t` we may take `x = a ∈ F`, and `x ≠ 1`.
- For each such prime `q`, the root `x/q` lies in some `t^k F t^(-k)`, say `y = t^k z t^(-k)` with `z ∈ F` and
  `y^q = x`. Then `z^q = t^(-k) x t^k = φ^k(x)`.
- So `P(x)` contains infinitely many primes.

**Part 2.**
- *Roots respect degree.* If `y^m = z` with `z ∈ γ_c ∖ γ_(c+1)` and `y ∈ γ_d ∖ γ_(d+1)` with `d < c`, then
  `m[y] ≠ 0` in the torsion-free `Γ_d`. So `z ∉ γ_(d+1)`, a contradiction. Hence `y ∈ γ_c` and `[z] = m[y]` in
  `Γ_c`.
- *Fitting decomposition.* Write `Γ_c ⊗ Q = V_nil ⊕ V_inv`, with `Φ_c` nilpotent on the first summand and invertible
  on the second.
- *The lattice.* Let `L = V_inv ∩ Γ_c`, which is saturated and `Φ_c`-stable, and let `D = det(Φ_c|_L) ≠ 0`.
- *Moving into `L`.* Since `Φ_c^k [x] ≠ 0` for all `k`, the vector `Φ_c^K [x]` is nonzero and lies in `L`, where
  `K = rank Γ_c`.
- *Roots persist.* If `φ^k(x) = y^p`, then `φ^(k+1)(x) = φ(y)^p`. So we may take `k >= K`. By the degree step,
  `Φ_c^k [x] = p[y]` with `[y] ∈ Γ_c`, and saturation gives `[y] ∈ L`.
- *Counting primes.* If `p ∤ D`, then `Φ_c` is invertible on `L/pL`. So `Φ_c^k[x] ∈ pL` gives `Φ_c^K[x] ∈ pL`, and
  `p` divides the content of the fixed nonzero vector `Φ_c^K[x] ∈ L`.
- Hence `P(x) ⊆ primes(D) ∪ primes(content(Φ_c^K[x]))`, a finite set.

**Part 3.**
- The degree `c_k` of `φ^k(x)` is nondecreasing, since `φ(γ_c) ⊆ γ_c`.
- If it is eventually constant, equal to `c` from `k_0` on, then `x' = φ^(k_0)(x)` is non-sinking at level `c`.
  So `P(x')` is finite by part 2.
- Roots persist, so `P(x) = P(x')` is finite, contradicting part 1.

**Part 4.**
- If `φ_ab ⊗ Q` is injective, then by (MW) `Φ_c ⊗ Q` is the restriction of `(φ_ab ⊗ Q)^(⊗c)`, which is injective.
- So a nonzero `[x] ∈ Γ_c` has `Φ_c^k[x] ≠ 0` for every `k`, and the degree of every `φ^k(x)` stays that of `x`.
  Nothing sinks, and part 3 gives the claim. ∎
