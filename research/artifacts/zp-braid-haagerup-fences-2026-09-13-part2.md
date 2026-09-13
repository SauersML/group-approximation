# Braid groups and the Haagerup property, part 2: the standard obstructions do not occur

Lane z3-07-braid-haagerup, Zaremsky Problem 3.7 (`zaremsky-3-07-braid-groups-haagerup`), 2026-09-13.
Status: unreviewed. Part 1: `zp-braid-haagerup-reductions-2026-09-13-part1.md` (closure properties (H1)–(H6),
braid facts (B1)–(B6)).

The usual way to show a group lacks the Haagerup property is an infinite subset with relative property (T).
In practice it comes from (a) an infinite subgroup with property (T), or (b) a Burger pair: `Z^2 ⋊ Γ` with
`Γ ≤ SL_2(Z)` non-amenable, where `(Z^2 ⋊ Γ, Z^2)` has relative property (T) (Burger, *Kazhdan constants for
SL(3,Z)*, J. reine angew. Math. 413 (1991), for `Γ = SL_2(Z)`; the non-amenable case is the standard
extension, not re-verified here). Neither occurs in braid groups.

## 1. Proposition D: every subgroup of `B_n` with property (T) is trivial

**Local indicability of `P_n`.** Call a group locally indicable if every nontrivial finitely generated
subgroup surjects onto `Z`. Free groups are locally indicable (nontrivial f.g. subgroups are free of positive
rank). If `N ◁ G` and both `N` and `G/N` are locally indicable, so is `G`: for a nontrivial f.g. `H ≤ G`,
either its image in `G/N` is nontrivial (and f.g.), so it surjects onto `Z`, or `H ≤ N`. By Artin combing
(B2), `P_n ≅ F_{n−1} ⋊ P_{n−1}`, and induction from `P_1 = 1` shows that `P_n` is locally indicable.

**Proof of D.** A countable group with property (T) is finitely generated and has finite abelianization. So a
(T) subgroup of `P_n` is trivial. If `H ≤ B_n` has (T), then `H ∩ P_n` has finite index in `H`, so it has (T)
and is trivial. Hence `H` is finite. `B_n` is torsion-free (the unordered configuration space of `n` points in
the plane is a finite-dimensional `K(B_n, 1)`), so `H = 1`. ∎

By (H6), this rules out obstruction (a).

## 2. Proposition E: normalizers act on free abelian subgroups of `B_n` through virtually solvable groups

**Statement.** Let `A ≤ B_n` be free abelian of finite rank `k`, and let `Γ ≤ B_n` normalize `A`. The conjugation
action `Γ → GL(A) ≅ GL_k(Z)` has virtually solvable image. In particular no subgroup `Z^2 ⋊ Γ` of `B_n` (with
`Z^2` normal) has `Γ` acting through a non-amenable subgroup of `GL_2(Z)`.

**Step 1 (Magnus order on free groups).** Let `μ: F_m → Z⟨⟨X_1, …, X_m⟩⟩` be the Magnus embedding,
`x_i ↦ 1 + X_i`. It is injective (Magnus). For `g ≠ 1` let `L(g)` be the lowest-degree nonzero homogeneous
component of `μ(g) − 1`, and call `g` positive if the coefficient of the largest monomial of `L(g)` (in a
fixed total order on monomials of each degree) is positive. This is a bi-invariant order:

- totality: `L(g^{-1}) = −L(g)`, since `μ(g^{-1}) − 1 = −(μ(g) − 1) + (terms of higher degree)`;
- products: `μ(gh) − 1 = (μ(g)−1) + (μ(h)−1) + (μ(g)−1)(μ(h)−1)`, so `L(gh)` is `L(g)`, `L(h)` or `L(g)+L(h)`
  (the product term has higher degree). In each case the leading coefficient is positive when both are;
- conjugation: `μ(h g h^{-1}) − 1 = μ(h)(μ(g) − 1)μ(h)^{-1}` and `μ(h) = 1 + (higher)`, so `L(hgh^{-1}) = L(g)`.

**Step 2 (IA automorphisms preserve it).** Let `φ ∈ Aut(F_m)` induce the identity on `H_1(F_m)`. The degree-1
part of `μ(w) − 1` is `Σ_i e_i(w) X_i`, where `e_i` is the exponent sum, so `μ(φ(x_i)) = 1 + X_i + (higher)`.
The continuous ring endomorphism `Φ` with `X_i ↦ μ(φ(x_i)) − 1` satisfies `μ ∘ φ = Φ ∘ μ` (both sides are
multiplicative and agree on each `x_i`). `Φ` sends a homogeneous polynomial `P` of degree `d` to
`P + (higher)`, so `L(φ(g)) = L(g)`, and `φ` preserves positivity.

**Step 3 (`P_n` is bi-orderable; Kim–Rolfsen).** Induct via `P_n = F_{n−1} ⋊ P_{n−1}`. Pure braid automorphisms
send each generator to a conjugate of itself, so they act trivially on `H_1(F_{n−1})` and preserve the Magnus
order (Step 2). Order `P_n` lexicographically: `uβ` (`u ∈ F_{n−1}`, `β ∈ P_{n−1}`) is positive iff `β > 1`, or
`β = 1` and `u > 1`. Products and totality are immediate. For conjugation invariance, the positive cone of
`F_{n−1}` is invariant under conjugation by `F_{n−1}` (Step 1) and by `P_{n−1}` (Step 2). For `β > 1`,
conjugation changes the `P_{n−1}`-coordinate by conjugation in `P_{n−1}`, which preserves positivity. This is
the ordering of D. M. Kim and D. Rolfsen, *An ordering for groups of pure braids and fibre-type hyperplane
arrangements*, Canad. J. Math. 55 (2003).

**Step 4 (group orders on `Z^k` force solvable symmetry).** Let `Λ` act on `Z^k` preserving a total group
order `<`.

- The convex subgroups form a chain `0 = C_0 < C_1 < … < C_r = Z^k`. Each is pure (if `mx ∈ C` then `x ∈ C`,
  since `x` lies between `0` and `mx`), so ranks strictly increase and `r ≤ k`.
- An order-preserving automorphism maps convex subgroups to convex subgroups and preserves inclusion, so it
  fixes each `C_i` (an order-preserving bijection of a finite chain is the identity).
- On `Q_i = C_i / C_{i−1} ≅ Z^{d_i}` the induced order is archimedean (the two convex subgroups are
  consecutive). By Hölder's theorem there is an order-embedding `ι: Q_i → R`, unique up to a positive scalar.
  So every `γ` in the image of `Λ` satisfies `ι ∘ γ = λ_γ ι` with `λ_γ > 0`.
- Extend `ι` Q-linearly to `Q_i ⊗ Q`; it stays injective. The rational matrices `M` with `ι ∘ M = λ_M ι` form a
  Q-algebra `E`, and `M ↦ λ_M` is an injective ring homomorphism `E → R` (if `λ_M = 0` then `ι ∘ M = 0`, so
  `M = 0`). Hence `E` is commutative, and `Λ` acts on each `Q_i` through an abelian group.
- The image of `Λ` in `GL_k(Z)` preserves the flag `C_•` and acts abelianly on each graded piece. The kernel
  of the map to `∏_i GL(Q_i)` is unipotent, hence nilpotent. So the image is solvable.

**Step 5 (conclusion).** Put `Γ_0 = Γ ∩ P_n` and `A_0 = A ∩ P_n`. They have finite index in `Γ` and `A`, and
`Γ_0` normalizes `A_0`. The bi-order of `P_n` (Step 3), restricted to `A_0`, is invariant under conjugation by
`Γ_0`. By Step 4, the image of `Γ_0` in `GL(A_0)` is solvable. An automorphism of the torsion-free group `A`
is determined by its restriction to the finite-index subgroup `A_0`, so the image of `Γ_0` in `GL(A)` is
solvable, and it has finite index in the image of `Γ`. ∎

By Proposition E, obstruction (b) cannot occur: a Burger pair inside `B_n` would give a non-amenable image.

## 3. What remains for a negative answer

Relative property (T) for an infinite subset of `B_n` not arising from (a) or (b). Examples would be a
non-abelian normal subgroup `N` of a subgroup `H ≤ B_n` with `(H, N)` relative (T), or relative (T) sets that
are not subgroups. Braid groups are linear and bi-orderable (after finite index), and every subgroup of `P_n`
is locally indicable. No mechanism producing relative (T) in such groups is known to this lane.
