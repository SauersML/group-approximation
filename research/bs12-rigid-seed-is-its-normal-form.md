---
rg: 2
id: bs12-rigid-seed-is-its-normal-form
kind: claim
title: BS(1,2) has an explicit six-letter quantum-rigid seed SFT whose seed point is the matrix normal form; the seed is forced at linear radius and carries exactly the polynomial-time word problem, so the CAP rung (1a) is complexity-neutral
distinct_from:
  locally-finite-splittings-preserve-rigid-sft-compactifications: that proves BS(m,n) is in the class C by a general gluing construction; this writes the BS(1,2) instance out (alphabet, rules, seed point, operator certificate) and measures what it certifies.
  locally-finite-tree-end-shifts-are-quantum-rigid-sfts: that is the end shift of the tree, which has no isolated point; this is a seed SFT with an isolated seed-forced point whose orbit is the group.
---

**ESTABLISHED (lane proof, bh-g1-universal-point, 2026-09-18; elementary, not independently reviewed).** This
is the rung (1a) of Gate 1 (SEED) in synthesis v6 (b5ad39956).

## 1. The group and its coordinates

- **Presentation and matrices.** `Λ = BS(1,2) = ⟨a, t | t a t⁻¹ = a²⟩`, with `a = [[1,1],[0,1]]` and
  `t = [[2,0],[0,1]]`. This is the faithful representation `Λ ≅ Z[1/2] ⋊ Z` (recalled).
- **Coordinates.** Write `h = (s, q)` for `[[2^s, q],[0,1]]`, with `s ∈ Z` and `q ∈ Z[1/2]`. Then
  `(s,q)(s',q') = (s+s', q + 2^s q')`.
- **The tree.** Vertex cosets are `h⟨a⟩ = (s, q + 2^s Z)`. The tree `T` is 3-regular:
  - the parent of `h⟨a⟩` is `ht⁻¹⟨a⟩ = (s−1, q + 2^{s−1}Z)`;
  - its two children are `h a^c t⟨a⟩ = (s+1, q + 2^s c + 2^{s+1}Z)` for `c ∈ {0,1}`.
- **The sink.** The sink vertex is `⟨a⟩ = (0, Z)`. Its proper ancestors are `(ℓ, 2^ℓ Z)` for `ℓ < 0`.

## 2. The SFT, the seed, the seed point

- **Alphabet.** Six letters: the pointers `D, U_0, U_1` and the sink letters `+, *, −`.
- **Meaning of the pointers.** At `h`, `D` points along the edge to `ht⁻¹⟨a⟩`, and `U_c` points along the edge to
  `h a^c t⟨a⟩`.
- **Action.** Configurations are `x : Λ → A` with `(g·x)(h) = x(g⁻¹h)`. Every rule below reads `x` at `h` and at
  `h·w` for `w ∈ {a, t, at, t⁻¹}`, so the rule radius is 2.

**Rules.**
- **(T) Transport along `a`.**
  - `x(h)` is a sink letter iff `x(ha)` is;
  - `x(h) = D` iff `x(ha) = D`;
  - `x(h) = U_c` iff `x(ha) = U_{1−c}`, because `a^{1+c'}t⟨a⟩ = a^c t⟨a⟩` iff `c' ≡ c − 1 (mod 2)`.
- **(Y) Sink line.** If `x(h)` and `x(ha)` are sink letters, then `x(h)x(ha) ∈ {++, +*, *−, −−}`. This is `C_Z`.
- **(X) Exclusivity.**
  - `x(h) = U_c` iff `x(h a^c t) ≠ D`, for `c = 0, 1`;
  - `x(h) = D` iff `x(ht⁻¹) ≠ U_0`, since `h⟨a⟩` is the `U_0`-child of `ht⁻¹`.

**Seed.** `π = [x(1) = *]`. The node `locally-finite-splittings-rigid-compactification-proof` §2 gives:
- (C1) `[π] = {y_*}`, with trivial stabilizer;
- (C2) `Y` is the orbit closure of `y_*`.

**The seed point, in closed form.** For `h = (s, q)`:
- `y_*(h) = +, *, −` if `s = 0` and `q ∈ Z`, according to `q < 0`, `q = 0`, `q > 0`;
- `y_*(h) = U_c` if `s < 0` and `q ∈ 2^s Z`, with `c = q·2^{−s} mod 2`, since then `h⟨a⟩` is a proper ancestor
  of the sink and `U_c` is the child toward it;
- `y_*(h) = D` otherwise, including every `h` with `s > 0`.

Direct check of (X):
- A `D`-vertex has `x(ht⁻¹) ∈ {D, U_1, sink letter}`, never `U_0` toward it.
- An ancestor labelled `U_c` has exactly its `c`-child non-`D`.

**Boundary.** `∂Y` consists of the following points.
- The two `C_Z` limits on the sink coset.
- The end-type points, pointing to an end of `T`. Among them is the constant point `D^Λ`: all
  pointers lead to the canonical end `s → −∞`, and it is fixed by all of `Λ`. So `Y` is not free. As v6 notes,
  seed ⇏ (D).

## 3. The rigidity certificate

Let `(E_ℓ(h))` be a `D`-family over any field with `D ≥ 2`. The node's lemmas give the following.
- **Tree part.** (L1)–(L4) apply.
  - `Π_v(e)` ("vertex `v` points along `e`") and `Σ_v` do not depend on the element read.
  - `Π_v(e) + Π_w(e) = 1` on each edge.
  - Along a tree path, `1 − Π_{v_0}(f_1) ≤ Π_{v_m}(f_m)`.
  So idempotents at different vertices are comparable or orthogonal in the needed way, and they commute.
- **Sink line.** Put `P_j = E_+(a^j)·Σ` on the sink coset.
  - (Y) forces `+` at `j` whenever `+` is at `j+1`, so `P_{j+1} ≤ P_j`.
  - Also `E_*(a^j) = P_{j−1} − P_j` and `E_−(a^j) = Σ − P_{j−1}`.
  - All sink idempotents lie in the algebra of the chain `(P_j)`, which is commutative.

Hence `Y` is `D`-quantum rigid for every `D ≥ 2`, over every field. It is compression along two monotone chains:
- the tree pointers toward the sink;
- the `+`-chain on the sink line.

## 4. What it certifies

**(a) The word problem.** `w = 1` iff `y_*(w) = *`, because `*` occurs only at `(0,0)`.
- `y_*(w)` is computed from `(s,q)`. The entry `q` has `O(|w|)` bits.
- So `y_*` and `WP(Λ)` are polynomial-time equivalent, and both are in P. By linearity, `WP(Λ)` is even in
  logspace (Lipton–Zalcstein, recalled).

**(b) Forcing radius is linear, despite exponential distortion.** Every locally admissible pattern on `B(10n+24)`
with `x(1) = *` agrees with `y_*` on `B(n)`. The proof has five ingredients.
- **Distortion bound.** Horner's rule `a^j = t a^{⌊j/2⌋} t⁻¹ a^{j mod 2}` gives `|a^j| ≤ 3 log_2|j| + 1`.
  Conversely, `|a^j| ≤ 2n` forces `log_2|j| ≤ 2n + log_2(2n)`.
- **Cosets are a-connected.** If `g, ga^j ∈ B(n)`, then the whole `a`-segment `ga^i` (`|i| ≤ |j|`) lies in
  `B(10n+4)`. Every coset meeting `B(n+2)` (which contains all crossing elements below) is `a`-connected inside `B(10n+24)`. So is every coset meeting `B(n)`.
- **Consistent labels.** By (T), each such coset has a single pointer or sink status. On `⟨a⟩`, rule (Y)
  propagates `+` and `−` from `1`.
- **Tree edges are visible.** A geodesic word for `h ∈ B(n)` crosses every edge of the tree geodesic from the sink
  to `h⟨a⟩`. Each crossing is one (X) rule inside `B(n+2)`.
- **Orientation.** The sink forces its neighbours to point in. Out-degree 1 then forces each next vertex along the
  geodesic, as in §2 of the gluing proof.

So `m(n) ≤ 10n + 24`. Exponential distortion costs nothing: a ball of radius `O(n)` contains the
exponentially long `a`-segments that transport labels.

**(c) The presentation-level cost is the Dehn function, not the WP.** Checking a pattern on `B(m)` from the
relators requires knowing which words are equal. For BS(1,2) that costs `2^{O(m)}` area, since the Dehn function
is exponential (recalled). The word problem is nevertheless in P, by arithmetic. So neither the forcing radius
nor the Dehn function measures what a seed carries.

**(d) The seed is the normal form, so the construction carries nothing harder.** The same reading applies to
every seed from `locally-finite-splittings-preserve-rigid-sft-compactifications`. There `y_*(h)` is one of:
- the first edge of the `T`-geodesic from `h`'s vertex to the sink;
- `y_{A*}(h)` on the sink coset.

So:
- `y_*` is computable from Britton reduction, plus membership in the finite-index edge groups (finite coset tables),
  plus `y_{A*}`;
- conversely, `WP(Λ)` reduces to `y_*`.

The tree layer is complexity-neutral. Over `A = Z`, i.e. for all GBS groups, Britton reduction with binary
exponents is polynomial (standard), so every seed of this construction over `Z` certifies a word problem in P.

**Where complexity could enter.** There are only three places:
- (i) the vertex seed `Y_A` itself;
- (ii) nested pinches in a distorted vertex group `A ≠ Z`. Each `φ` between finite-index subgroups is
  bi-Lipschitz, so the lengths of `A`-elements grow at most like `K^n` and must be handled compressed;
- (iii) infinite-index edge groups, which need relative seeds (lesson of the gluing node).

Question (ii) is open here: is "compressed WP of `A` in P" preserved by finite-index HNN extensions? A yes would
make the whole locally-finite closure of `{finite, Z}` in 𝒞 CAP-bounded by P.

## Lesson for general BH

On a locally finite tree, a rigid seed is the group's normal form written as a local rule: a pointer to the origin
plus the sign of one coordinate. It is forced at linear radius even through exponential distortion, and it is rigid
by monotone chains. It is also complexity-neutral: it carries exactly `WP(Λ)`, which is in P for all GBS groups. So
the CAP gate cannot be decided on locally finite rungs. A seed can carry hardness only through its vertex seed,
through compressed arithmetic in a distorted vertex group, or through relative seeds over infinite-index edge
groups. Higman–Clapham and Sapir–Birget–Rips towers live in the last case, so rung (1c) needs relative seeds, not
locally finite gluing.
