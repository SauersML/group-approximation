---
rg: 2
id: local-boone-higman-iff-boone-higman-proof
kind: route
title: Put a Thompson simple envelope inside a Clapham finitely presented decidable envelope; one surviving element of the simple subgroup makes the host map injective on it
target: local-boone-higman-iff-boone-higman
requires:
  - boone-higman-thompson-simple-envelope
  - clapham-fp-embedding-preserves-word-problem
---

Imported statements, as recorded on the graph:
- `boone-higman-thompson-simple-envelope`, from Belk--Bleak--Matucci--Zaremsky
  arXiv:2306.16356, Theorem 3.8, verbatim: "A finitely generated group has
  solvable word problem if and only if it embeds into a finitely generated,
  computably presented simple group."
- `clapham-fp-embedding-preserves-word-problem` (Clapham, Proc. LMS (3) 17
  (1967) 419--430): "Every finitely generated group with solvable word problem
  embeds in a finitely presented group with solvable word problem."

Standard facts used:
- (F1) A finitely generated subgroup of a finitely generated group with
  solvable word problem has solvable word problem. Write its generators as
  words in the ambient generators and run the ambient algorithm.
- (F2) von Dyck: if `H = ⟨x_1, ..., x_n | r_1, ..., r_d⟩` and `k_1, ..., k_n`
  are elements of a group `K` with `r_i(k) = 1` for all `i`, then `x_j ↦ k_j`
  extends to a homomorphism `H → K`.

Fix a class `𝒦` of groups.

**(a) ⇒ (b).** Let `g = (g_1, ..., g_n)` solve `u_i(y) = 1, v_j(y) ≠ 1` in a
finitely generated group with solvable word problem. The subgroup
`G = ⟨g_1, ..., g_n⟩` is finitely generated with solvable word problem (F1). By
(a), `G ≤ K` for some `K ∈ 𝒦`. The words `u_i(g)`, `v_j(g)` take the same values
in `G` and in `K`, so `g` solves the system in `K`.

**(b) ⇒ (c).** Let `H = ⟨x_1, ..., x_n | r_1, ..., r_d⟩` have solvable word
problem and let `g = w(x) ≠ 1` in `H`. The system `r_1(y) = 1, ..., r_d(y) = 1,
w(y) ≠ 1` has the solution `y = x` in `H`, which is finitely generated with
solvable word problem. By (b) it has a solution `k` in some `K ∈ 𝒦`. By (F2),
`x_j ↦ k_j` defines `φ : H → K`, and `φ(g) = w(k) ≠ 1`.

The quasi-identity form of (c): the quasi-identity `∀y (r(y) = 1 → w(y) = 1)`
fails in `K` iff some `k` has `r(k) = 1` and `w(k) ≠ 1`, iff (F2) some
`φ : H → K` has `φ(w(x)) ≠ 1`. Every nontrivial `g ∈ H` is `w(x)` for some `w`,
and every quasi-identity has this shape for the group `H = ⟨x | r⟩` it
determines. So "(c) for `H`" and "every quasi-identity true in `𝒦` holds in
`H`" are the same statement for each finitely presented `H`.

**(c) ⇒ (a).** Let `G` be finitely generated with solvable word problem.
1. `G × Z` is finitely generated with solvable word problem and contains `G`.
2. By `boone-higman-thompson-simple-envelope`, `G × Z ≤ S` with `S` finitely
   generated, computably presented and simple. Applying the same theorem's
   converse direction to `S ≤ S`, `S` has solvable word problem. `S` contains
   `Z`, so `S ≠ 1`.
3. By `clapham-fp-embedding-preserves-word-problem`, `S ≤ H` with `H` finitely
   presented with solvable word problem.
4. Pick `g ∈ S`, `g ≠ 1`. By (c) there are `K ∈ 𝒦` and `φ : H → K` with
   `φ(g) ≠ 1`.
5. `N = ker(φ) ∩ S` is a normal subgroup of `S` not containing `g`, so
   `N ≠ S`. `S` is simple, so `N = 1`, and `φ` restricted to `S` is injective.
6. So `G ≤ G × Z ≤ S` embeds in `K ∈ 𝒦`.

This closes the cycle (a) ⇒ (b) ⇒ (c) ⇒ (a). `∎`

**Specialization.** For `𝒦 = fps`, (a) is the statement of
`boone-higman-conjecture` and (b) is the statement of
`local-boone-higman-conjecture`, word for word.

**Consequence 1** (Local Boone--Higman implies CGP Question 4). By (b) ⇒ (a),
every decidable `G` embeds in a finitely presented simple group, which is
isolated by `fp-simple-groups-are-isolated`. This is prose only; the graph route
`isolated-overgroup-via-boone-higman` already carries the second step.

**Consequence 4** (ultraproducts). If (b) holds for `fps` and `G` is finitely
generated decidable, index the finite pieces `p = (finite set of relators true
in G, finite set of elements nontrivial in G)` of `G` on its generators. Each
piece has a solution in some `K_p ∈ fps`. Take an ultrafilter on the pieces
containing every set `{p : p ⊇ p_0}`. The tuple of solutions defines a map from
the generators to `∏ K_p / U`, which kills every relator of `G` and no
nontrivial element, hence embeds `G`. Conversely, Łoś's theorem transfers each
finite system from an ultraproduct to some factor. This consequence is standard
model theory and is not load-bearing for the theorem.

**Why the local freedom buys nothing.** The proof never uses that the host in
(b) may depend on the system: step 4 uses one system, and step 5 turns its one
solution into a global embedding of `S`. A local method gains freedom only by
choosing hosts per piece, and simplicity of the Thompson envelope removes that
freedom on the single piece `(relators of H, g ≠ 1)`.
