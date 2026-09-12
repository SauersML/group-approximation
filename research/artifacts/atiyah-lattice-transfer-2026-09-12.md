# Lattice transfer for the Strong Atiyah Conjecture

Lane `atiyah-computability`, 2026-09-12.

This artifact proves two statements, one positive and one negative, and records one open claim.

- **Theorem 1 (proportionality):** discrete groups acting freely and cocompactly on one complex have proportional L²-Betti numbers, with a rational ratio.
- **Corollary 1 (transfer):** a torsion-free group sharing a complex with a group that has an irrational L²-Betti number refutes Strong Atiyah over Q with an explicit Laplacian.
- **Theorem 2 (obstruction):** torsion-free discrete subgroups of (locally-elliptic-by-abelian) × tree groups lie in Linnell's class C, so the transfer cannot run on complexes with such automorphism groups.
- **Open claim:** some complex carries free cocompact actions of both a group with an irrational L²-Betti number and a torsion-free group.

## Why this route is different

The published irrational and transcendental kernel dimensions use groups with
infinite locally finite subgroups: lamps (Grigorchuk–Żuk, Dicks–Schick, Austin,
Grabowski, Pichot–Schick–Żuk). Existing attempts on
`algebraic-strong-atiyah-counterexample-exists` try to rebuild the lamp coins
without torsion and die there. The percolation-coin and one-compressor
attempts are recorded on that claim.

This route keeps the torsion group and moves the *value* instead. An
L²-Betti number of a free cocompact complex is a local invariant of the complex
(Lemma B below). So any other free cocompact group of automorphisms of the same
complex sees the same value, up to a rational covolume factor.

## Setup

Let `X` be a connected locally finite simplicial complex.
- `X_k` is the set of k-simplices, with arbitrary orientations.
- `C^k = ℓ²(X_k)`, with orthonormal basis `δ_σ`.
- `d_k : C^k → C^(k+1)` is the coboundary, `Δ_k = d_k^* d_k + d_(k-1) d_(k-1)^*`,
  and `P_k` is the orthogonal projection onto `ker Δ_k`.

When some group acts cocompactly, `X` has bounded geometry, so the `d_k` are
bounded.

`H = Aut(X)` is the group of simplicial automorphisms, with the permutation
topology on vertices. It is totally disconnected and locally compact, and
simplex stabilizers `H_σ` are compact open. `H` acts unitarily on `C^k` by
`h·δ_σ = ε(h,σ) δ_(hσ)` with `ε ∈ {±1}`. This action commutes with every `d_k`,
hence with `Δ_k` and `P_k`.

Let `D ≤ H` be discrete, acting freely on each `X_k` (no nontrivial element maps
a simplex to itself) and cocompactly. Orient one representative `σ_i` of each
`D`-orbit and push the orientation forward along `D`; this is well defined
because the action on simplices is free. Then `C^k ≅ ℓ²(D)^(n_k)`
`D`-equivariantly, with `n_k = |D\X_k|`. Also `d_k` and `Δ_k` are right
multiplications by matrices over `Z[D]`, and
`b_k^(2)(X;D) = dim_(N(D)) ker Δ_k`.

## Lemma A (trace formula)

For every closed `D`-invariant subspace `V ≤ C^k`,

```text
dim_(N(D)) V = Σ_(σ ∈ D\X_k) <P_V δ_σ, δ_σ>.
```

*Proof.* Under `C^k ≅ ℓ²(D) ⊗ C^(n_k)`, `δ_(gσ_i) ↦ δ_g ⊗ e_i`, the dimension
is `(τ ⊗ Tr)(P_V) = Σ_i <P_V (δ_e ⊗ e_i), δ_e ⊗ e_i>`. The sum does not depend
on the choice of orbit representatives, because `P_V` commutes with `D` and the
orientation signs cancel on the diagonal. ∎

## Lemma B (local invariance)

`p(σ) = <P_k δ_σ, δ_σ>` is constant on `H`-orbits.

*Proof.* `<P_k h δ_σ, h δ_σ> = ε² <P_k δ_(hσ), δ_(hσ)>` and `h` commutes with
`P_k`. ∎

## Lemma C (unfolding)

`H` contains a lattice, so it is unimodular; fix a Haar measure `μ`. For an
`H`-orbit `O ⊆ X_k` and `σ ∈ O`, and `D` acting freely on `O`,

```text
|D\O| · μ(H_σ) = μ(D\H).
```

*Proof.* `D\H` is the disjoint union over `x ∈ D\H/H_σ` of `D\D x H_σ`. Each
piece is the injective image of `x H_σ`: `Dxh = Dxh'` gives an element of
`D ∩ x H_σ x^-1`, which is `Stab_D(xσ) = 1`. So each piece has measure
`μ(H_σ)`, and `D\H/H_σ ↔ D\O`. ∎

## Theorem 1

Let `G, Γ ≤ Aut(X)` be discrete, acting freely on simplices and cocompactly.
Then for every `k`

```text
b_k^(2)(X;Γ) = r · b_k^(2)(X;G),     r = μ(Γ\H)/μ(G\H) = |Γ\X_0| / |G\X_0| ∈ Q_(>0).
```

*Proof.* By Lemmas A and B, `b_k^(2)(X;D) = Σ_(O ∈ H\X_k) |D\O| p_O`, a finite
sum. By Lemma C this equals `μ(D\H) Σ_O p_O / μ(H_(σ_O))`. Apply it with
`D = Γ` and `D = G`, and read off `r` at any vertex orbit. ∎

This is the free cocompact complex form of the proportionality principle for
L²-Betti numbers of lattices. The group form, for lattices in a common lcsc
unimodular group, is due to Gaboriau (measure equivalence) and H. D. Petersen
(arXiv:1104.3294; see also Petersen–Sauer–Thom, arXiv:1612.04559). Those
statements were not read from source in this lane, so nothing is imported from
them. The proof above is self-contained, and no novelty is claimed for the
principle.

## Corollary 1 (transfer)

If moreover `Γ` is torsion-free and `b_k^(2)(X;G) ∉ Q`, then `Δ_k ∈ M_(n_k)(Z[Γ])`
has `dim_(N(Γ)) ker Δ_k = r·b_k^(2)(X;G) ∉ Q`. So Strong Atiyah over `Q` fails for
`Γ`, and `algebraic-strong-atiyah-counterexample-exists` holds.

The contrapositive is a rationality criterion. If a torsion-free `Γ` satisfying
Strong Atiyah acts freely and cocompactly on `X`, then every free cocompact `G`
on `X`, torsion or not, has `b_k^(2)(X;G) ∈ (1/r)Z ⊆ Q`.

## Theorem 2 (obstruction)

Let `H_1` be a totally disconnected locally compact group, and let `N ◁ H_1` be
closed and **locally elliptic**: every finite subset of `N` lies in a compact
subgroup of `H_1`. Assume `H_1/N` is abstractly torsion-free abelian. Let `T` be
a locally finite tree and `H_2 ≤ Aut(T)` closed (or `H_2 = 1`). Then every discrete
torsion-free `Γ ≤ H_1 × H_2` lies in Linnell's class `C`, and so satisfies Strong
Atiyah over `C`.

*Proof.*
1. `Γ^0 = Γ ∩ (N × H_2)` is normal in `Γ`, and `π_1` embeds `Γ/Γ^0` into
   `H_1/N`. So the quotient is torsion-free abelian, hence elementary amenable.
2. Let `F ≤ Γ^0` be finitely generated. The first coordinates of its generators
   lie in a compact subgroup `K ≤ H_1`, so `F ≤ K × H_2`.
3. `π_2|_F` is injective: its kernel lies in `Γ ∩ (K × 1)`, which is compact
   and discrete, hence finite, hence trivial.
4. `π_2(F)` is discrete. Take a compact open `V ≤ H_2`; then
   `π_2(F) ∩ V = π_2(F ∩ (K × V))`, and that set is finite.
5. So `F` is isomorphic to a discrete torsion-free subgroup of `Aut(T)`. Its
   vertex stabilizers are compact and discrete, hence trivial. An inversion `g`
   would give `g²` fixing an edge's endpoints, so `g² = 1` and `g = 1`. So `F` acts
   freely without inversions and is free (Serre, *Trees*, I.3.3).
6. `Γ^0` is locally free, a directed union of free groups, so `Γ^0 ∈ C`. Hence
   `Γ ∈ C`, as an extension with elementary amenable quotient.
7. Torsion-free groups in `C` satisfy Strong Atiyah over `C` (Linnell, *Division
   rings and group von Neumann algebras*, Forum Math. 5 (1993) 561–576). ∎

## Corollary 2

Suppose `Aut(X)` embeds as a closed subgroup of an `H_1 × H_2` as in Theorem 2.
Then no torsion-free lattice acting freely and cocompactly on `X` refutes Strong
Atiyah. If such a lattice exists, every free cocompact `G` on `X` has rational
L²-Betti numbers. The transfer of Corollary 1 is dead on such complexes.

**Candidate instance, not verified here.** Diestel–Leader graphs `DL(n,n)`, the
Cayley graphs of lamplighters `Z/n ≀ Z`. In the height-preserving subgroup of
the isometry group, which has index at most 2, the kernel of the height
homomorphism consists of end-fixing, horocycle-preserving pairs. It should be
locally elliptic by the horocyclic-product structure theorem
(Bartholdi–Neuhauser–Woess). The structure statement has not been read from
source.

## Open claim

There is a locally finite simplicial complex `X` with discrete `G, Γ ≤ Aut(X)`,
both acting freely on simplices and cocompactly, such that `Γ` is torsion-free
and `b_k^(2)(X;G)` is irrational for some `k`.

Together with Theorem 1, this gives `algebraic-strong-atiyah-counterexample-exists`.

What a witness needs:
- `G` is not virtually torsion-free. If `G' ≤ G` is torsion-free of finite
  index, then `b_k^(2)(X;G') = [G:G'] b_k^(2)(X;G)` is already irrational, and
  the transfer is idle. The published irrational groups contain finite
  subgroups of unbounded order.
- `Aut(X)` is non-discrete. If it were discrete, `G` and `Γ` would both have
  finite index in it, so `G ∩ Γ` would be a torsion-free finite-index subgroup
  of `G`, contradicting the previous point.
- `X` is not contractible. A free cellular action on a finite-dimensional
  contractible complex forces finite cohomological dimension, hence
  torsion-freeness, and `G` has torsion. In particular `X` is not CAT(0),
  since a finite subgroup would fix a point, hence stabilize the simplex
  containing it in its interior (atiyah-nonsofic, 2026-09-12).
- `Aut(X)` lies outside the class of Theorem 2.
- `Γ` is outside every class where Strong Atiyah is proved: elementary amenable
  extensions and class `C`, locally indicable, virtually special, residually
  torsion-free elementary amenable.
- `Γ` and `G` are both uniform lattices in `Aut(X)`, so they are quasi-isometric.

Directions left open: complexes with rank-two or building-like automorphism
groups (Burger–Mozes-type square complexes, where irreducible torsion-free
lattices outside class `C` exist), carrying a lattice with unbounded torsion.
No such complex is known to carry an irrational L²-Betti number.
