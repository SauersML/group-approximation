# Tree actions with elliptic stabilizers, amenable hosts, and the lattice transfer

Lane `atiyah-lattice-complex`, 2026-09-12.

Target: `complex-with-irrational-and-torsion-free-lattices`. A witness complex, combined with
`free-cocompact-lattices-proportional-l2-betti`, refutes
`algebraic-strong-atiyah-counterexample-exists`.

Result: no witness was found. This artifact records one new established obstruction
(Theorem 3), one reduction for amenable hosts whose literature inputs are not yet verified
(Section 3), and the status of the published irrational examples (Section 4).

## 1. Theorem 3: tree actions with locally elliptic stabilizers

**Setting.**
- `X` is a connected locally finite simplicial complex.
- `Γ ≤ Aut(X)` is discrete and torsion-free, and acts freely on simplices and cocompactly.
- `H` is any subgroup with `Γ ≤ H ≤ Aut(X)`.
- `H` acts on a locally finite tree `T`. No continuity is assumed.
- Every vertex stabilizer `H_v` is **locally elliptic in `Aut(X)`**: every finite subset of
  `H_v` lies in a compact subgroup of `Aut(X)`.

**Theorem 3.**
(a) `Γ` acts on `T` freely and without inversions.
(b) `Γ → Aut(T)` is injective, and its image is a discrete torsion-free subgroup. In
    particular `Γ` is free (Serre, *Trees*, I.3.3).
(c) `Γ` satisfies Strong Atiyah over every subfield `K ⊆ C` closed under complex conjugation.
(d) Every discrete `G ≤ Aut(X)` acting freely on simplices and cocompactly has
    `b_k^(2)(X;G) ∈ Q` for every `k`. So `X` is not a witness.

**Proof.**
1. *Trivial vertex stabilizers.* Let `v` be a vertex and `F ⊆ Γ_v = Γ ∩ H_v` finite. By
   hypothesis `F` lies in a compact subgroup `K ≤ Aut(X)`. Then `⟨F⟩ ≤ Γ ∩ K`, which is
   discrete and compact, hence finite. So `Γ_v` is locally finite, and torsion-free, hence
   trivial.
2. *No inversions.* If `γ ∈ Γ` swaps the endpoints of an edge, `γ²` fixes both endpoints, so
   `γ² = 1` by step 1 and `γ = 1`.
3. *Discrete faithful image.* The kernel of `Γ → Aut(T)` fixes every vertex, so it is
   trivial by step 1. The image meets every vertex stabilizer of `Aut(T)` trivially. Those
   stabilizers are open in the permutation topology, so the image is discrete.
4. *Strong Atiyah.* Apply `tree-by-elliptic-lattices-satisfy-strong-atiyah` with
   `H_1 = N = 1` and `H_2 = Aut(T)`: `N = 1` is locally elliptic and `H_1/N = 1` is
   torsion-free abelian. The image of `Γ`, which is isomorphic to `Γ`, is a discrete
   torsion-free subgroup of `H_1 × H_2`, so it satisfies Strong Atiyah over `K`.
5. *Rationality on `X`.* The Laplacian `Δ_k` of `X` is a matrix over `Z[Γ]`, so
   `b_k^(2)(X;Γ) = dim_(N(Γ)) ker Δ_k` is an integer by step 4. By
   `free-cocompact-lattices-proportional-l2-betti`,
   `b_k^(2)(X;G) = r^(-1) b_k^(2)(X;Γ)` with `r ∈ Q_(>0)`. ∎

**Remarks.**
- Only the elliptic-stabilizer condition is used. `H` need not be closed, and the tree
  action need not be continuous or cocompact.
- *Elliptic-by-tree hosts.* Let `N ◁ H` be closed and locally elliptic, and let `H/N` act
  on `T` with compact vertex stabilizers. Then `H_v` is an extension of a compact group by
  `N`. It is locally elliptic PROVIDED local ellipticity is closed under extensions of
  locally compact groups (Platonov's elliptic radical, 1966). That closure theorem was not
  read from a source in this lane, so this case is a remark, not a Cairn claim.
- *Relation to the product obstruction.* `tree-by-elliptic-lattices-satisfy-strong-atiyah`
  covers closed subgroups of (elliptic-by-abelian) × (tree group). Theorem 3 covers tree
  actions with elliptic stabilizers and needs no product decomposition.

## 2. What a witness complex must avoid

Collected from `complex-with-irrational-and-torsion-free-lattices` and this lane:
- a discrete `Aut(X)`;
- a contractible or CAT(0) `X`;
- `Aut(X)` closed in (elliptic-by-abelian) × tree (Theorem 2 of the transfer artifact);
- a tree action of `Aut(X)`, or of any subgroup containing the torsion-free group, with
  locally elliptic vertex stabilizers (Theorem 3).

## 3. Amenable hosts: a reduction pending source verification

**Statement (not landed as a node).** Suppose `X` is a witness, and the groups acting freely
and cocompactly on `X` are amenable. They are uniform lattices in `Aut(X)`, hence
quasi-isometric, so if one is amenable all are. Then the torsion-free `Γ` has zero divisors
in `C[Γ]`.

**Intended derivation.**
1. *Ore.* If `C[Γ]` had no zero divisors, it would be an Ore domain, because `Γ` is
   amenable (Tamari). Kielak's appendix to Bartholdi–Kielak, arXiv:1605.09133, is already
   cited abstract-level in `thompson-f-amenable-iff-group-ring-is-ore`.
2. *Analytic zero divisors.* For amenable groups, the algebraic zero-divisor property
   implies the analytic one: every nonzero element of `C[Γ]` acts injectively on `ℓ²(Γ)`.
   As recalled, this is due to Elek (Bull. London Math. Soc., early 2000s). NOT verified.
3. *Linnell's rank argument.* Each nonzero element of `C[Γ]` is then invertible in the
   algebra `U(Γ)` of affiliated operators. So the Ore localization `D` embeds in `U(Γ)` as a
   division ring, and matrices over `Z[Γ] ⊆ D` have integer von Neumann kernel dimensions.
   NOT read from source.
4. This contradicts the irrational value transferred to `Γ` by proportionality.

**Trust.** Steps 2 and 3 are from memory. The arXiv API returned HTTP 429 during this lane
(2026-09-12), so nothing was verified. The reduction is recorded only under Attempts on the
host claim.

**If verified:** a published *amenable* irrational example could transfer only through a
torsion-free amenable group whose complex group ring has zero divisors. By
Kropholler–Linnell–Moody that group is not elementary amenable. So such a witness would also
refute `kaplansky-zero-divisor-conjecture`.

## 4. Published irrational examples and co-lattice status

Recalled from memory at abstract level. None of these statements was re-read in this lane.

| Example | Group type | Amenable | Co-lattice status |
|---|---|---|---|
| Grigorchuk–Linnell–Schick–Żuk; Dicks–Schick (spectral measures) | `Z/2 ≀ Z`, Cayley graph `DL(2,2)` | yes | Dead by Theorem 2 if `Aut(DL)` has the product form (unchecked). Section 3 applies. |
| Austin (uncountably many kernel dimensions) | lamplighter-type over amenable bases | yes | Section 3 applies. No co-lattice known. |
| Grabowski (irrational and transcendental values) | lamplighter-based groups | yes, as recalled | Section 3 applies. No co-lattice known. |
| Lehner–Wagner (free lamplighters) | `Z/p ≀ F_n` | no | Candidate for Theorem 3 through the lamp-forgetting map to the tree of `F_n`, IF `Aut(X)` preserves that fibration with elliptic fibre stabilizers. Unchecked. |
| Pichot–Schick–Żuk (transcendental, closed manifolds) | finitely presented groups containing lamplighter pieces | no | Complexes come from embedding theorems, with no visible extra symmetry. No attack run. |

## 5. What remains

1. Verify from sources Platonov's extension closure, and whether `Aut` of a Cayley complex
   of `Z/p ≀ F_n` preserves the lamp fibration. Both would kill the free-lamplighter hosts.
2. Verify Section 3 (Elek; Linnell's rank argument). That would kill the amenable hosts,
   except through zero-divisor counterexamples.
3. The live region is non-amenable hosts with no tree action with elliptic stabilizers. One
   example is lamplighters over Kazhdan or one-ended bases; whether any of those carries an
   irrational value is not known here.
