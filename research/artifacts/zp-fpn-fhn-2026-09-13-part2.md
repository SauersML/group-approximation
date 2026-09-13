# FP_n versus FH_n (Zaremsky Problem 1.4), part 2: acyclic kernels and the case n = 3

Lane z1-04-fp-fh, 2026-09-13. Conventions and Lemma S are in
`zp-fpn-fhn-2026-09-13-part1.md`. Status of every statement: unreviewed.

## 5. Theorem E: quotients by acyclic kernels

**Theorem E.** Let `n ≥ 1`, and let `G` be of type `FP_n`. Suppose there is a
group `Q` of type `F_{n−1}` and a surjection `Q → G` whose kernel `P`
satisfies `H̃_i(P; ℤ) = 0` for `0 ≤ i ≤ n−1`. Then `G` is of type
`FH_n^free`.

*Proof.* Let `B` be a `K(Q,1)` with finite `(n−1)`-skeleton, and let
`Z → B` be the covering with deck group `G` corresponding to `P`. Then `Z` is
a `K(P,1)` and a free `G`-CW complex with `Z/G = B`. Set `X = Z^{(n−1)}`.
It has finitely many orbits of cells, and `H_i(X) = H_i(Z) = H_i(P)` for
`i ≤ n−2`, so `X` is `(n−2)`-acyclic.

The cellular sequence `C_{n−1}(X) → ⋯ → C_0(X) → ℤ → 0` is exact at every
place except `C_{n−1}`, with finitely generated free terms. By Lemma S
(`k = n`), `H_{n−1}(X) = ker(C_{n−1} → C_{n−2})` is a finitely generated
`ℤG`-module.

`H_{n−1}(X) → H_{n−1}(Z) = H_{n−1}(P) = 0`, and passing from `X` to `Z`
attaches cells of dimension `≥ n`. So `H_{n−1}(X)` is spanned by the
boundaries `∂e ∈ Z_{n−1}(X)` of the `n`-cells `e` of `Z`. Each of finitely
many module generators of `H_{n−1}(X)` is a finite combination of such
boundaries. Let `Y ⊆ Z^{(n)}` be `X` together with the `G`-orbits of the
finitely many `n`-cells involved. `Y` is a free `G`-CW complex with finitely
many orbits of cells, `H_i(Y) = H_i(X) = 0` for `i ≤ n−2`, and
`H_{n−1}(Y) = H_{n−1}(X)/ℤG⟨∂e⟩ = 0`. ∎

Remarks.
- For `n = 2` the hypothesis on `P` is stronger than necessary: Theorem B
  uses the free group `Q` with kernel the relation subgroup, which is not
  perfect.
- Bestvina–Brady kernels over finite `(n−1)`-acyclic flag complexes are
  `FH_n` directly, through their level sets, and Theorem E is not needed
  for them.

## 6. Theorem D: characterization of FH_3

**Theorem D.** `G` is of type `FH_3` (either reading) iff `G` is of type
`FP_3` and there are a finitely presented group `Q` and a surjection `Q → G`
whose kernel `P` is superperfect, `H_1(P) = H_2(P) = 0`.

*Proof of ⇐.* A finitely presented group is of type `F_2`. Apply Theorem E
with `n = 3`.

*Proof of ⇒.* By Theorem C and the skeleton remark there is a free `G`-CW
complex `Y` that is 2-acyclic, with finitely many orbits of cells and
dimension `≤ 3`. `K = Y/G` is a finite complex and `Y → K` is a regular
covering with deck group `G`, so `Q := π_1(K)` is finitely presented and
`1 → P → Q → G → 1` with `P = π_1(Y)` (`Y` is connected). `H_1(P) =
H_1(Y) = 0`. Build a `K(P,1)` from `Y` by attaching cells of dimension
`≥ 3`. Attaching 3-cells can only quotient `H_2`, and higher cells do not
touch it, so `H_2(Y) → H_2(P)` is onto. With `H_2(Y) = 0` this gives
`H_2(P) = 0`. `FP_3` holds by Theorem A. ∎

**Corollary.** At `n = 3`, Problem 1.4 is equivalent to the purely
group-theoretic statement: *every group of type `FP_3` is a quotient of a
finitely presented group by a superperfect normal subgroup.*

The kernel of `H_2(Y) → H_2(P)` in the ⇒ proof is exactly the Hurewicz image
`h(π_2 Y)` (Hopf). So the only obstruction to attaching 3-cells to the
`G`-cover of a presentation complex is `H_2(P)`.

## 7. General n: what is and is not proved

- Theorem E gives `FP_n` plus "some `F_{n−1}` group maps onto `G` with
  `(n−1)`-acyclic kernel" ⇒ `FH_n`.
- The converse at general `n` would follow from a finite Kan–Thurston
  theorem: a finite aspherical `T` with a map `T → K = Y/G` inducing
  isomorphisms on homology with all local coefficient systems on `K`. Then
  `π_1(T) → π_1(K) → G` is onto. Pulling back the covering `Y → K` gives a
  covering `T_G → T` with deck group `G`. `T_G` is aspherical, so it is a
  `K(P_T,1)` for `P_T = ker(π_1 T → G)`, and `H_*(T_G) ≅ H_*(Y)` (homology
  of `K` with coefficients `ℤG`). So `P_T` is `(n−1)`-acyclic and
  `π_1(T)` is of type `F`. The finiteness version of Kan–Thurston is
  attributed to Baumslag–Dyer–Heller (1980). The exact statement has **not**
  been checked from the source here. Leary, *A metric Kan–Thurston theorem*
  (arXiv:1009.1540), abstract read 2026-09-13, states only "t_X is a homology
  isomorphism" in the abstract. So the general-`n` converse is recorded as
  unverified and nothing depends on it.
- At `n = 3` no citation is needed: Theorem D is complete.

## 8. Attempts on the n = 3 question (where each dies)

Setup: `G` of type `FP_3`; `Q_0` finitely presented with perfect kernel
`P_0`, which exists by `FP_2`; `X_0` the `G`-cover of a presentation
complex. `H_2(P_0)` is a quotient of the finitely generated module
`H_2(X_0)`, so it is a finitely generated `ℤG`-module.

1. *Kill a perfect subgroup.* Attach 2-cells along finitely many `Q_0`-normal
   generators of a perfect `N ◁ Q_0` with `N ≤ P_0`. Because `H_1(N) = 0`,
   the Lyndon–Hochschild–Serre sequence gives
   `H_2(N)_{P_1} → H_2(P_0) → H_2(P_1) → 0` with `P_1 = P_0/N`, and `P_1` is
   perfect. This removes `H_2(P_0)` iff `H_2(N) → H_2(P_0)` is onto, which
   holds if every generator of `H_2(P_0)` is supported on a finitely
   generated perfect subgroup of `P_0`. Dies: classes of a perfect group need
   not be supported on finitely generated perfect subgroups. Enlarging the
   support to make it perfect is an infinite regress.
2. *Amalgamate a superperfect finitely presented `B`* along a finitely
   generated `A ≤ P_0` supporting the classes, mapping `B → 1`. The new
   kernel is a tree of groups `P_0 *_A (∗_{g∈G} B^g)`. Mayer–Vietoris removes
   `im H_2(A)` but adds `⊕_{g∈G} H_1(A)` to `H_2`. Dies unless `A` is
   perfect, which is item 1 again.
3. *Glue acyclic groups along surface subgroups* representing the classes.
   Mayer–Vietoris adds `⊕_{g∈G} H_1(Σ)`, classes of curves that bound on
   both sides. Dies the same way.
4. *Universal central extension of `P_0`.* It is superperfect, and the
   `Q_0`-action lifts, but the resulting extension of `Q_0` by `H_2(P_0)` is
   finitely presented only in special cases: `ℤ[t^{±1}] ⋊ ℤ` shows a cyclic
   module does not suffice.
5. *Homological invariants for a No answer.* A superperfect kernel forces
   `H_k(Q; M) ≅ H_k(G; M)` for `k ≤ 2` and all `ℤG`-modules `M`, and
   `H_3(Q; M) ↠ H_3(G; M)`. All of this is compatible with `FP_3` and `Q`
   finitely presented, so no obstruction comes from low-degree homology. A
   separating group needs an invariant that sees every finite presentation
   with perfect kernel at once.
