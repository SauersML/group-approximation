# The KK norm functor, part 2: KK-equivalences, the functor, bootstrap norms

Lane ex2-uct-norm-functor, 2026-09-13.  Unreviewed.  Continues part 1
(`research/artifacts/uct-kk-norm-functor-2026-09-13-part1.md`), whose
Theorem A says: `A ≃_KK 0` implies `N(A) ≃_(KK^G) 0`.

## 5. Tensor powers of KK-equivalences

**Theorem B.**  Let `f : A → B` be a \*-homomorphism that is a KK-equivalence.
Then `f^(⊗p) : N(A) → N(B)` is a `KK^G`-equivalence.

*Proof.*
1. **Cylinder.**  Let `Z_f = {(a, g) ∈ A ⊕ B[0,1] : g(0) = f(a)}`.  The map
   `i : A → Z_f`, `a ↦ (a, const f(a))` is a homotopy equivalence, and
   `ev_1 : Z_f → B` is surjective with `ev_1 ∘ i = f`.  Its kernel is the
   mapping cone `C_f`, and `s(b) = (0, t ↦ t b)` is a contractive completely
   positive splitting.  `C_f ≃_KK 0` because `f` is a KK-equivalence (Puppe
   triangle).
2. **Equivariant homotopy.**  `i^(⊗p)` is a `G`-equivariant homotopy
   equivalence, since the tensor power of a homotopy is shift-equivariant.  So
   it suffices to show `ev_1^(⊗p) : N(Z_f) → N(B)` is a `KK^G`-equivalence.
3. **Filtration.**  For `0 ≤ k ≤ p` let `I_k ⊆ Z_f^(⊗p)` be the closed ideal
   `Σ_(|S| ≥ k) C_f^(⊗S) ⊗ Z_f^(⊗S^c)`, over subsets `S ⊆ {1, …, p}`.  Each
   `I_k` is shift-invariant, and `I_p = C_f^(⊗p) = N(C_f)` as a `G`-algebra.
   Because the extension `C_f ↪ Z_f ↠ B` has a c.p. splitting, the minimal
   tensor product is exact on it and on its tensor powers (standard slice-map
   fact, not re-read).  So:
   - `Z_f^(⊗p)/I_1 ≅ B^(⊗p)`, the quotient map being `ev_1^(⊗p)`;
   - `I_k/I_(k+1) ≅ ⊕_(|S| = k) C_f^(⊗S) ⊗ B^(⊗S^c)`, with `G` permuting the
     summands.
   Tensor products of `s` and identity maps give c.p. splittings of these
   extensions.  Averaging over the finite group `G` makes them equivariant.
   Equivariantly c.p.-split extensions give exact triangles in `KK^G`
   (standard, not re-read).
4. **Pieces.**  For `1 ≤ k ≤ p − 1` the `G`-set of `k`-subsets is free,
   because `p` is prime.  So `I_k/I_(k+1) ≅ Ind_1^G(D_k)` for
   `D_k = ⊕` over orbit representatives of `C_f^(⊗S) ⊗ B^(⊗S^c)`.  Since
   `C_f ≃_KK 0`, the exterior product gives `C_f ⊗ D ≃_KK 0` for every `D`,
   so `D_k ≃_KK 0`.  `Ind_1^G : KK → KK^G` is a functor, so `I_k/I_(k+1) ≃ 0`.
   For `k = p`: `I_p = N(C_f) ≃_(KK^G) 0` by Theorem A.
5. **Induction.**  Downward from `k = p`, the triangles
   `I_(k+1) → I_k → I_k/I_(k+1)` give `I_k ≃_(KK^G) 0` for all `k ≥ 1`.  The
   triangle `I_1 → N(Z_f) → N(B)` then makes `ev_1^(⊗p)` a
   `KK^G`-equivalence.  ∎

This is the C\*-analogue of the fact that a norm of a map with contractible
cofiber has contractible cofiber, where the cofiber filtration has induced
middle layers and the norm of the cofiber on top.

## 6. The functor

**Theorem C.**  There is a unique functor `N : KK → KK^G` with `N(A) = A^(⊗p)`
with the shift, and `N([f]) = [f^(⊗p)]` for every \*-homomorphism `f`.  It is
not additive on morphism groups.

*Proof.*  The functor `A ↦ N(A)`, `f ↦ f^(⊗p)` from separable C\*-algebras to
`KK^G` inverts KK-equivalences, by Theorem B.  The canonical functor from
separable C\*-algebras to `KK` is the localization at KK-equivalences: every
KK-class is a composite of \*-homomorphisms and inverses of KK-equivalence
\*-homomorphisms (Meyer, *Equivariant Kasparov theory and generalized
homomorphisms*, K-Theory 21 (2000); Meyer--Nest, *The Baum--Connes conjecture
via localisation of categories*, Topology 45 (2006), §2.1).  This standard
input was not re-read.  The universal property of the localization gives `N`
and its uniqueness.  Non-additivity: on `KK(C, C) = Z`,
`N(2) = [C^2 ⊗ C^2, flip] = 3 + χ ≠ 2 = 2 N(1)` for `p = 2`.  ∎

*Relation to part 1.*  The cycle-level norm of Proposition 1 should represent
`N(x)` for every cycle `x`.  That needs compatibility of the construction with
the Kasparov product, and it is not proved here.  Theorem C does not use it.
What Theorem C does not give: the sum formula
`N(x + y) = N(x) + N(y) + Σ_(orbits) Ind(mixed products)` and
`N(x ⊗ x') = N(x) ⊗ N(x')` for general KK-classes.  They hold for
\*-homomorphisms and direct sums of them, but the general case is not proved.

## 7. Consequences

1. **Equivalences.**  `A ≃_KK B` implies `N(A) ≃_(KK^G) N(B)`.
2. **Bootstrap norms.**  `N(B) ⊆ B^G`.  If `A ∈ B`, then `A ≃_KK C_0(X)` for
   a locally compact `X` (Rosenberg--Schochet), so
   `N(A) ≃_(KK^G) (C_0(X^p), permutation)`, a commutative, hence type I,
   `G`-algebra.  That lies in `B^G` by the Meyer--Nadareishvili description
   recorded in `zp-detection-equals-meyer-nadareishvili-sufficiency`.
3. **Contractible norms and Rokhlin shifts.**  Theorem A and Corollary A of
   part 1: the flip on `O_2 ⊗ O_2` and the shift on `O_2^(⊗p)` are Rokhlin.
   More generally, if `D` is unital, simple, purely infinite, `KK`-contractible
   and `D^(⊗p) ≅ O_2`, the shift on `D^(⊗p)` is Rokhlin.
4. **The action element of a norm.**  `θ_(N(A)) = [σ]` is the class of the
   shift.  On `N(C) = C` it is `1`.  On `N(M_n)` it is the class of an inner
   automorphism by a shift-fixed unitary, so it is `1`.  On `N(C ⊕ C)` it is not
   `1`, since that algebra contains induced summands `C(G)`, where translation
   is nontrivial.

## 8. The phantom question for norms

Let `P → C` be a cellular approximation of `C` by the localizing subcategory
generated by induced objects, with `Res(P → C)` a KK-equivalence (Meyer--Nest
complementary pair for the family of induced objects), and put `1_T = cone(P → C)`.
Then `Res 1_T ≃ 0`.  For every `A`, the object `T(A) := 1_T ⊗ N(A)` has
contractible restriction.  By `zp-restriction-trivial-splits-cellular-plus-phantom`,
item 3, it splits as `e T(A) ⊕ (1 − e) T(A)`, a trivial-action retract plus
an equivariant phantom.

* If `A ∈ B`, then `T(A) ∈ B^G` by item 2, so its phantom summand is `0`.
* If `(1 − e) T(A) ≠ 0` for some separable `A`, detection fails for all
  separable algebras, and `MN(all separable)` is false.  The same with `A`
  nuclear refutes `MN(nuclear)`.

So each non-bootstrap algebra `A` gives one concrete test object: is the shift
trivial in `KK^G` on the Tate part of `N(A)`?  Posed as the open claim
`tate-norm-shift-is-kkg-trivial`.  The adversarial non-nuclear case
`A = C*_r(Γ)` for `Γ` infinite hyperbolic with property (T) is in part 3.
