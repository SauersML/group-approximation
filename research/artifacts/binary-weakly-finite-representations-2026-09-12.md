# Weakly finite images of the binary complement corner

Lane `w5-wf-binary`, 2026-09-12. Supports `binary-complement-corner-has-no-weakly-finite-image` (OPEN),
`binary-corner-weakly-finite-images-are-unit-representations` (established on paper), and the route
`binary-cyclic-corner-from-no-weakly-finite-complement-image`.

## 0. Setup and sources

- `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, with the ternary family and `g`, `e = 1 + [g] + [g²]`,
  `f = 1 - e`, `T = f A f`, `D(h) = Σ s_i h t_i`, `ψ'(x) = f D(x)` as in
  `research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md` (Sections 0–1).
- `A_9 = ⟨g, D(g)⟩ ≅ C_3²`, and `f = f_(K_2) + f_(K_3) + f_(K_4)` with `f_K` the primitive idempotent of
  the two characters with kernel `K`.
- A ring `W` is weakly finite if `XY = I_n` implies `YX = I_n` for all square matrices over `W`.
- Inputs used:
  - Theorem B (`binary-cyclic-corner-full-iff-complement-corner-has-no-state`, pending verification):
    `c e b = 1` is solvable iff `T` fails the rank condition.
  - Theorem C (`rank-condition-rings-have-weakly-finite-images`, pending verification): a unital ring
    satisfies the rank condition iff it has a nonzero weakly finite image.
  - Simplicity of `G` (`binary-leavitt-unit-group-is-simple`), used only for (c) <=> (d) below.

## 1. Theorem W

**Theorem W.** The following are equivalent.
- (a) `c e b = 1` is solvable in `A`: the binary cyclic corner is full.
- (b) `T` has no nonzero weakly finite homomorphic image.
- (c) Every unital ring homomorphism `φ : A -> W` into a weakly finite ring has `φ([g]) = 1`.
- (d) Every group homomorphism from `G` into the unit group of a weakly finite ring of characteristic two
  is trivial.

**Lemma W.1 (corners and subrings).** If `W` is weakly finite and `p` is an idempotent of `W`, then `pWp`
is weakly finite, and so is every subring of `pWp` containing `p`.

*Proof.* If `XY = p I_n` over `pWp`, put `X' = X + (1-p) I_n` and `Y' = Y + (1-p) I_n`. Then `X'Y' = I_n`,
so `Y'X' = I_n`, and compressing by `p` gives `YX = p I_n`. A subring with the same unit inherits the
implication. QED

**Lemma W.2.** Let `q : T -> W` be a unital ring homomorphism with `W != 0`. Then
`φ = q ∘ ψ' : A -> W` is a unital ring homomorphism with `φ([g]) != 1`.

*Proof.* `ψ'` is unital (Lemma 1.1 of the complement-corner artifact), so `φ` is unital.
- `φ([g]) - 1 = q(f D(1 - [g]))`, and `f D(1 - [g]) = f (1 - [D(g)])`.
- In `F_2[A_9]`, `f_(K_2) [D(g)] = f_(K_2)`, while on the blocks of `K_3` and `K_4` the element `[D(g)]`
  acts by a primitive cube root of unity. So `1 - [D(g)]` is invertible in the block algebras of `K_3`
  and `K_4`, and `f(1 - [D(g)]) = (f_(K_3) + f_(K_4)) u` with `u` a unit of that block algebra.
- If `φ([g]) = 1`, then `q(f_(K_3) + f_(K_4)) = 0`, so `q(f_(K_3)) = 0` by orthogonality.
- Take `M` in `GL_2(F_3)` fixing `K_1` with `M K_3 = K_2`. Then `π_M` commutes with `f`, so
  `x = π_M f_(K_3)` and `y = f_(K_3) π_M^(-1)` lie in `T`, with `xy = f_(K_2)`. Since `x = x f_(K_3)`,
  `q(f_(K_2)) = 0`. The same with `K_4` gives `q(f_(K_4)) = 0`.
- So `q(f) = 0`. But `f` is the unit of `T`, so `W = 0`, a contradiction. QED

*Proof of Theorem W.*
- **(a) => (c).** Let `φ : A -> W` be unital with `W` weakly finite, and put `X = φ(c e)`, `Y = φ(e b)`.
  Then `XY = φ(c e b) = 1`, so `YX = φ(e b c e) = 1`. So `φ(e)` has a left inverse `φ(e b c)` and a right
  inverse `φ(b c e)`, hence is invertible. An invertible idempotent is `1`. So `φ(f) = 0`, that is,
  `u + u² = 0` for `u = φ([g])`. In characteristic two this is `u² = u`, and `u` is a unit, so `u = 1`.
- **(c) => (b).** If `q : T -> W` is a nonzero weakly finite image, Lemma W.2 gives `φ` with
  `φ([g]) != 1`.
- **(b) => (c).** Suppose `φ : A -> W` is unital, `W` weakly finite, and `u = φ([g]) != 1`. Then
  `φ(f) = u + u² != 0`, as in (a) => (c). By Lemma W.1, `φ(T) ⊆ φ(f) W φ(f)` is weakly finite, with unit
  `φ(f) != 0`. So `φ(T)` is a nonzero weakly finite image of `T`.
- **(c) => (d).** A group homomorphism `ρ : G -> W^x` with `W` of characteristic two extends to a unital
  `F_2`-algebra homomorphism `φ : A -> W`. By (c), `ρ(g) = 1`. So `ker ρ` is a normal subgroup containing
  `g != 1`, and `G` is simple, so `ρ` is trivial.
- **(d) => (c).** `φ` restricted to `G` is a homomorphism into `W^x`, and `W` has characteristic two
  because `φ` is unital. So it is trivial, and `φ([g]) = 1`.
- **(b) => (a).** By Theorem C, `T` fails the rank condition. By Theorem B (6 => 1), `c e b = 1` is
  solvable. QED

**What is elementary.** (a) => (c), (b) <=> (c) and Lemma W.1 use nothing beyond the complement-corner
artifact's Lemma 1.1 and the equivalence of the `f_K` inside `T`. (c) <=> (d) adds simplicity of `G`.
Only (b) => (a) uses Theorems B and C.

**Independence of `g`.** Statement (d) does not mention `g`. So every averaging corner to which Theorem B
applies is full simultaneously, or none is.

## 2. Consequences and dead sources

**The binary counterexample as a representation statement.** By Theorem W and
`binary-cyclic-corner-fullness-gives-kaplansky-failure`, the binary averaging corner, and with it the
binary Gottschalk counterexample on `G`, is exactly:

> `L_(F_2)(1,2)^x` has no nontrivial homomorphism into the unit group of any weakly finite ring of
> characteristic two.

**Sources of weakly finite targets. Each would refute (d), and none is known for `G`.**
1. **Rank functions.** A non-augmentation Sylvester rank function on `A` has a weakly finite null quotient
   (`sylvester-rank-function-quotients-are-weakly-finite`), in which `G` acts nontrivially. So
   `binary-leavitt-units-carry-nonaugmentation-rank-function` refutes (d).
2. **Linear soficity.** Rank ultraproducts of matrix algebras over fields of characteristic two are weakly
   finite. So an `F_2`-linear sofic approximation of `G` refutes (d). Hence (d) implies that `G` is not
   `F_2`-linear sofic.
3. **Stably finite group algebras.** If `G` maps nontrivially into the units of `F_2[H]` with `F_2[H]`
   stably finite, (d) fails. In particular (d) implies that `F_2[G]` is not weakly finite, which is the
   Kaplansky failure already known to follow from (a).
4. **Division rings: dead, elementary.** A nontrivial homomorphism `ρ : G -> D^x` with `D` a division ring
   of characteristic two is injective by simplicity. Then the `F_2`-span of `ρ(A_9)` is a finite commutative
   subring of `D`, so a finite field, whose multiplicative group is cyclic. That contains `C_3²`, a
   contradiction.
5. **Matrices over division rings: dead.** `T` has no unital homomorphism into `M_n(D)`
   (complement-corner artifact, Corollary 4.2).
6. **Commutative rings: dead.** `G` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`), so every
   homomorphism into an abelian unit group is trivial.

**The evaluation quotient is not weakly finite.** `π(f) = [g] + [g²]`, evaluated in `R`, is nonzero because
`g` has order three. `R` is purely infinite simple (Leavitt; Ara–Goodearl–Pardo, statement-level, not
re-read locally), so the corner `π(f) R π(f)` is not weakly finite. So a weakly finite image `q : T -> W`
cannot factor through `π`. Since `π(f) R π(f)` is simple, `q` must be nonzero on `f (ker π) f`: the
evaluation defect has to survive.
