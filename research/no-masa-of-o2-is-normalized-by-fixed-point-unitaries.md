---
rg: 2
id: no-masa-of-o2-is-normalized-by-fixed-point-unitaries
kind: claim
title: For an automorphism of O_2 of prime order, no masa of O_2 is normalized by all exp(ih) with h self-adjoint in the fixed-point algebra, so invariant Cartan subalgebras are never unique or natural under conjugation
distinct_from:
  o2-z2-actions-fix-a-cartan-subalgebra: that asks for one Cartan subalgebra invariant under the automorphism itself; this proves that no masa is invariant under the unitaries exp(ih) of the fixed-point algebra, which all commute with the automorphism, so every invariant Cartan subalgebra breaks that symmetry and no conjugation-natural choice of one exists.
  o2-z3-actions-fix-a-cartan-subalgebra: that is the existence question at p = 3; this is the same symmetry-breaking no-go, proved for every prime p at once.
  cartan-respecting-o2-automorphisms-give-uct-crossed-products: that exhibits automorphism families that preserve a Cartan subalgebra; this rules out masas preserved by the identity component of the fixed-point unitary group, for every automorphism of prime order.
  bootstrap-class-zp-actions-on-o2-fix-a-cartan: that proves an invariant Cartan subalgebra exists for bootstrap-class actions; this shows that even then it is never unique, and none is fixed by the identity component of the fixed-point unitary group.
---

**ESTABLISHED (derivation, this repository; elementary, no priority claim).**
Let `p` be a prime, `α ∈ Aut(O_2)` with `α^p = id`, `O_2^α` its fixed-point
algebra, and `U_0(O_2^α)` the path component of `1` in the unitary group of
`O_2^α`. A *masa* is a maximal abelian C\*-subalgebra. No outerness or strong
approximate innerness is assumed.

1. **Normalizing one-parameter groups lie in the masa.** Let `A` be a unital
   C\*-algebra, `D ⊆ A` a masa and `h = h*` in `A`. If
   `e^{ith} D e^{-ith} ⊆ D` for all `t` in some interval `(0, ε)`, then
   `h ∈ D`.
2. **Commutative fixed points force small representations.** Let `β` be an
   automorphism of a C\*-algebra `A` with `β^p = id`. If `A^β` is
   commutative, every irreducible representation of `A` has dimension at most
   `p`. `O_2` has no nonzero finite-dimensional representation, so `O_2^α` is
   not commutative.
3. **No-go.** No masa `D ⊆ O_2`, hence no Cartan subalgebra, satisfies
   `e^{ih} D e^{-ih} = D` for every self-adjoint `h ∈ O_2^α`. In particular,
   no masa of `O_2` is invariant under `Ad u` for all `u ∈ U_0(O_2^α)`.
   Quantitatively: for every masa `D` there are a self-adjoint `h ∈ O_2^α`
   and `a ∈ (0, ∞]` such that `t ↦ e^{ith} D e^{-ith}` is injective on
   `[0, a)`.
4. **Invariant Cartan subalgebras are never canonical.**
   - Suppose `D` is an `α`-invariant Cartan subalgebra (or masa). Then so is
     `u D u*` for every `u ∈ U(O_2^α)`. This family is uncountable, and no
     member of it is fixed by all of `U_0(O_2^α)`.
   - Let `𝒜` be a nonempty set of automorphisms `α` of `O_2` with
     `α^p = id`, closed under `α ↦ Ad u ∘ α ∘ Ad u*` for `u ∈ U_0(O_2)`.
     Examples: the `U_0(O_2)`-conjugation orbit of one such automorphism;
     the set of all outer strongly approximately inner `Z/p`-actions, which
     is closed under this conjugation, as soon as it is nonempty. There is no
     map `Φ` from `𝒜` to masas of `O_2` with
     `Φ(Ad u ∘ α ∘ Ad u*) = u Φ(α) u*` for all `α ∈ 𝒜` and `u ∈ U_0(O_2)`.
     This holds whether or not `α(Φ(α)) = Φ(α)` is required.
5. **Contrast at `p = 2`: invariant masas always exist.** For any
   automorphism `α` of a C\*-algebra with `α^2 = id`, every maximal element
   among the `α`-invariant abelian C\*-subalgebras is a masa. Such elements
   exist by Zorn's lemma.

Proof: `no-masa-of-o2-is-normalized-by-fixed-point-unitaries-proof`.

**Bearing on `o2-z2-actions-fix-a-cartan-subalgebra` (and its `p = 3`
sibling).**
- **Where the difficulty is.** At `p = 2`, by item 5, maximality is free.
  What the claim asks beyond an invariant masa is regularity together with a
  faithful conditional expectation. (Item 5 is not proved for `p = 3`.)
- **What a proof must use.** By items 3 and 4, an invariant Cartan
  subalgebra has to be built from data not determined by `α` up to
  conjugation by `U_0(O_2^α)`: for example a choice of towers, of a groupoid
  model, or of a realization of a KK-class. No recipe that assigns "the"
  invariant Cartan subalgebra equivariantly under inner conjugation can
  exist. This is one precise form of the failure recorded in the target's
  Attempts, that classification supplies no coherence; it does not rule out
  non-equivariant choices along a specially chosen approximation.
- **What it does not obstruct.** Existence is untouched. Bootstrap-class
  actions do fix Cartan subalgebras
  (`bootstrap-class-zp-actions-on-o2-fix-a-cartan`). By item 4 those
  subalgebras come in uncountable `U(O_2^α)`-orbits.
