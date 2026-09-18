---
rg: 2
id: scalar-descendant-hosts-see-only-rfd-inputs
kind: claim
title: A self-similar algebra with a character and scalar descendants is residually finite-dimensional, so scalar-descendant completions host only residually finite-dimensional inputs, the algebra face of the residual-finiteness wall
distinct_from:
  scalar-descendants-make-completions-simple: that proves simplicity from scalar descendants; this identifies the price, residual finite-dimensionality of the base, whenever a character is present, as in every lossless monomial recursion.
  lossless-monomial-recursions-give-simple-completions: that is a host construction whose base is monomial; this shows why every input it can host is residually finite-dimensional, and why a constant field is needed to go further.
---

**ESTABLISHED** (lane proof, bh-algebra, elementary, not reviewed).

**Claim.** Let `ψ : A -> M_d(A)` be a unital recursion and `ε : A -> K` a character (unital algebra
homomorphism). If every nonzero `a ∈ A` has a scalar descendant, then `A` is residually
finite-dimensional: the homomorphisms `ρ_j = M_(d^j)(ε) ∘ ψ_j : A -> M_(d^j)(K)` separate the points of
`A`.

**Proof.** Each `ρ_j` is a homomorphism, being a composite of homomorphisms. If `a ≠ 0` has
`ψ_j(a)_(uu') = λ ∈ K^x`, then `ρ_j(a)_(uu') = ε(λ) = λ ≠ 0`. ∎

**Where a character comes from.** In `lossless-monomial-recursions-give-simple-completions` the base is
`K<G>/J` with `J` spanned by dying words. The empty word never dies, so `J` lies in the augmentation
ideal, and augmentation is a character. So every algebra hosted in the base of such a completion is
residually finite-dimensional.

**Consequences.**
- The monomial benchmark `A_X` is residually finite-dimensional (quotients by all words of length
  `> L` separate points), so this wall does not exclude it.
- A field such as `K(t)` has no nonzero finite-dimensional module (a minimal polynomial of `t` would not
  be invertible), so it lies in no such base. `char-p-rational-function-fields-in-fp-simple-algebras`
  reaches `F_p(t)` precisely because its descendants contract to units of a constant field `F_p(t)`,
  not to scalars of `K = F_p`.

**Lesson for general BH.** Simplicity of Leavitt--Nekrashevych (and Röver--Nekrashevych) envelopes is
"contraction to constants": every nonzero element must have a descendant that is a unit fixed diagonally
by the recursion. The constants then bound the inputs. With scalar constants `K` the input must be
residually finite-dimensional. This is the algebra form of the wall that makes faithful self-similar
groups residually finite. To host general inputs, the construction must choose a larger constant
object, a field or a simple algebra, for the recursion to contract to. Both the register completions
here (constant field `F_p(t)`) and the Leavitt tensor hosts `B ⊗ L` (constant simple algebra `B`) do this.
