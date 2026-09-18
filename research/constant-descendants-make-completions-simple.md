---
rg: 2
id: constant-descendants-make-completions-simple
kind: claim
title: If every nonzero element of a self-similar algebra has a nonzero descendant in a simple constant subalgebra S (psi(s) = s I), the recursion is minimal and aperiodic; this one criterion covers Leavitt tensor hosts and transducer hosts alike
distinct_from:
  scalar-descendants-make-completions-simple: that is the case S = K of scalars; this allows any simple unital subalgebra fixed diagonally by the recursion, which is what escapes the residual finite-dimensionality forced by scalar constants.
  simple-ln-completion-premise-is-equivalent-to-algebra-bh: that uses the trivial recursion b ↦ b I on a simple base; this is the general criterion, of which that is the case j = 0 with S the whole base.
---

**ESTABLISHED** (lane proof, bh-algebra, elementary, not reviewed). The proof is that of
`scalar-descendants-make-completions-simple-proof`, with scalars replaced by constants.

**Setting.** `ψ : A -> M_d(A)` is an injective unital recursion, `d >= 2`. `S ⊆ A` is a simple unital
subalgebra with `ψ(s) = s I_d` for every `s ∈ S` (the *constants*).

**Claim.** If every nonzero `a ∈ A` has `ψ_j(a)_(uu') ∈ S \ {0}` for some `j, u, u'`, then `A` is
ψ-minimal and `(A, ψ)` is aperiodic, so `O_ψ(A)` is simple.

**Proof.**
- *Minimality.* A saturated ideal `I ∋ a` contains all entries of every `ψ_j(a)`, so it contains some
  `0 ≠ s ∈ S`. Then `I ⊇ S s S = S ∋ 1`, because `S` is simple.
- *Aperiodicity.* In §§3–4 of the scalar proof, the only properties of `λ` used are
  `ψ_m(λ)_(rr) = λ ≠ 0` and `ψ_m(λ)_(rr') = 0` for `r ≠ r'`, both true for `s ∈ S` since `ψ(s) = s I`.
  The word-combinatorics contradiction is unchanged. ∎

**Instances.**
- `S = K`: scalar descendants, as in `lossless-monomial-recursions-give-simple-completions`. The inputs
  are residually finite-dimensional (`scalar-descendant-hosts-see-only-rfd-inputs`).
- `S = A` simple with `ψ(a) = a I`: then `j = 0` works for every `a`, and `O_ψ(A) = A ⊗ L_d` is simple.
  This is the Leavitt tensor host.
- **Mixed hosts.** `A = (S * K<G>)/J`, with `ψ(s) = s I` on a finitely presented simple `S` and a
  transducer on `G`. The completion is finitely presented
  (`noninjective-ln-completions-have-self-similar-bases`), and simple once every surviving element
  contracts to `S \ 0`.

**Lesson for general BH.** Leavitt tensor hosts and transducer (self-similar) hosts are two ends of one
mechanism: *contraction to a simple constant algebra*. Tensor hosts contract in zero steps but add no
complexity. Transducer hosts add arbitrary complexity through the time-to-die, but with scalar constants
they only see residually finite-dimensional inputs. Mixed hosts over a fixed finitely presented simple
constant algebra `S` can have both. So algebra Boone--Higman reduces to one realizability question:
does every decidable algebra embed in a surviving quotient `(S * K<G>)/J` that contracts to `S`, for one
universal `S` (for example `L_2`, or `R_(p,k)` ⊗ `L_2`) and a transducer depending on the input?
