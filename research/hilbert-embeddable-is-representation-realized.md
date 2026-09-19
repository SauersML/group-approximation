---
rg: 2
id: hilbert-embeddable-is-representation-realized
kind: claim
title: A Hilbert embeddable length is exactly the normalized-HS metric of a representation
distinct_from:
  hilbert-embeddable-length-hyperlinearity: that proves the conversion is possible, via Schoenberg and a character realization with constants depending on the parameter t; this identifies the length with a representation metric exactly, on the nose, and so replaces the asymptotic realization by an identity
  hilbert-embeddable-length-lp-feasibility: that says the witness question is a finite linear program; this identifies what the program's variables mean — the multiplicity vector of a unitary representation — and turns the whole design problem into a membership question about approximation by finite subgroups of unitary groups
  hilbert-embeddable-witness-for-kun-thom-wreath: that asks the design question for one group; this is the general structure theorem that removes the design step from it
artifacts:
  - notes/TRUE_HILBERT_EMBEDDABLE_IS_REPRESENTATION_REALIZED.md
---

Let `H` be finite and `ℓ` a real conjugation-invariant function with
`ℓ(1) = 0`, `ℓ ≥ 0`. Put `ψ_i(h) = d_i − Re χ_i(h) = ½‖π_i(h) − 1‖_F²`.
Then `ℓ` is Hilbert embeddable **iff** `ℓ = Σ_{i ≠ triv} a_i ψ_i` with
`a_i ≥ 0`, **iff** `ℓ(h) = ½‖ρ(h) − 1‖_F²` for a finite-dimensional unitary
representation `ρ` without trivial subrepresentation (exactly for integer
multiplicities; up to a positive scalar and arbitrarily small uniform error in
general). Normalizing, `ℓ(a⁻¹b) ∝ ‖ρ(a) − ρ(b)‖²_{2,norm}`.

**Consequence A — corrected twice; read the second correction.** The first
version of this node claimed the identity removes the uniformity-of-constants
exposure in `hilbert-embeddable-length-hyperlinearity` item 2, with no reason
given. The correction that replaced it asserted the opposite — that
`dim ρ` is "unbounded", so an exact realization gives normalized separation
`2ℓ(w)/dim ρ → 0` along a family. **That failure mode cannot occur**
(`cairn-verify`, audit 2026-08-14), and the corrected text is:

* `mean_H(ψ_i) = d_i` for every nontrivial `i`, since `Σ_h χ_i(h) = 0`.
  Hence in the trivial-free decomposition **`dim ρ = mean_H(ℓ)`** — the
  dimension of the realizing representation *is* the average of the length,
  not a free parameter.
* `ψ_i ≤ 2d_i` pointwise, hence **`max ℓ ≤ 2·mean_H(ℓ)`** for every Hilbert
  embeddable `ℓ`.

So for a witness normalized to `ℓ ≤ 1` with separation `c`, `mean_H(ℓ)` is
pinned into `[c/2, 1]`: the scalar `2/dim ρ` is bounded above and below by
absolute functions of `c`, the normalized-HS defect is at most `4δ/c` and the
normalized-HS separation at least `2c`. Far from being unbounded, `dim ρ ≤ 1`
whenever `ℓ ≤ 1`, which is exactly why exact integral realization of a
normalized length essentially never exists and the theorem says "up to a
positive scalar". The discrete-length calibration does not show otherwise: the
regular representation realizes `|K|·ℓ`, not `ℓ`, and `mean(|K|·ℓ) = |K|−1 =
dim(λ ⊖ triv)`, consistent with the identity.

Equivalently, in the **normalized character** `φ = χ_ρ/dim ρ`:
`½‖ρ(a) − ρ(b)‖²_{2,norm} = 1 − Re φ(a⁻¹b)`, and `1 − Re φ = Σ_i λ_i g_i` with
`g_i = 1 − Re χ_i/d_i` and `λ` on the **simplex**. Since `mean_H(g_i) = 1`,
the simplex constraint and `dim ρ = mean_H(ℓ)` are the same fact.

**Nevertheless item 2 of the criterion stands, for a different reason:
scalar-freeness.** The identity controls only `Re τ(ρ(h)) = 1 − ℓ(h)/dim ρ`
and leaves `|τ|` free; `|τ| = 1` exactly on scalars, where the upgrade to
maximal separation (`HyperlinearAmplification.exists_conjDouble_separation`,
and equally plain tensor powers) is unavailable at any number of copies. The
obstruction is realized, not hypothetical: on `Z/N`,
`ℓ(h) = ½(1 − cos(2πh/N))` is a Hilbert embeddable invariant length (kernel
test: conditionally negative definite, vanishing only at `0`) whose exact
realizer is the one-dimensional character `χ₁`, so every `ρ(h)` is a
**scalar** and `|τ(ρ(h))| = 1` for all `h ≠ 0`. On the same data the
Schoenberg trace `exp(−ℓ)` is real, positive and bounded away from `1`. So
the identity and item 2 compose; the identity does not replace it.

What survives, and is the reusable content, is the **cone description**:
the Hilbert embeddable invariant lengths are exactly the nonnegative
combinations of the `ψ_i`, equivalently of the `g_i`. Since `ψ_i = d_i g_i`
with `d_i > 0` the two generating sets span the same cone, so every ratio or
feasibility statement over the cone is independent of the choice.

**Consequence B — the design problem becomes a membership question.** For a
weak-soficity witness `φ : Φ → H` with defect set `X` and target set `T`,
asking for a Hilbert embeddable witnessing length is asking for a
finite-dimensional unitary representation `ρ` of `H` with `‖ρ(x) − 1‖₂` small
on `X` and `‖ρ(y) − 1‖₂ ≥ c` on `T`; and then `ρ ∘ φ` **is** the hyperlinear
microstate, since `ρ` is a homomorphism and all defects of `ρ ∘ φ` are `ρ(X)`.
Hence for a countable group `K` the following coincide:

* `K` is weakly sofic with Hilbert embeddable witnessing lengths;
* `K` has hyperlinear microstates factoring as `Φ → H → U(m)` with the second
  arrow a homomorphism;
* `K` is approximable by **finite subgroups of unitary groups** in normalized
  Hilbert–Schmidt. Call this class `𝒞_FU`.

`sofic ⊆ 𝒞_FU ⊆ hyperlinear`, the first inclusion because permutation matrices
give `‖σ − 1‖²_{2,norm} = 2 d_H(σ, 1)`.

So `hilbert-embeddable-witness-for-kun-thom-wreath` is exactly the membership
question `W ∈ 𝒞_FU`, with no metric left to design, and the linear program of
`hilbert-embeddable-length-lp-feasibility` is a program in the multiplicity
vector of `ρ`, readable off the character table. Whether `𝒞_FU` equals the
class of hyperlinear groups is a separate open question and is not needed:
`W ∈ 𝒞_FU` suffices for Question 3.4.
