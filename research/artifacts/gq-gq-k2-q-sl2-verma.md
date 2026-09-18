# The sl_2 loophole for the stateless host target (lane gq-k2-q, 2026-09-18)

Verdict on Attempt 4 of `fp-simple-resolvent-ring-with-divisible-unit-class` (gq-ring-fp-simple, 76bf5bf69): the
sl_2 idea reduces to the same two-register comparison that killed the capacity chain, and the specific Casimir
fix provably fails. Below is the reasoning and the K-theory that would apply if a presentation existed.

## 1. Why sl_2 is attractive, and the exact danger

- `dim L(k) = k+1`, so the finite-dimensional irreducibles give the multiplicity `k+1` at level `k` with three
  fixed generators `e, f, h`, no growing-length letter.
- Danger, as the coordinator flagged: `U(sl_2)` also has the Verma modules `M(λ)`, infinite dimensional. If the
  host admits one, an element vanishing on all `L(k)` is nonzero on it, so the host is not simple. This is the
  `capacity-chain-presentation-is-not-simple` failure in a new guise.

## 2. The Casimir cannot rescue it (rigorous)

Node `sl2-casimir-cannot-separate-verma-from-finite-dimensional`.
- `Ω = 2fe + h + ½h²` acts by `½λ(λ+2)` on `M(λ)`.
- `½k(k+2) = ½(-k-2)(-k)`, and `f^(k+1) v_k` is a highest-weight vector of weight `-k-2` generating
  `M(-k-2) ⊆ M(k)`, with quotient `L(k)`.
- So every central element, and every resolvent of a central element, acts by one scalar on `M(k)` and on its
  Verma submodule. It cannot annihilate the submodule while keeping `L(k)`.
- The one element that cuts `M(k)` to `L(k)` is the singular vector `f^(k+1) v_k`, of length `k+1`: the
  growing-length relation, back again.

## 3. The general obstruction (heuristic, same strength as the capacity lesson)

Node `sl2-vacuum-hosts-admit-verma-type-modules`.
- Finite-dimensionality of a highest-weight `sl_2`-module = local nilpotence of `f` = `∀v ∃n f^n v = 0`, a `Π_2`
  condition.
- A finite presentation is a conjunction of `Π_1` relations. It cannot imply a `Π_2` condition that fails on some
  model of the relations. So a Verma-type highest-weight module satisfies all relations, and non-simplicity
  follows.
- Escaping this needs the presentation to force weight `>= -k`, i.e. to compare the running weight `h` to the top
  weight `k`: two unbounded registers, the `capacity-chain-presentation-is-not-simple` regime.

## 4. K-theory, if a presentation existed

Suppose, contrary to §3, that some finite presentation did realize exactly `⊕_k L(k) ⊗ m_k` with a vacuum. Then
under the Pimsner hypothesis (P) of `resolvent-register-units-give-rational-symbols`:
- `K_0` classes are the weight-space indicators. The level-`k` block contributes `dim L(k) = k+1` weight spaces,
  weights `k, k-2, ..., -k`.
- The recursion from `f` and `e` (each weight space maps to its neighbours) is a finite-difference operator on the
  weight lattice with reflecting ends at `±k`. Its cokernel per block is `Z` (the whole block collapses to one
  class `[L(k)]`), and the branching `[L(k)] -> (k+1)[pt]` is where a factor `k+1` could enter `[1]`.
- So the K_0 picture is the same as `R_cap`: `[1]` divisible by `k+1` at level `k`, hence by every `n` if all
  levels occur. The register units are now the Casimir/weight resolvents; their `1 - [X]` cokernel would have to
  vanish, as in `resolvent-register-units-give-rational-symbols`.
- All of this is void because §3 denies the presentation.

## 5. Recommendation

- Do not pursue Casimir or resolvent-of-Casimir cuts: refuted in §2.
- The sl_2 route needs the same well-foundedness that no finite presentation supplies. Treat it as another face of
  the capacity obstruction, not a new loophole.
- The two genuinely untested shapes remain: dilation letters `N ↦ pN + r` (outside
  `single-register-rings-divide-unit-at-finitely-many-primes`), and hosts not of register type. Quantum `sl_2` at a
  root of unity makes `f^ℓ = 0` finite but caps multiplicities at `ℓ`, so it lands back in the one-register
  bounded-multiplicity verdict.
