# Referee report (gq-referee-a, proof-gap lens): register-comparison presentations are not simple

**Reviewed:** `register-comparison-presentations-are-not-simple` and its route `-proof` (lane gq-ring-fp-simple,
663115bfb), read on origin/main.

**Verdict: PASS.** No gaps found. Two points of precision are listed in §5. This generalizes the capacity refutation
I passed at b7958da79.

## 1. Lemma 1 (author's (a))
- **Diagonal action.** In a diagonal module a transport acts diagonally:
  `t_x f s_x η = α_x(v η)·F_f(σ_x(v η))·η`.
- **Constructible pieces.** Each `α_x` is a Boolean polynomial in indicators, so it is constant on the cells of a
  constructible partition. Cells pull back under the polynomial map `σ_x`: `{P = 0}` pulls back to `{P∘σ_x = 0}`.
- **Denominators.** On a pulled-back cell, `F_f∘σ_x = (a∘σ_x)/(b∘σ_x)`. The denominator `b∘σ_x` is nowhere zero
  there, because `σ_x` maps the pulled-back cell into the original cell.
- **Sums and products.** Take a common refinement, with denominator `bb'`.
- **Resolvents.** They are defined wherever their transported polynomials are nonzero. In any module where they
  act, this holds at every value.

Correct.

## 2. The generic cell (author's (b))
**No: a dense constructible set always contains a nonempty open set.**
- Write the cell in disjunctive normal form, as a union of terms `∩_{P ∈ A} {P = 0} ∩ ∩_{P' ∈ B} {P' ≠ 0}`.
- If every term has a nonzero polynomial in `A`, the cell lies in a proper closed set. So a dense cell has a term with
  no equations, and it contains `{Π_{P' ∈ B} P' ≠ 0}`.
- Two disjoint cells cannot both contain nonempty open sets of the irreducible affine space. So the generic cell is
  unique.
- The finitely many cells cover the space, which is not a finite union of proper closed sets. So some cell is dense.

## 3. Lemma 2 (author's (c))
- **Density.** Remove `{P_f = 0}` from the dense set of `M_Z`-values. What remains is still dense, because otherwise
  the space would be the union of two proper closed sets.
- **Vanishing.** `a` vanishes on that set, so `a = 0` as a polynomial over `Q`.
- **Over `Q(δ)`.** A `Q`-polynomial that vanishes on a Zariski-dense set of `Q`-points is zero, so the conclusion
  holds over every field `K ⊇ Q`, in particular `K = Q(δ)`.

## 4. The main proof and the instance
**§3 (author's (d)).** Every value of `M_k` is either δ-dependent or δ-free, so the two cases are exhaustive.
- **δ-dependent values.** `P_*` does not depend on `k`, so the third bullet of (C4) excludes only finitely many `k`.
- **δ-free values.** These are `M_Z`-values, where the extra relations vanish and the resolvents are nonzero.
- **The resolvents.** The added resolvents act by `1/Q_i(y) ∈ Q(δ)`. Their relations (`Q^{-1}Q = p_ρ`, commuting
  with range projections) hold pointwise.
- **The separating element.** On chain states, `λ_k = 1` and every `ε_i = 0`, because `Δ ∉ Z`. On `M_Z` states,
  exactly one `ε_i` is 1 when `L = k`, and otherwise `λ_k = 0`. Correct.

**§4 (author's (e)).**
- **Shape of `u`-states.** A `u`-state is `(c | a_u)^*` followed by either the chain or `st·ξ` with `ξ` a `v`-state.
- **Values reached from the chain.** Along `c` and `a_u` from the chain, `L ≥ k` (only `a_u` changes `L`, and it
  raises it) and `Δ ∈ δ + Z`.
- **Values reached after an `st`.** `Δ = L = N(ξ) − 1` is an integer. `c` is blocked at the integer 0, and `a_u`
  preserves `Δ ≤ L`. So these are integer triangle points, and all of them are `M_Z`-values.
- **`v`-values.** `N(dη) = L(η)`, an integer.
- **The divisibility count.** `P(δ + j, k') = 0` iff `(L − k') | P`, which holds for at most `deg_L P` values of
  `k'`. Since `k' ≥ k`, only finitely many `k` are affected.
- **(C3) density.** A polynomial vanishing on the integer triangle is divisible by `L − k` for every
  `k > deg_Δ P`, so it is zero. And `N ∈ Z_{≥0}` is dense in `Q`.

Correct.

## 5. Points of precision (non-blocking)
1. **Choice of `P_f`.** Choose it from a DNF term with no equations, as in §2. Then `{P_f ≠ 0} ⊆ C_f` holds as a
   formula over every field `K ⊇ Q`. That is what is used at the δ-dependent values of `M_k`, which lie over `Q(δ)`
   and not over `Q`.
2. **Extra relations not in a single type.** An extra relation `f_j` need not be supported at a single type. Apply
   Lemmas 1 and 2 type by type, using `f_j p_ρ`, and let `P_*` be the product over types.
