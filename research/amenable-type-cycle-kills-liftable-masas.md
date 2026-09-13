---
rg: 2
id: amenable-type-cycle-kills-liftable-masas
kind: claim
title: A long cyclic shift of central vertex types normalizes the vertex commutant exactly, yet its fixed algebra has no liftable masa
distinct_from:
  actor-commutant-has-liftable-masa-in-every-model: that is the open existence of a liftable masa for every model of the Kazhdan Theorem E actor; this is an established model test outside Kazhdan scope, showing that exact normalization plus ultraproduct saturation do not produce one.
  hs-block-gap-iff-liftable-masa-of-actor-commutant: that proves a liftable masa is equivalent to the summed block gap when the actor is Kazhdan; this exhibits an exactly normalizing configuration, with no Kazhdan actor, where no partition algebra is maximal abelian at all.
  hs-vertex-rounding-and-liftable-masa-force-normalization: that derives normalization from vertex rounding plus a liftable masa; this shows the converse direction fails for a single cyclic compressor, so the masa input is strictly stronger than normalization in general.
---

**ESTABLISHED.** Let `U` be a free ultrafilter, `M = prod_U M_(N_n)` with normalized trace, and for
each `n`:
- `A_n <= M_(N_n)` a unital `*`-subalgebra;
- `e_(n,k)`, `k in Z/L_n`, projections in the center `Z(A_n)` with `sum_k e_(n,k) = 1`;
- `V_n in U(N_n)` with `V_n A_n V_n^* = A_n` and `V_n e_(n,k) V_n^* = e_(n,k+1)`.

Assume `L_n -> infinity` along `U`. Put `A = prod_U A_n`, `V = [V_n]` and `Q = {V}' cap A`.

1. `V A V^* = A` exactly, at every finite stage.
2. No abelian subalgebra `C = prod_U C_n <= Q`, with `C_n` spanned by a finite partition of unity
   of `M_(N_n)` by projections, contains `Z(Q)`. Hence `Q` has **no** maximal abelian subalgebra
   that lifts to finite partitions.
3. Quantitatively: if `eps_n^2 = sum_A ||[V_n, q_(n,A)]||_2^2` is the summed boundary of `C_n`, the
   unitary `f_j = sum_k exp(2 pi i j k / L_n) e_(n,k)` satisfies
   `||f_j - E_(C_n) f_j||_2^2 >= 1 - sqrt(2) eps_n / |1 - exp(2 pi i j / L_n)|`, while
   `||[V_n, f_j]||_2 = |1 - exp(2 pi i j/L_n)|`.
4. **Separable pieces lift.** For any `j_n` with `j_n / L_n -> 0`, the central unitary `[f_(j_n)]`
   lies in a liftable abelian subalgebra of `Q` (partition `Z/L_n` into intervals of length
   `ceil((L_n / j_n)^(1/2))`). So the obstruction is not visible on any one element.

**Example.** `N_n = L_n d_n m_n`, `A_n = D_(L_n) (x) 1_(d_n) (x) M_(m_n)`, `V_n = S_(L_n) (x) 1 (x) 1`
with `S` the cyclic shift. With `d_n = m_n = 1`, `Q` is the algebra of almost shift-invariant
functions on `Z/L_n`, and item 2 is the statement that the cyclic almost action of `Z` has no Kun
decomposition. It is realized by genuine representations of `Gamma x|_alpha Z` whenever `Gamma` is
Kazhdan and `alpha` moves an irreducible representation of dimension `d_n` around an orbit of exact
length `L_n`: by `at-op62-holds-for-representation-lifts`, `sigma(Gamma)' cap M = A`.

## Reading

- **Normalization does not give (LM).** In the example the compressor normalizes the vertex
  commutant exactly and preserves every aspect ratio `d_n / m_n`, and still no liftable masa exists. So
  `actor-commutant-has-liftable-masa-in-every-model` is not a formal consequence of normalization,
  of countable saturation, or of genuine coordinates for the vertex.
- **What it costs.** The obstruction lives entirely in `Z(Q) cap prod_U Z(A_n)`, the central type
  observables, and it is the Hilbert--Schmidt face of the failure of Kun--Thom Lemma 2.3 for an
  amenable almost action on types. A proof of (LM) at a Kazhdan pair must spend property (T) of
  the group acting on vertex types, at least to exclude long cycles of types on most of the mass.
- **Zorn, realized.** The interval partitions of item 4, refined along any sequence, form chains of
  liftable abelian subalgebras of `Q` with no liftable masa above them. This is the failure recorded
  in the Attempts of `actor-commutant-has-liftable-masa-in-every-model`, now in an explicit model.
- **Not claimed.** Nothing here constructs a model of the Theorem E actor. A counterexample there
  must be a model of `G` that is not flexibly roundable on `G`
  (`at-op62-holds-for-representation-lifts` gives (LM) for genuine coordinates of a Kazhdan actor).

Derivation: `amenable-type-cycle-kills-liftable-masas-proof`.
