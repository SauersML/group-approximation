---
rg: 2
id: neumann-doubling-host-is-not-fp
kind: claim
title: The doubling host of Neumann's group is not finitely presented, because sparse doubling orbits give fake actions of every truncated presentation
distinct_from:
  neumann-doubling-host-candidate: that builds the residually finite host Γ = ⟨α, β, x↦2x⟩ and reduces its finite presentability to whether the truncations Γ_K stabilize; this proves they never do.
  neumann-alternating-product-group-embeds-in-fp-rf-group: that is Minasyan's open question; this kills one candidate host and leaves the question open.
---

**ESTABLISHED** (elementary; written inline by lane bh-free-59, not independently
reviewed). **Refutes** the candidate in `neumann-doubling-host-candidate`, whose notation
is used here: `Γ = ⟨α, β, s⟩ ≤ ∏_{m∈M} Sym(Z/m)`, with

    Γ_K = ⟨α, β, s | sβs^{-1} = β^2, sαs^{-1} = u(a_0,a_1,a_2), relations of W_K⟩,

and `Γ` is finitely presented iff `Γ_K → Γ` is an isomorphism for some `K`.

**Theorem.** For every `K` there is a finite quotient of `Γ_K` that is not a quotient of
`Γ` compatibly with the generators. So `Γ` is not finitely presented.

## Step 1: fake actions of Γ_K

Take `m ∈ M` and a nonempty set `O ⊆ Z/m` such that:
- `O` is invariant under `x ↦ 2x`;
- `O` is **`K'`-sparse**: `o − o' ∉ [−K', K']` (mod `m`) for all `o ≠ o'` in `O`,
  where `K' = max(K+2, 6)`.

On `Z/m` let `β` act by `x ↦ x+1`, let `s` act by `x ↦ 2x`, and let
`α' = ∏_{o∈O} (o, o+1, o+2)`. Put `a'_i = β^iα'β^{-i} = ∏_o (o+i, o+i+1, o+i+2)`.

- `sβs^{-1} = β^2` holds as in the honest coordinates.
- `sα's^{-1} = ∏_o (2o, 2o+2, 2o+4) = ∏_o (o, o+2, o+4)`, because `x ↦ 2x` permutes `O`.
  By sparsity, `a'_0, a'_1, a'_2` act on the disjoint blocks `[o, o+4]` as translated
  copies of `a_0, a_1, a_2` on `{0,…,4}`. So `u(a'_0,a'_1,a'_2) = ∏_o (o, o+2, o+4)`.
- `a'_0,…,a'_K` act on the disjoint windows `[o, o+K+2]` as translated copies of the
  window action `W_K → Alt({0,…,K+2})`, `a_i ↦ (i, i+1, i+2)`. That is a homomorphism, so
  every relation of `W_K` holds.

So `(α', β, s)` defines an action of `Γ_K` on `Z/m`.

## Step 2: such sets exist for every K

Take `r` prime with `(2^r−1)/4 > 2K'r^2`, and put `m = 2^r − 1 ∈ M`. For
`0 < k < r`, `gcd(2^k − 1, m) = 2^{gcd(k,r)} − 1 = 1`, so every difference
`2^i − 2^j` with `i ≢ j (mod r)` is a unit mod `m`. At most `2K'r^2` values of `y_0` put
some `y_0(2^i − 2^j)` in `[−K', K']`. Every prime factor of `m` is `≡ 1 (mod r)`, and
there are fewer than `r` of them, so `φ(m) ≥ m(1 − 1/r)^r ≥ m/4`. Hence some unit `y_0`
avoids all bad values, and `O = {2^i y_0 : 0 ≤ i < r}` is doubling-invariant and
`K'`-sparse, with `r ≥ 3` points.

## Step 3: a relation of Γ that the fake breaks

Let `y = y_0`, `z = 2y_0`, `w = 4y_0 ∈ O`. Choose integers `d, e` with:
- `d ≡ y + 2 − z`, `e ≡ y − 2 − w` (mod `m`);
- `gcd(d−2, e+2) = 1`.

This is possible: `d − 2 ≡ −y_0` is a unit mod `m`, so any such `D = d − 2 ≠ 0` is prime
to `m`, and by CRT we can take `E = e + 2 ≡ −3y_0 (mod m)` with `E ≡ 1 (mod D)`.

**Fake side.** By sparsity, the only clusters of `a'_0`, `a'_d`, `a'_e` meeting
`Ω = [y−2, y+4]` are `(y, y+1, y+2)`, `(z+d, …) = (y+2, y+3, y+4)` and
`(w+e, …) = (y−2, y−1, y)`. So `Ω` is one orbit of `⟨a'_0, a'_d, a'_e⟩`, which acts on it
as `A_7`. This gives a map `φ` onto `A_7` sending the three generators to that chain of
3-cycles.

**Honest side.** `H = ⟨a_0, a_d, a_e⟩ ≤ Γ` is finite, because `G_0` is locally finite,
and it embeds in `∏_{m'∈M} H_{m'}` via the coordinates. Suppose `φ` were defined on `H`,
i.e. suppose the fake were a `Γ`-action.
- A homomorphism from a subdirect product onto a nonabelian simple group factors through
  one factor. (If each of the finitely many coordinate kernels `K_j` maps onto `S`, then
  iterated commutators of the `K_j` map onto `S` but lie in `⋂K_j = 1`.)
- So `φ` factors through some `H_{m'} = ⟨(0 1 2), (d', d'+1, d'+2), (e', e'+1, e'+2)⟩`,
  with `d' ≡ d` and `e' ≡ e (mod m')`. By the same fact it then factors through one
  orbit `Θ` on which all three generators are 3-cycles.
- Then `Alt(Θ) ≅ A_7`, so `|Θ| = 7`, and the isomorphism is induced by a bijection
  `f: Θ → Ω`, since `Aut(A_7) = S_7`.
- Transport the chain. `supp(a_0) ∩ supp(a_d)` is one point `P`, with `f(P) = y+2`.
  `supp(a_0) ∩ supp(a_e)` is one point `(0 1 2)(P)`, because `(y, y+1, y+2)` sends `y+2`
  to `y`.
- A 3-cycle `(c, c+1, c+2)` meets `{0,1,2}` in one point only when `c ≡ ±2`, and the
  point is then `2` or `0`. Since `(0 1 2)(0) = 1` is not an end point, `P = 2`. So
  `d' ≡ 2` and `e' ≡ −2 (mod m')`.

Then `m' | gcd(d−2, e+2) = 1`, a contradiction. So some word in `a_0, a_d, a_e` is trivial
in `Γ` but not in the fake action. Hence `Γ_K ≠ Γ` for every `K`. ∎

## What the failure says

`W_K`-relations and the scaling relation are local, and a sparse doubling orbit carries
many copies of the local picture. Only a long relation can see that the copies are
arranged differently from the one cluster at the fixed point `0` of an honest
coordinate. The same proof works for `x ↦ Nx` with any `N ≥ 2`, using `m = N^r − 1`. It
also works after adding `x ↦ −x`, since `O = ±2^i y_0` is still small and sparse.

For all odd degrees, the only integer multipliers invertible modulo every coordinate are
`±2^k`. So **no host of the form ⟨α, β, affine maps of Z/m⟩ over Neumann's full degree
set is finitely presented.** A host for Neumann's exact group must act on coordinate sets
larger than `Z/m`, or use non-affine generators.

## Lesson for general BH

**Fake-action test for candidate hosts.** A group `Γ` given by generators acting on a
family of honest sets is finitely presented iff, for some `R`, every action whose
`R`-balls look like honest ones is honest. For a host of the form ⟨finitary element,
dynamical group `H`⟩:
- every sparse periodic orbit of `H` on a finite quotient carries a locally honest,
  globally fake action, with one copy of the finitary element on each orbit point;
- the scaling relations and local Alt-relations are blind to how many copies there are.

So hosts whose finite quotients have many small `H`-invariant sparse sets (affine,
Baumslag–Solitar-type, one multiplier) are never finitely presented. Thompson-type fp
simple hosts escape because elements with small support can move one copy
independently of the others. A residually finite host cannot do that inside the finite
coordinates. Use the test as a quick non-fp certificate before writing presentations.
