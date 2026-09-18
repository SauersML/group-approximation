---
rg: 2
id: leavitt-copy-centralizing-units-are-self-doubling
kind: claim
title: A Leavitt unit commutes with a unital copy of the Leavitt algebra exactly when it is conjugate to its own double, and doubling kills every additive invariant
distinct_from:
  leavitt-unit-commuting-with-a-leavitt-copy-gives-q-in-units: that turns one commuting unital copy of L into (Q,+) ⊂ L^×; this characterizes when such a copy exists (t conjugate to t ⊕ t) and proves the invariants that obstruct it, excluding every Thompson unit in characteristic 0 and every aperiodic Thompson unit over any field.
  leavitt-unit-centralizers-have-finite-rank: that OPEN conjecture forbids infinite centralizer rank; this shows (Q,+) ⊂ L^× already forces infinite rank, so the conjecture kills the whole finite-field Leavitt route to GL_n(Q), not only the commuting-copy mechanism.
  unit-group-is-automorphisms-of-a-self-doubling-module: that is the module M = M ⊕ M behind L^× = Aut(M); this is about ELEMENTS t with t ≅ t ⊕ t, which is much rarer.
---

**ESTABLISHED** (lane proof, bh-gln-centralizer, elementary; not reviewed; no priority claimed).

**Setting.** `F` is a field, `L = L_F(1,2)` with `y_i x_j = δ_ij`, `x_0 y_0 + x_1 y_1 = 1`, and
`Ψ(a) = x_0 a y_0 + x_1 a y_1`, the diagonal ("doubling") endomorphism. Under `L ≅ M_2(L)`,
`Ψ(a) = diag(a, a) = a ⊕ a`. "Copy of `L`" means a unital `F`-subalgebra `D ≅ L`; for `F = F_p` any unital
subring `≅ L` qualifies, since ring maps are then `F_p`-linear.

## Theorem 1 (commuting with a copy = self-doubling)

For `t ∈ L` the following are equivalent:
1. `t` commutes elementwise with a unital copy `D` of `L`;
2. `t = u Ψ(t) u^(-1)` for some `u ∈ L^×`, i.e. `t` is conjugate to its own double.

More precisely, unital endomorphisms of `L` are exactly `φ_u : x_i ↦ u x_i, y_i ↦ y_i u^(-1)`, one for each `u ∈ L^×`.
They are all injective, since `L` is simple. For each of them, `φ_u(L)' ∩ L = Fix(Ad(u)∘Ψ)`.

*Proof.* Let `φ` be unital with `X_i = φ(x_i)`, `Y_i = φ(y_i)`, and put `u = Σ_i X_i y_i`, `u' = Σ_i x_i Y_i`.
Then `u u' = Σ_i X_i Y_i = 1 = Σ_i x_i y_i = u' u`, while `u x_i = X_i` and `y_i u' = Y_i`, so `φ = φ_u`.
Conversely, every `u ∈ L^×` gives a Leavitt pair `u x_i`, `y_i u^(-1)`.
- *If `a` commutes with `D = φ_u(L)`:* then `a = a Σ X_i Y_i = Σ X_i a Y_i = u Ψ(a) u^(-1)`.
- *If `a = u Ψ(a) u^(-1)`:* then `a X_j = u Ψ(a) x_j = u x_j a = X_j a`, and similarly `Y_j a = a Y_j`. ∎

## Theorem 2 (doubling kills additive invariants)

Let `t = u Ψ(t) u^(-1)`.
- **(a) Traces.** Every trace `τ : L → F` vanishes on `F[t^(±1)]`. Indeed
  `τ(Ψ(a)) = Σ τ(y_i x_i a) = 2τ(a)` and `τ` is conjugation-invariant, so `τ(p(t)) = 2τ(p(t))`, in every
  characteristic.
- **(b) Modules.** For every left `L`-module `M`, write `M_t` for `M` as an `F[z^(±1)]`-module with `z` acting
  by `t`. Then `M_t ≅ M_t ⊕ M_t`.
  - `M = x_0 M ⊕ x_1 M`, and `x_i : M → x_i M` intertwines `a` with `Ψ(a)`, so `M_(Ψ(t)) ≅ M_t ⊕ M_t`.
  - The unit `u` gives `M_t ≅ M_(Ψ(t))`.
  - So every additive isomorphism invariant of `F[z^(±1)]`-modules that is finite on `M_t` vanishes on it.

## Lemma 3 (Lefschetz traces count hyperbolic fixed points)

Use `L ≅ A_F(𝒢_2)`, the Steinberg algebra of the Cuntz groupoid `𝒢_2 = {(αw, |α|−|β|, βw)}`
(Clark–Farthing–Sims–Tomforde). The monomial `x_α y_β` is the indicator of the bisection
`Z(α,β) = {(αw, |α|−|β|, βw)}`.
- **The trace.** Fix an orbit `O` of eventually periodic points, the tail class of `ρ^∞` with `ρ` primitive, and
  a lag `n ≠ 0`. Put `τ_(O,n)(f) = Σ f(g)`, summed over isotropy arrows `g = (z, n, z)` with `z ∈ O`.
- **Finite and linear.** `Z(α,β)` contains at most one isotropy arrow: `αw = βw` forces `α = βρ` and
  `w = ρ^∞`, or the reverse.
- **Trace property.** In `τ(f*h)` the pairs `g_1 g_2 = g` correspond bijectively to pairs `(g_2, g_1)` with
  `g_2 g_1 = g_1^(-1) g g_1`. That is an isotropy arrow with the same lag at a point of the same orbit.
- **On Thompson units.** For `g ∈ V ⊂ L^×`, the indicator of the germ bisection of `g`, `τ_(O,n)(g)` is the
  number of fixed points `z ∈ O` at which `g` has contracting (`n > 0`) or expanding (`n < 0`) germ of lag
  `n`, i.e. hyperbolic fixed points counted by type. Fixed points where `g` is locally the identity have
  lag 0 and are not counted.

## Theorem 4 (Thompson units are never self-doubling)

Let `g ∈ V ⊂ L_F(1,2)^×` have infinite order.
- **(a)** If `char F = 0`, then `g` commutes with no unital copy of `L`.
- **(b)** For every `F`: if no power of `g` is the identity on a nonempty clopen set ("aperiodic" `g`), then `g`
  commutes with no unital copy of `L`.
- **(c)** For `char F = p`: the same holds as soon as, for some `m`, some type `(O, n)` carries a number of
  hyperbolic fixed points of `g^m` not divisible by `p`.

*Inputs.* The dynamics of `V` (Brin; Salazar-Díaz, *Thompson's group V from a dynamical viewpoint*; recalled,
not re-read). An infinite-order `g` has an attracting periodic orbit. For aperiodic `g`, `Per(g)` is finite
and every forward orbit accumulates on a periodic orbit.

*Proof.*
- **(a) and (c).** Let `P` be an attracting orbit of period `m`. Then `g^m` fixes a point of `P` with
  contracting germ, so `τ_(O,n)(g^m) ∈ Z_(≥1)` for its type. In characteristic 0 this contradicts Theorem 2(a);
  (c) is the same count mod `p`.
- **(b), step 1: the Cantor module.** Take `M = W = LC(C, F)`, locally constant functions on Cantor space, with
  `(x_i f)(w) = [w_1 = i] f(σ w)` and `(y_i f)(w) = f(iw)`. This is a faithful `L`-module, and `g` acts through
  its homeomorphism.
- **Step 2: torsion is fixed by a power.** Let `S` be a finite-dimensional `g`-invariant subspace. The finitely
  many joint level sets of `S` form a clopen partition that `g` permutes, so some `g^k` is trivial on `S`.
  Hence the torsion submodule `T(W_g)` is `∪_k ker(g^k − 1)`.
- **Step 3: torsion is finite and nonzero.** A `g^k`-invariant locally constant function is constant on the atoms
  of the finest `g^k`-invariant clopen partition. Each atom is closed and invariant, so it contains a periodic
  point, giving `dim ker(g^k − 1) ≤ |Per(g)|` for all `k`. So `T(W_g)` is finite-dimensional, and it is nonzero
  since it contains the constants.
- **Step 4.** Theorem 2(b) gives `T(W_g) ≅ T(W_g)^2`, which is impossible. ∎

## Corollary 5 ((Q,+) in the units forces infinite centralizer rank)

Let `F` be finite and `(Q,+) ↪ L^×` with `r_k = image(1/k!)`. Then `r_1` has infinite order and
`ρ(r_1) = dim_(F(r_1)) F(r_1) ⊗ C_L(r_1) = ∞`.
- `r_k` is transcendental, so `F[r_k^(±1)]` is free of rank `k!` over `F[r_1^(±1)]`, since `r_1 = r_k^(k!)`.
- `F[r_k^(±1)] ⊆ C_L(r_1)`, and localization is exact, so `ρ(r_1) ≥ k!` for every `k`.

**So `leavitt-unit-centralizers-have-finite-rank` implies `(Q,+) ⊄ L_(F_2)(1,2)^×`.** Hence no `Aff(Q)`,
`GL_n(Q)` or `PSL_n(Q)` embeds there, and route R2 of the GL_n(Q) skeleton dies entirely, not only its
commuting-copy mechanism. By Theorem 1, that mechanism is literally "find an infinite-order self-doubling
unit", and such a unit has `ρ = ∞`.

## Attempts (toward the decisive question)

- **Where the question sits in the literature.** Existence of an infinite-order self-doubling unit over a finite
  field is equivalent to a unital embedding `L ⊗ F[u^(±1)] ↪ L` (item "Equivalent hypothesis" of
  `leavitt-unit-commuting-with-a-leavitt-copy-gives-q-in-units`). `L ⊗ F[u^(±1)]` is the Kumjian–Pask algebra
  of the 2-graph `E_2 × E_1`, so an affirmative answer to Bilich–Hazrat–Nam's Question 2.8
  (arXiv:2512.09241, Dec 2025: do Kumjian–Pask algebras embed into `L_k(1,2)`?) would give YES. They note it
  would also give `L ⊗ L ↪ L`, which is open over fields. Brownlowe–Sørensen (arXiv:1603.03618) rule out a
  unital `*`-embedding `L_(2,Z) ⊗ L_(2,Z) ↪ L_(2,Z)` using `V` inside the unitaries. That is the same phenomenon
  as Theorem 4(a). Both were read at abstract/theorem-statement level only.
- **What a witness must survive, over F_2.**
  - All Lefschetz counts of all powers even.
  - Torsion in every `L`-module either absent or of infinite multiplicity in every indecomposable type.
  - `ρ = ∞`.
- **A Thompson witness that Theorem 4 misses, killed by rank.** Take `t = x_0 y_0 + x_1 Ψ(c) y_1 ∈ V`, the
  identity on `[0]` and the doubled north–south unit `c ⊕ c` on `[1]`.
  - **It passes the trace test over `F_2`.** Every hyperbolic count of every power is even.
  - **It passes the torsion test on the Cantor module.** `LC([0])` supplies infinitely many trivial summands,
    which absorb the two constants of the `[1]` part.
  - **So Theorem 4 does not reach it over `F_2`.**
  - **But its rank is finite.** With `e = x_0 y_0`, the Peirce blocks `eCe`, `eC(1−e)` and `(1−e)Ce` of
    `C_L(t)` are all killed by `t − 1`. So `ρ(t) = ρ_L(Ψ(c)) = 4 < ∞`, using the corner isomorphism
    `a ↦ y_1 a x_1` and the diagonal-copy value recorded on `leavitt-heisenberg-centers-have-infinite-centralizer-rank`.
  - **Hence `t` is not self-doubling.** The three tests are genuinely different.
- **Status.** The YES/NO question is not decided. The first obstruction is combinatorial dynamics, and in
  characteristic 0 it kills every Thompson unit. A YES needs a genuinely linear unit with no Lefschetz numbers
  and no finite torsion anywhere.

## Lesson for general BH

"Commutes with a unital copy of the host" is the same as "self-doubling" (`t ≅ t ⊕ t`). That is the algebraic
shadow of the absorption `O_2 ⊗ O_2 ≅ O_2`, which is exactly what fails algebraically. Doubling multiplies every
additive invariant by 2, so self-doubling elements must be invariant-free: Lefschetz traces (hyperbolic
fixed-point counts), finite torsion in any module, and centralizer rank. Combinatorial (Thompson-type) elements
always carry Lefschetz numbers, so absorption mechanisms can never be fed by them in characteristic 0. For
GL_n(Q), infinite divisibility inside a Leavitt unit group is the same obstacle: it forces infinite centralizer
rank. The whole finite-field Leavitt route is therefore one question: does an invariant-free unit exist?
