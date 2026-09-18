---
rg: 2
id: bernoulli-full-shift-conjugacies-are-base-relabelings-proof
kind: route
title: Transport the homoclinic Radon-Nikodym cocycle and prove a Livsic lemma by counting pattern occurrences
target: bernoulli-full-shift-conjugacies-are-base-relabelings
requires: []
---

**Conventions.** `G` is a countable group acting by `(gx)_h = x_(g^-1 h)`, so
`(h^-1 x)_e = x_h`. Write `μ = λ^G` and `ν = κ^G`, both of full support. The homoclinic
relation `Δ_A` pairs configurations that differ in finitely many coordinates.

## Part 0. Reduction of (b) to (a)

Assume (b). Fix `h` and let `q(x) = φ(x)_h`. Changing `x` at a coordinate `g` changes
`φ(x)` only inside `gF`. So `q` is a.e. invariant under single-coordinate changes at every
`g ∉ K := hF^-1`, and hence under finite changes outside `K`.
- Write `x = (x_K, x')` with `x' ∈ A^(G∖K)`.
- By Fubini, for a.e. `x_K` the function `x' ↦ q(x_K, x')` is invariant under finite
  changes.
- By the Hewitt–Savage/Kolmogorov 0–1 law for the product measure on `A^(G∖K)`, it is
  a.e. constant.
So `q` is a.e. a function of `x_K`, and `φ` agrees a.e. with the cellular automaton of window
`K`. The same holds for `φ^-1`, so (a) holds.

## Part 1. A topological conjugacy that transports the cocycle

**Step 1 (conjugacy).**
- Let `Φ` and `Ψ` be the cellular automata agreeing a.e. with `φ` and `φ^-1`.
- The set `{x : ΨΦx = x}` is closed, since both maps are continuous. It has full `μ`-measure,
  and `μ` has full support, so it is dense and hence everything. Likewise `ΦΨ = id`.
- So `Φ` is a `G`-equivariant homeomorphism, and `Φ_* μ = ν`.
- It maps `G`-fixed points bijectively. These are exactly the constant configurations, so
  `|A| = |B|`, and `Φ(a^G) = π(a)^G` defines a bijection `π`.

**Step 2 (Φ preserves Δ).** Let `Φ` have window `N` and `Ψ` window `N'`.
- A change of `x` inside a finite set `K` changes `Φx` only inside `KN^-1`.
- The same holds for `Ψ` with `N'`.
- So `Φ × Φ` maps `Δ_A` onto `Δ_B`.

**Step 3 (cocycle transport).** For `(x,y) ∈ Δ_A`, let
`c_μ(x,y) = Π_g λ(y_g)/λ(x_g)`, a finite product. We claim that
`c_ν(Φx, Φy) = c_μ(x,y)` for every `(x,y) ∈ Δ_A`.

- Every such `y` is `T x`, where `T = T_(K,p,q)` exchanges two patterns `p, q ∈ A^K` on a finite
  set `K` and is the identity off `K`.
- `T` is a homeomorphism, and `d(μ∘T)/dμ (x) = c_μ(x, Tx)`.
- The homeomorphism `S = Φ T Φ^-1` moves points only inside the finite set `L = K N^-1`.
  Its restriction to `L` depends on `z` only through a finite window. That window is the
  union of `K N'^-1` (which decides whether `T` acts) and `L N N'^-1`.
- So on each cylinder of that window, `S` is a fixed injective recoding of the pattern on `L`.
  It exchanges patterns within a finite orbit. There,
  `d(ν∘S)/dν (z) = c_ν(z, Sz)`, and this is locally constant in `z`.
- Also `ν∘S = Φ_*(μ∘T)`, so `d(ν∘S)/dν (z) = c_μ(Φ^-1 z, T Φ^-1 z)`. This is also locally
  constant in `z`.
- The two derivatives agree ν-a.e. Both are locally constant and `ν` has full support, so
  they agree everywhere. Put `z = Φx`.

**Step 4 (potential with vanishing homoclinic sums).**
- Let `u_λ(x) = log λ(x_e)` and `u_κ(z) = log κ(z_e)`. Then
  `log c_μ(x,y) = Σ_(h∈G) [u_λ(h^-1 y) − u_λ(h^-1 x)]`, a finite sum.
- By equivariance, `h^-1 Φ = Φ h^-1`. Step 3 then says that the locally constant function
  `f = u_κ∘Φ − u_λ`, which depends only on `x|_(N ∪ {e})`, satisfies
  `Σ_(h∈G) [f(h^-1 y) − f(h^-1 x)] = 0` for all `(x,y) ∈ Δ_A`.
- Each sum is finite: its terms vanish unless `h(N ∪ {e})` meets the set where `x` and `y`
  differ.

## Part 2. Livšic lemma over every group

**Lemma.** Let `f: A^G → R` depend only on coordinates in a finite set `E`, with vanishing
homoclinic sums. Then `f = c + Σ_i (g_i∘s_i^-1 − g_i)` for a constant `c`, finitely many
locally constant `g_i`, and elements `s_i ∈ G`. Consequently `∫ f dm = c` for every
`G`-invariant probability measure `m`.

*Proof.* Fix a rest letter `o ∈ A`.
- **Basis.** For a finite `S ⊂ G` and a pattern `p: S → A∖{o}`, let `δ_(S,p)(x) = [x|_S = p]`,
  with `δ_(∅,∅) = 1`. The `δ_(S,p)` with `S ⊆ E` form a basis of the functions of `x|_E`.
  - They span, since `[x_g = o] = 1 − Σ_(a≠o) [x_g = a]`.
  - There are `Σ_(S⊆E) (|A|−1)^|S| = |A|^|E|` of them.
- **Group action.** `δ_(S,p)(h^-1 x) = δ_(hS, hp)(x)`, where `(hp)(hs) = p(s)`. So `G` permutes
  the index pairs. Write `f = Σ f_(S,p) δ_(S,p)`, and for an orbit `O` of nonempty pairs let
  `W(O) = Σ_((S,p)∈O, S⊆E) f_(S,p)`.
- **Stabilizers.** For `(S,p) ∈ O`, `Σ_h δ_(h(S,p))(y) = |Stab_O| · occ_O(y)`.
  - Here `occ_O(y)` is the number of pairs in `O` that occur in `y` (`y|_(S') = p'`).
  - `Stab_O` is finite, since `hS = S` forces `h ∈ S s_0^-1`.
- **Occurrence counts.** Let `y` be finitely supported: it equals `o` off a finite set `T`,
  and is non-`o` on `T`, with pattern `q`. For the pair `(o^G, y)`:
  - the constant term cancels;
  - every nonempty `δ_(S,p)` vanishes at `o^G`, since `p` avoids `o`;
  - so the homoclinic sum equals `Σ_O W(O) |Stab_O| occ_O(y)`.
- **Induction on `|T|`.** Let `O_0` be the orbit of `(T,q)`.
  - Every pair occurring in `y` has `S' ⊆ T`.
  - The only pair of size `|T|` occurring in `y` is `(T,q)`, so `occ_(O_0)(y) = 1`.
  - Suppose `W(O) = 0` for all orbits of size `< |T|`. Then the vanishing sum gives
    `W(O_0)|Stab_(O_0)| = 0`, so `W(O_0) = 0`.
  - The base case `|T| = 1` is the same computation.
- **Conclusion.** Every orbit sum vanishes. Choose a representative `r_O` in each of the finitely
  many orbits that meet `E`. For `(S,p) = h r_O` we have
  `δ_(S,p) − δ_(r_O) = δ_(r_O)∘h^-1 − δ_(r_O)`. So
  `f − f_(∅,∅) = Σ_O Σ_((S,p)∈O) f_(S,p) (δ_(S,p) − δ_(r_O))` is a finite sum of coboundaries,
  and `c = f_(∅,∅)`. Coboundaries integrate to 0 against invariant measures. ∎

## Part 3. Pinning the constant at the fixed points

Apply the lemma to `f = u_κ∘Φ − u_λ` from Step 4.
- **With `m = μ`.** `∫ u_κ∘Φ dμ = ∫ u_κ dν = −H(κ)` and `∫ u_λ dμ = −H(λ)`, so
  `c = H(λ) − H(κ)`.
- **With `m = δ_(a^G)`**, which is invariant. `f(a^G) = log κ(π(a)) − log λ(a)`, so
  `κ(π(a)) = e^c λ(a)` for every `a`.
- **Summing over `a`.** Summing over `a ∈ A` and using that `π` is a bijection gives `1 = e^c`.
  So `c = 0`, `κ∘π = λ` and `H(λ) = H(κ)`. ∎

## Remarks

- **Calibration on `Z`.** The finitary isomorphism between the Meshalkin bases
  `(1/2, 1/8^4)` and `u_4` is not a relabeling. It is consistent with the claim because it is
  not continuous in either direction.
  - It also cannot preserve `Δ`. A `Δ`-preserving measure isomorphism transports the
    Radon–Nikodym cocycle, since that cocycle is intrinsic to the measured relation.
  - The cocycle of the first base takes the value `4` on a set of positive measure. The
    cocycle of `u_4` is identically `1`.
- **Exact failing step for measurable isomorphisms.** Part 3 evaluates `f` at the fixed
  points `a^G`, which are `μ`-null. For a measurable `f` with vanishing homoclinic sums,
  Part 2 has no analogue: constants have vanishing sums, and the cocycle does not see the
  constant `H(λ) − H(κ)`.
- **Scope.**
  - The argument needs both directions continuous. Step 1 needs this for the constants,
    and Step 3 for local constancy.
  - A one-sided version: an injective cellular automaton factor map carrying `λ^G` to `κ^G`
    gives `κ(π(a)) = e^(H(λ)−H(κ)) λ(a)` on constants. For the uniform bases `u_2` and
    `u_3` this identity is vacuous, so the one-sided form does not decide the `2`-versus-`3`
    question.
