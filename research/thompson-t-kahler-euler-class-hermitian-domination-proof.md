---
rg: 2
id: thompson-t-kahler-euler-class-hermitian-domination-proof
kind: route
target: thompson-t-kahler-euler-class-is-a-hermitian-domination-problem
title: "Proof that (K) for Thompson's T is equivalent to Hermitian domination of the displacement kernel, that every finite section is feasible, and that no bounded witness exists"
requires: []
artifacts: []
---

The notation is that of the target claim. The one input from the graph is Step 3 of
`integrably-paired-cup-products-exact-proof`:

- `u_{fg} = u_f∘g̃ + u_g`;
- `ω(φ∘g̃, ψ∘g̃) = ω(φ, ψ)`;
- `ω(u_f∘g̃, u_g) = −D(f, g)`, with `e_R = [D]` and `|D| < 1`.

Inner products are conjugate-linear in the first slot. (K) is invariant under this choice, because
passing to the conjugate representation `(π̄, b̄)` negates `Im⟨b(g), π(g)b(h)⟩`.

## Step 0. Conventions and bounds

**0.1 The form is well defined.** `ω` kills constants in both slots:

- `∫_0^1 c dψ = c(ψ(1) − ψ(0)) = 0`, by periodicity;
- `∫ φ d(c) = 0`.

So `ω` is defined on `W`. It is skew, since `∫_0^1 φ dψ + ∫_0^1 ψ dφ = [φψ]_0^1 = 0`.

**0.2 The action preserves ω.** The action `g·φ = φ∘g̃^{-1}` does not depend on the lift, since
the lifts differ by integer translations and `φ` is periodic. It preserves `ω` by Step 3.4, applied
with `g̃^{-1}`.

**0.3 v is a left cocycle.** `u_{h^{-1}g^{-1}} = u_{h^{-1}}∘g̃^{-1} + u_{g^{-1}}`, which says
`v_{gh} = g·v_h + v_g`.

**0.4 The sign of the area cocycle.** Put `κ_v(g, h) := ω(v_g, g·v_h)`. We claim `κ_v = −D`.

- From `u_1 = 0` and the cocycle rule, `u_{g^{-1}}∘g̃ = −u_g` and `u_{h^{-1}} = −u_h∘h̃^{-1}`.
- By invariance, `κ_v(g,h) = ω(u_{g^{-1}}∘g̃, u_{h^{-1}}) = −ω(u_g, u_{h^{-1}})`.
- Next, `−ω(u_g, u_{h^{-1}}) = ω(u_g, u_h∘h̃^{-1}) = ω(u_g∘h̃, u_h) = −D(g, h)`.

So `[κ_v] = −e_R`.

**0.5 Bound.** `|Ω| ≤ 1`, so in particular `|Ω| < 2`. Each `v_g` is a displacement function
`u_{g^{-1}}`.

- By Step 3 its oscillation is `< 1`, so a representative `φ` satisfies `|φ − m| ≤ ½` for a
  constant `m`.
- The total variation of `ψ = k̃^{-1} − id` over one period is at most
  `∫_0^1 ((k̃^{-1})' + 1) = 2`.
- Hence `|ω(φ, ψ)| = |ω(φ − m, ψ)| ≤ ½ · 2 = 1`.

**0.6 Symmetries.** A cnd function is real and symmetric, `ψ(g^{-1}) = ψ(g)`. So `G_ψ` is real
symmetric. `Ω` is real skew by 0.1. When `f` is odd, `∂f` is real skew:
`∂f(k, g) = f(k) + f(k^{-1}g) − f(g) = −(f(g) + f(g^{-1}k) − f(k))`.

Hence `H_{ψ,f} = G_ψ + i(Ω + ∂f)` is a Hermitian kernel.

## Step 1. Algebraic identities

**1.1** `Ω(g, gh) = κ_v(g, h)`. Indeed `v_{gh} = v_g + g·v_h` and `ω(v_g, v_g) = 0`.

**1.2** `∂f(g, gh) = f(g) + f(h) − f(gh) = δf(g, h)`.

**1.3 Invariance under the affine action.** For a kernel `K`, write
`(a⋆K)(g,k) := K(ag, ak) − K(ag, a) − K(a, ak) + K(a, a)`. This is the value of `K` on the pair
`(δ_{ag} − δ_a, δ_{ak} − δ_a)`. We claim `a⋆K = K` for `K = G_ψ`, `Ω` and `∂f`, under the
hypotheses of (A2).

- *`G_ψ`, for ψ symmetric with ψ(1) = 0.* `G(a,a) = ψ(a)`. Expand the four terms. The `ψ(ag)`,
  `ψ(ak)` and `ψ(a)` contributions cancel, which leaves
  `½(ψ(g^{-1}) + ψ(k) − ψ(g^{-1}k)) = G_ψ(g, k)`.
- *`Ω`.* Write `v_{ag} = v_a + a·v_g` and `v_{ak} = v_a + a·v_k`. Then
  - `Ω(ag, ak) = ω(v_a, a·v_k) + ω(a·v_g, v_a) + ω(a·v_g, a·v_k)`;
  - `Ω(ag, a) = ω(a·v_g, v_a)`;
  - `Ω(a, ak) = ω(v_a, a·v_k)`;
  - `Ω(a, a) = 0`.

  So `a⋆Ω = ω(a·v_g, a·v_k) = Ω(g, k)`, by 0.2.
- *`∂f`, for f odd with f(1) = 0.* Here
  - `∂f(ag,ak) = f(ag) + f(g^{-1}k) − f(ak)`;
  - `∂f(ag,a) = f(ag) + f(g^{-1}) − f(a)`;
  - `∂f(a,ak) = f(a) + f(k) − f(ak)`;
  - `∂f(a,a) = f(1)`.

  So `a⋆∂f = f(g^{-1}k) − f(g^{-1}) − f(k) + f(1)`. This equals
  `∂f(g,k) − (f(g) + f(g^{-1}) − f(1)) = ∂f(g, k)`.

**1.4 Row at 1.** `G_ψ(1, k) = ½(ψ(1) + ψ(k) − ψ(k)) = 0`, `Ω(1, k) = 0` (`v_1 = 0`) and
`∂f(1, k) = f(1) = 0`. So `H_{ψ,f}(1, ·) = 0`, and likewise the column at 1.

## Step 2. (A2) ⇒ (A1): the universal witness

Let `H = H_{ψ,f} ⪰ 0`. Put `⟨c, c'⟩_H := Σ c̄(g) H(g,k) c'(k)` on `c_c(T)`. Let `𝓗` be the
Hilbert completion of `c_c(T)` modulo the null vectors. `T` is countable, so `𝓗` is separable.

**2.1 The representation.** Define `π_0(a)` on `c_c(T)` by linear extension of
`π_0(a)δ_g := δ_{ag} − δ_a`.

- *It is an action.* `π_0(b)π_0(a)δ_g = δ_{bag} − δ_b − (δ_{ba} − δ_b) = δ_{bag} − δ_{ba}`, which
  is `π_0(ba)δ_g`. Also `π_0(1) = id`.
- *It preserves the form.* By 1.3, `⟨π_0(a)δ_g, π_0(a)δ_k⟩_H = (a⋆H)(g,k) = H(g,k)`. So `π_0(a)`
  preserves null vectors and is isometric.
- *It is unitary.* `π_0(a)` has inverse `π_0(a^{-1})`, so it extends to a unitary `π(a)` of `𝓗`.

Note `π_0(a)δ_1 = 0`, which is consistent with 1.4: `δ_1` is null.

**2.2 The cocycle.** `b(g) := [δ_g]`. Then
`π(g)b(h) + b(g) = [δ_{gh} − δ_g + δ_g] = b(gh)`.

**2.3 The area class.** Using 1.1 and 1.2,
`Im⟨b(g), π(g)b(h)⟩ = Im H(g, gh) − Im H(g, g) = κ_v(g,h) + δf(g,h) − 0`.

Here `Im H(g,g) = Ω(g,g) + ∂f(g,g) = f(g) + f(1) − f(g) = 0`. By 0.4 the area cocycle is
`−D + δf`, with class `−e_R`. The conjugate witness `(π̄, b̄)` has class `e_R`, which is (K).
This is the universal witness stated in (A).

## Step 3. (A1) ⇒ (A2)

Let `(π, b)` witness (K). Replace it by its conjugate, so that `[Im⟨b(g), π(g)b(h)⟩] = −e_R`.

**3.1 The correction f.** There is `f : T → R` with
`Im⟨b(g), π(g)b(h)⟩ = −D(g,h) + δf(g,h)`, where `δf(g,h) = f(g) + f(h) − f(gh)`. Here
`H²(T; R)` is ordinary group cohomology, so `f` is arbitrary and possibly unbounded.

`f` is unique: two choices differ by a homomorphism `T → R`, and `T` is simple, hence perfect.

**3.2 The unknowns.** Put `ψ(g) := ‖b(g)‖²`. It is cnd with `ψ(1) = 0`, a standard property of
`‖b‖²` for a 1-cocycle. The cocycle identity `b(k) = b(g) + π(g)b(g^{-1}k)` gives two facts.

- **Real part.** `‖b(k) − b(g)‖² = ψ(g^{-1}k)`, so polarization gives
  `Re⟨b(g), b(k)⟩ = G_ψ(g, k)`.
- **Imaginary part.**
  `Im⟨b(g), b(k)⟩ = Im⟨b(g), π(g)b(g^{-1}k)⟩ = −D(g, g^{-1}k) + δf(g, g^{-1}k)`.
  - By 0.4 and 1.1, `−D(g, g^{-1}k) = κ_v(g, g^{-1}k) = Ω(g, k)`.
  - And `δf(g, g^{-1}k) = f(g) + f(g^{-1}k) − f(k) = ∂f(g,k)`.
  - So `Im⟨b(g), b(k)⟩ = Ω(g,k) + ∂f(g,k)`.

**3.3 Normalizing f.** Take `k = 1` in the last identity. Since `b(1) = 0` and `Ω(g, 1) = 0`, we
get `0 = f(g) + f(g^{-1}) − f(1)`. Then `g = 1` gives `f(1) = 0`, so `f` is odd.

**3.4 Positivity.** Hence `H_{ψ,f}(g,k) = ⟨b(g), b(k)⟩` is a Gram kernel, so it is positive
semidefinite. This gives (A2), with the `ψ` and `f` stated in (A).

## Step 4. (A2) ⟺ (A3)

Write `B := i(Ω + ∂f)`. It is Hermitian with purely imaginary entries, and `G := G_ψ` is real
symmetric. For `c ∈ c_c(T)` both `⟨c, Gc⟩` and `⟨c, Bc⟩` are real, and conjugating gives
`⟨c̄, (G − B) c̄⟩ = conj⟨c, (G + B)c⟩ = ⟨c, (G + B)c⟩`.

- So `G + B ⪰ 0` iff `G − B ⪰ 0`.
- Both hold iff `⟨c, Gc⟩ ≥ ±⟨c, Bc⟩` for all `c`, i.e. iff `⟨c,Gc⟩ ≥ |⟨c,Bc⟩|`.
- Finally `|⟨c, Bc⟩| = |⟨c, (Ω + ∂f)c⟩|`.

This is (A3).

## Step 5. (B): every finite section is feasible

**5.1 The comparison function.** Let `ψ_reg(g) := 2·1_{g ≠ 1}`. It is `‖β(g)‖²` for the cocycle
`β(g) = δ_g − δ_1` of the left regular representation, since
`λ(g)β(h) + β(g) = δ_{gh} − δ_1`. So it is cnd with `ψ_reg(1) = 0`.

For `g, k ≠ 1`, `G_{ψ_reg}(g,k) = Re⟨β(g), β(k)⟩ = 1_{g=k} + 1`. So on `E' := E ∖ {1}`,
`G_{Cψ_reg} = C(I + J) ⪰ C·I`, where `J` is the all-ones matrix.

**5.2 The estimate.** Take `f = 0`. By 1.4, every entry of `H_{Cψ_reg, 0}` in the row or column of
`1` vanishes, so it suffices to test `c` supported on `E'`. By 0.5,
`|⟨c, Ωc⟩| ≤ Σ |c(g)||c(k)| = ‖c‖_1² ≤ |E| ‖c‖_2²`.
With `C ≥ 2|E|`, this is `≤ C‖c‖_2² ≤ ⟨c, G_{Cψ_reg} c⟩`. So (A3) holds on `E × E`, and by Step 4
the kernel `H` is positive semidefinite on `E × E`.

The constant in (B) was stated with the cruder bound `|Ω| < 2`, which still suffices.

**5.3 Consequence.** Any finite obstruction is a finite set `E` on which no admissible `(ψ, f)` is
positive. This covers:

- a dual SDP certificate on `E × E`;
- a finite list of relators;
- a finite-radius ball in a Cayley graph.

No such obstruction exists, even with `f = 0` fixed. Every refutation must therefore be global: it
must use infinitely many group elements at once, against unbounded `ψ`.

## Step 6. (C): no bounded witness, and unboundedness of the displacement form

This step uses `e_R ≠ 0`. That fact is recalled from Ghys–Sergiescu, as in
`cup-products-of-integrably-paired-potential-cocycles-are-exact`, and is not re-verified here.

Steps 0–5, and hence (A) and (B), do not use it.

**6.1 No pair in (A2) has ψ bounded.** Suppose `H_{ψ,f} ⪰ 0` with `sup ψ < ∞`.

- *The cocycle is bounded.* Take the universal witness of Step 2. Then
  `‖b(g)‖² = H(g,g) = G_ψ(g,g) = ψ(g)`, so `b` is bounded.
- *So it is a coboundary.* The affine orbit `{b(g)}` of `0` is bounded, and its circumcenter `w` is
  fixed by the affine action. Hence `b(g) = w − π(g)w`.
- *The area cocycle is then a coboundary.* Expanding,
  `⟨w − π(g)w, π(g)w − π(gh)w⟩ = ⟨w, π(g)w⟩ − ‖w‖² − ⟨w, π(gh)w⟩ + ⟨w, π(h)w⟩`.
  So `Im⟨b(g), π(g)b(h)⟩ = F(g) + F(h) − F(gh) = δF(g,h)`, with `F(g) = Im⟨w, π(g)w⟩`.
- *Contradiction.* By 2.3, `−D + δf = δF`. Hence `e_R = [D] = [δ(f − F)] = 0`, which is false.

**6.2 The form is unbounded for every odd f.** Fix `f` odd with `f(1) = 0`. Suppose
`|⟨c, (Ω + ∂f)c⟩| ≤ M‖c‖_2²` for all `c ∈ c_c(T)`. Take `ψ = (M/2 + 1)·ψ_reg`, which is bounded.

- By 1.4 the rows at `1` vanish.
- By 5.1, `⟨c, G_ψ c⟩ ≥ (M/2 + 1)·2‖c‖² ≥ M‖c‖²` for `c` supported off `1`.

So (A3) holds for `(ψ, f)`. By Step 4, (A2) holds with `ψ` bounded, which contradicts 6.1. Hence
the Hermitian form `c ↦ ⟨c, i(Ω + ∂f)c⟩` is unbounded on the unit ball of `ℓ²(T)`, for every odd
`f` with `f(1) = 0`.

**6.3 Reading.** Take `f = 0`. The bounded kernel `Ω`, with `|Ω| ≤ 1`, is not the matrix of a
bounded operator on `ℓ²(T)`. No odd correction `f` can make it bounded either.

Any `ψ` that works must therefore grow. Its Gram kernel must dominate an unbounded form, one that
concentrates on vectors escaping to infinity. This is the precise content of "the Euler class is
not a bounded-cocycle phenomenon on Hilbert space". The class `e_R` is itself bounded, since
`|D| < 1`.

## Step 7. Generality

Steps 1–5 used only four things:

- a group `Γ`;
- a `Γ`-module `W` with an invariant skew form `ω`;
- a 1-cocycle `v : Γ → W`;
- for (B), a uniform bound on `ω(v_g, v_k)`.

Step 6 used in addition that the area class `[κ_v]` is nonzero in `H²(Γ; R)`. So for every such
datum:

- `[κ_v]` lies in the Kähler subspace iff the analogous kernel domination holds;
- a bounded area kernel makes the problem finitarily feasible.

The only input specific to `T` is Step 3 of `integrably-paired-cup-products-exact-proof`, which
identifies `[κ_v]` with `−e_R`.
