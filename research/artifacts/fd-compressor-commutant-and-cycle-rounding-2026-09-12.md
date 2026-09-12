# Genuine finite-dimensional models: commutants are free, central rounding is dead

Lane `hs-normalization-hunter`, 2026-09-12. Two results about the compressor
commutant question `kt-centralizer-normalization-hs` in *genuine* finite-dimensional
models. Both are elementary; neither refutes (CCR), and the second is a fence on a
proof mechanism, not on the statement.

Notation throughout: `Γ` a group, `t` a strict compressor (`Λ := tΓt⁻¹ ⊆ Γ`,
possibly proper), `G` any group containing `Γ` and `t`. `M_D` carries the
normalized trace `tr` (`tr 1 = 1`) and `‖x‖₂ = tr(x*x)^{1/2}`.

## 1. For genuine finite-dimensional representations the commutants coincide

**Theorem A.** Let `π : G → U(D)` be any unitary representation on a
finite-dimensional space. Then

```text
π(Λ)' = π(Γ)' ,
```

and `Ad π(t)` restricts to a `*`-automorphism of `π(Γ)'`. No property (T), no
image collapse, no congruence structure, no hypothesis on `π` at all.

*Proof.* Two lines.

* `Λ ⊆ Γ` gives `π(Λ) ⊆ π(Γ)`, and commutants reverse inclusions, so
  `π(Γ)' ⊆ π(Λ)'`.
* `π(Λ) = π(t) π(Γ) π(t)*`, hence `π(Λ)' = π(t) π(Γ)' π(t)*`. Conjugation by a
  unitary is a linear bijection of `M_D`, so `dim_C π(Λ)' = dim_C π(Γ)'`.

A containment of linear subspaces of equal finite dimension is an equality, so
`π(Λ)' = π(Γ)'`. Then `Ad π(t)(π(Γ)') = π(Λ)' = π(Γ)'`. ∎

The argument is pure dimension count. It fails in the ultraproduct precisely
because there `dim` is replaced by a trace, and `A ⊆ uAu*` with `A ≅ uAu*` is
then possible (`R ⊂ R` is the standard picture). That is the entire content of
the open problem.

### 1.1 Consequence: (CCR) for every coordinatewise genuine model

**Corollary A1.** Let `Λ ≤ Γ ≤ G` with `Λ` finitely generated with property (T),
and let `σ = ∏_𝒰 π_n : G → U(M)`, `M = ∏_𝒰 (M_{d_n}, tr)`, be a coordinatewise
ultraproduct of *genuine* finite-dimensional unitary representations of `G`.
Then `σ(Λ)' ∩ M = σ(Γ)' ∩ M`.

*Proof.* `Λ ≤ Γ` gives one containment. For the other, take
`x = (x_n) ∈ σ(Λ)' ∩ M` with `‖x‖ ≤ 1`. Fix a finite generating set `S` of `Λ`
with Kazhdan constant `κ > 0`, so that for every unitary representation `ρ` of
`Λ` on a Hilbert space `V` and every `v ∈ V`,

```text
max_{s∈S} ‖ρ(s)v − v‖ ≥ κ · dist(v, V^{ρ(Λ)}) .                (K)
```

Exact commutation `[x, σ(s)] = 0` for the finitely many `s ∈ S` means
`ε_n := max_{s∈S} ‖x_n − π_n(s)x_nπ_n(s)*‖₂ → 0` along `𝒰`. Apply (K) to the
conjugation representation `Ad(π_n|_Λ)` on `(M_{d_n}, ‖·‖₂)` and the vector `x_n`:
its fixed-point space is `π_n(Λ)'`, so

```text
dist₂(x_n, π_n(Λ)') ≤ ε_n / κ → 0 .
```

By **Theorem A**, `π_n(Λ)' = π_n(Γ)'`. Let `y_n = E_n(x_n)`, where `E_n` is the
`tr`-preserving conditional expectation of `M_{d_n}` onto the von Neumann
subalgebra `π_n(Γ)'` (averaging over `π_n(Γ)`); `E_n` is the `‖·‖₂`-orthogonal
projection onto `π_n(Γ)'` and is a contraction for `‖·‖_op`, so `‖y_n‖ ≤ 1` and
`‖x_n − y_n‖₂ = dist₂(x_n, π_n(Γ)') → 0`. Hence `y = (y_n)` defines an element of
`M` with `x = y` and `y ∈ ∏_𝒰 π_n(Γ)' ⊆ σ(Γ)' ∩ M`. ∎

**What this changes in the graph.** `ccr-for-coordinate-collapsing-models` proves
the same conclusion under the extra hypothesis of *image collapse*
`π_n(Γ) ⊆ π_n(Λ)`, and its proof spends Step 3 and the uniformity-in-`λ`
bookkeeping on converting `Γ`-conjugation into `Λ`-conjugation. Theorem A makes
that step unnecessary: the two exact commutants are equal at every coordinate for
structural reasons, so no collapse is needed and the requirement
`compressor-coset-two-point-exact` is not consumed.

In particular this closes the regime `kt-centralizer-normalization-hs` flagged as
uncharted in its 2026-08-18 honesty amendment — *"genuine coordinate chains that
SEPARATE `Λ` from `Γ` (if any exist for `G` — no congruence chain does); the
collapsing-regime proof says nothing there."* Separating genuine chains satisfy
(CCR) too, because separation of the images is irrelevant to the commutants.

### 1.2 Consequence for the hunt

Every counterexample to (CCR) is invisible coordinatewise: it must live entirely
in the excess commutant (the Alekseev–Thom OP 6.2 locus), and it cannot be
exhibited by any exact finite-dimensional model, however large. A finite-model
search for a counterexample to (CCR) *itself* is therefore futile, and the
remaining target is the approximate-coordinate regime only.

## 2. Almost-invariant central projections cannot be rounded

Theorem A says the commutant algebra is exactly compressor-invariant. It does
**not** say that individual almost-invariant projections in it are near invariant
ones. They are not, and the failure is macroscopic and dimension-free.

**Theorem B.** Let `Γ ≤ G` be the Kun–Thom Theorem E pair,
`Γ = EL_r(F_q[x_1,…,x_d])`, `G = EL_r(F_q[x_1^{±1},…,x_d^{±1}]) ⋊ SL_d(Z)`,
`r, d ≥ 3`, and let `t = E_12(1) ∈ SL_d(Z)` (so `tΓt⁻¹ = EL_r(F_q[x_1, x_1x_2, x_3,…]) ⊊ Γ`).
For every prime `m` with `q ≡ 1 (mod m)` there is a genuine finite-dimensional
unitary representation `π_m` of `G` and a projection `p_m ∈ Z(π_m(Γ)')` with

```text
‖Ad π_m(t)(p_m) − p_m‖₂ ≤ sqrt(2/m) ,
dist₂( p_m , { q ∈ Z(π_m(Γ)') : q a projection, Ad π_m(t)(q) = q } ) ≥ (1 − 1/m)/sqrt(2) .
```

So as `m → ∞` the invariance defect tends to `0` while the distance to the
invariant central projections tends to `1/sqrt 2`.

### 2.1 The model

Choose a prime `m` with `q ≡ 1 (mod m)` (Dirichlet). Put
`R_m = F_q[(Z/m)^d]`, the congruence quotient of the Laurent ring by
`x_i^m = 1`. Since `q ≡ 1 (mod m)` and `gcd(m,q) = 1`, the group algebra splits
completely,

```text
R_m ≅ ∏_{χ ∈ X} F_q ,        X := Hom((Z/m)^d, F_q^×) ≅ (Z/m)^d ,
```

so `E := EL_r(R_m) = ∏_{χ ∈ X} EL_r(F_q)`, one factor per character. The quotient
map `G ↠ Q_m := E ⋊ SL_d(Z/m)` is defined because `SL_d(Z)` permutes the `x_i^m = 1`
relations; write `S = SL_d(Z/m)`, which acts on `X` linearly and hence permutes
the factors of `E`. Both `Γ` and `tΓt⁻¹` surject onto `E` (elementary matrices
lift, and `F_q[x_1,…,x_d] ↠ R_m`), so the image of `Γ` in `Q_m` is exactly `E`.

Fix a nontrivial irreducible `ρ` of `EL_r(F_q)` (Steinberg, say) and for `ψ ∈ X`
let `W_ψ` be the irreducible representation of `E` equal to `ρ` on the `ψ`-factor
and trivial on all others. Distinct `ψ` give non-isomorphic `W_ψ` (different
support), and `s · W_ψ ≅ W_{s·ψ}` for `s ∈ S`. Fix `χ ≠ 0` and set

```text
π := Ind_E^{Q_m}( W_χ ) ,     pulled back to G .
```

### 2.2 The commutant and the compressor permutation

As an `E`-representation, `π|_E = ⊕_{s ∈ S} W_{s·χ}`, so each `W_ψ` with
`ψ ∈ S·χ` occurs with multiplicity `|Stab_S(χ)|` and no other `E`-irreducible
occurs. Hence

```text
π(Γ)' = π(E)' = ⊕_{ψ ∈ S·χ} M_k(C) ,      k = |Stab_S(χ)| ,
Z(π(Γ)') = span{ z_ψ : ψ ∈ S·χ } ≅ C^N ,  N = |S·χ| ,
```

where `z_ψ` is the `W_ψ`-isotypic projection. All the `W_ψ`, `ψ ∈ S·χ`, are
transported into one another by the (trace-preserving) action of `S`, so they have
equal dimension and

```text
tr(z_ψ) = 1/N   for every ψ ∈ S·χ .
```

Since `π(s)` carries the `ψ`-isotypic subspace onto the `(s·ψ)`-isotypic subspace,

```text
Ad π(s)(z_ψ) = z_{s·ψ} ,
```

i.e. `Ad π(t)` acts on the `N` minimal central projections exactly as `t` acts on
the orbit `S·χ ⊆ X`. **This is the whole point: the compressor acts on the center
of the commutant by a permutation, and that permutation has long cycles.**

### 2.3 The cycle structure of t

`m` is prime and `S = SL_d(Z/m)` acts transitively on `X \ {0}`, so `S·χ = X \ {0}`
and `N = m^d − 1`. With `t = E_12(1)`, `(t − 1)² = 0` on `X`, hence
`t^j − 1 = j(t − 1)`, so for `ψ ∈ X`:

* if `(t−1)ψ = 0` then `ψ` is a `t`-fixed point;
* otherwise `t^jψ = ψ` iff `m | j`, so the `t`-orbit of `ψ` has length exactly `m`.

The fixed points are `ker(t−1) \ {0}`, of size `m^{d−1} − 1`. Writing `F` for the
fixed set and `c` for the number of length-`m` cycles,

```text
|F| = m^{d−1} − 1 ,    c = (N − |F|)/m ,    c/N ≤ 1/m .
```

### 2.4 The projection and the two estimates

In each length-`m` cycle fix a cyclic order and let the *arc* be the first
`⌊m/2⌋` of its members; take nothing from the fixed points. Let `A ⊆ S·χ` be the
union of the arcs and

```text
p := Σ_{ψ ∈ A} z_ψ  ∈  Z(π(Γ)') ,      tr(p) = c⌊m/2⌋ / N .
```

**Invariance defect.** `Ad π(t)(p) = Σ_{ψ ∈ A} z_{t·ψ}`, and shifting an arc of a
cycle by one moves exactly two members (the head leaves, the successor of the tail
enters), in each of the `c` cycles. The `z_ψ` are orthogonal projections with
pairwise orthogonal ranges, so

```text
‖Ad π(t)(p) − p‖₂² = 2c/N ≤ 2/m .
```

**Distance to invariant central projections.** A projection `q ∈ Z(π(Γ)')` is a
sum `Σ_{ψ ∈ B} z_ψ`, and `Ad π(t)(q) = q` iff `B` is `t`-invariant, i.e. a union of
full cycles and fixed points. For such `B`,

```text
‖p − q‖₂² = tr(p) + tr(q) − 2 tr(pq) = tr(p) + Σ_{ψ ∈ B \ A} tr(z_ψ) − Σ_{ψ ∈ A ∩ B} tr(z_ψ) .
```

Each cycle contained in `B` contributes `⌊m/2⌋` members to `A ∩ B` and `m − ⌊m/2⌋`
to `B \ A`, so its net contribution is `(m − 2⌊m/2⌋)/N ≥ 0`; fixed points in `B`
contribute `≥ 0`; no member of `A` lies outside a cycle. Hence

```text
‖p − q‖₂² ≥ tr(p) = c⌊m/2⌋/N = (1 − |F|/N)·⌊m/2⌋/m .
```

With `m` an odd prime, `⌊m/2⌋/m = (m−1)/(2m)` and
`|F|/N = (m^{d−1}−1)/(m^d−1) < 1/m`, so

```text
‖p − q‖₂² ≥ (1 − 1/m)·(m−1)/(2m) = (1/2)(1 − 1/m)² ≥ 1/2 − 1/m ,
```

which is the stated bound `dist₂ ≥ (1 − 1/m)/sqrt 2`, tending to `1/sqrt 2`. ∎

### 2.5 Scope: what Theorem B does and does not kill

* It **does not** refute (CCR) or normalization. By Theorem A the algebra
  `π(Γ)'` is exactly `Ad π(t)`-invariant in this very model. Only the *individual
  projection* fails to be near an invariant one.
* It **does** kill, dimension-free and already for exact representations of the
  genuine Kun–Thom pair, any proof step of the form *"an almost-`Ad u_t`-invariant
  central projection of the `Γ`-commutant is `‖·‖₂`-close to an exactly invariant
  one"*. The gap is `1/sqrt 2` against a defect `sqrt(2/m) → 0`. This is the
  shape the Hilbert–Schmidt transcription of the median/majority step needs, and it
  has no dimension-free form.
* It evades the two fences already recorded on `kt-centralizer-normalization-hs`.
  It is not small-block surgery: `tr(p) → 1/2`, so the structure is macroscopic.
  It is not amplification: the multiplicity space `M_k(C)` is untouched and the
  cycle lives in the center, whereas `σ ⊗ 1` acts componentwise and leaves both
  estimates unchanged.
* What survives as the licensed shape is a step that rounds the *algebra*, or one
  that uses integrality of a counting invariant. Kun–Thom's permutation proof gets
  its canonicity from integer orbit counts and isotropy orders with a residual
  index below two; Theorem B says the center of a matrix commutant supplies no
  such integrality, since all `N` atoms here have equal trace `1/N` and the cycle
  admits no canonical arc.

## 3. Net position

`kt-centralizer-normalization-hs` is now: (i) settled affirmatively for every
genuine coordinatewise model, by Theorem A and Corollary A1, with no hypothesis
on the coordinates; (ii) untouched in the approximate-coordinate regime, which is
the whole remaining problem; and (iii) closed to central-projection rounding as a
proof mechanism, by Theorem B.
