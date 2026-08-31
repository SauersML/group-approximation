---
rg: 2
id: x2-three-operator-reduction-proof
kind: route
title: Clock-shift encoding and averaged decompression prove the three-operator reduction
target: x2-reduces-to-three-operator-packets
requires: []
artifacts:
  - research/artifacts/x2-shadow-avoidance-recon-2026-08-31.md
---

Fix the packet `{b_1,…,b_m}` (self-adjoint contractions) and `ε > 0`.
All constants `C` below depend only on `m`; `δ(ε')` denotes an
`m`-dependent modulus with `δ(ε') → 0` as `ε' → 0`, not always the
same one.  Choose `ε'` at the end so that every accumulated error is
below `ε`.

**Setup.**  Local AFD is invariant under isomorphisms, so replace
`(R, {b_k})` by `(R ⊗ M_m, {b_k ⊗ 1})`.  Let `d = diag(1, ω,…,ω^{m−1})`
(`ω = e^{2πi/m}`), `c` the cyclic shift (`c e_{jj} c^* = e_{j+1,j+1}`),
and set

```text
u := 1⊗d,   w := 1⊗c,   x := (1/m) Σ_k b_k ⊗ c^k,
h := 1⊗diag(1,…,m).
```

Note `w u w^* = ω^{-1}u`-type clock–shift relations, `h` is a
polynomial in `u, u^*` with `C`-Lipschitz functional calculus (the
spectrum `{ω^j}` is `m`-gapped), and the corner extraction
`b_k ⊗ c^k = (1/m) Σ_j ω^{-jk} u^j (m x) u^{-j}` recovers each
Fourier layer of `x` by clock averaging, with norm at most `m‖x‖`.

**Apply the hypothesis** to `{u, w, x}` at tolerance `ε'`: this gives
a nonzero projection `s` and a finite-dimensional `B ⊂ R⊗M_m` with
support `s`, with `‖[u,s]‖, ‖[w,s]‖, ‖[x,s]‖ < ε'` and
`sys ∈_{ε'} B` for `y ∈ {u, w, x}`.

**Step 1 (block form of `s`).**  `‖[h,s]‖ ≤ Cε'` (Lipschitz calculus
of `u`).  With `p_j := 1⊗e_{jj}` (spectral projections of `h`,
recovered by Lagrange interpolation, coefficients bounded by `C`):
`‖p_i s p_j‖ ≤ Cε'` for `i ≠ j`, so `s` is `Cε'`-block-diagonal,
`s ≈ Σ_j s'_j ⊗ e_{jj}`.  Because `w` acts on blocks by pure shift —
`w (a ⊗ e_{jj}) w^* = a ⊗ e_{j+1,j+1}` with the SAME `a` — the
condition `‖[w,s]‖ < ε'` forces `‖s'_{j+1} − s'_j‖ ≤ Cε'` for all `j`.
Hence with `s' := s'_1`:

```text
‖s − s'⊗1_m‖ ≤ Cε'.
```

`s'` is `Cε'`-almost a projection (block-read of `s² = s`); replace it
by `1_{[1/2,1]}(s'_1)`, at cost `δ(ε')`.  It is nonzero: `‖s‖ = 1` is
attained on some block, and all blocks are near-equal, so
`‖s'‖ ≥ 1 − δ(ε')`.  Set `S := s'⊗1_m`, a nonzero projection with
`‖S − s‖ ≤ δ(ε')`.

**Step 2 (commutators for the original packet).**
`‖[x, S]‖ ≤ ε' + 2‖x‖·δ(ε') = δ(ε')`, and clock averaging extracts
each Fourier layer: since `1⊗d` commutes with `S` exactly (`S` has
scalar `M_m`-leg) and conjugation by a unitary is isometric,

```text
‖[b_k ⊗ c^k, S]‖ ≤ m · δ(ε')   ⟹   ‖[b_k, s']‖ ≤ δ(ε'),
```

reading the `c^k`-layer of `[m x, S] = Σ_k [b_k, s']⊗c^k`.

**Step 3 (exact finite-dimensional algebra at support `S`).**  The
compression `φ : B → S(R⊗M_m)S`, `φ(b) := SbS`, is unital-to-`S`,
completely positive, and `η`-multiplicative with
`η := C‖S − s‖ ≤ δ(ε')` — the defect `SbSb'S − Sbb'S = Sb(S−s)b'S +
Sb(s−1)... ` collapses to terms carrying `S − s` because `s` is `B`'s
unit, and it is bounded bilinearly, hence uniformly on the unit ball.
A finite-dimensional domain admits the classical averaged
perturbation (Christensen-type: Stinespring-dilate, average the
almost-intertwiner over the compact group `U(B)` with Haar measure —
the defect bound is uniform on the ball, so the averaging is
dimension-free — then polar-correct): there is a \*-homomorphism
`ψ : B → S(R⊗M_m)S` with `‖ψ − φ‖ ≤ f(η)`, `f` universal,
`f(η) → 0`.  Put `B₀ := ψ(B)` — an exact finite-dimensional
C\*-algebra — and `S₀ := ψ(s)`, a projection with
`‖S₀ − S‖ ≤ f(η)`, nonzero for `ε'` small.  `B₀` has support `S₀`.

**Step 4 (compression conditions).**  Let `x̂, û, ŵ ∈ B` denote
`ε'`-approximants of `sxs, sus, sws` from the hypothesis, with `û, ŵ`
polar-corrected inside `B` to unitaries of `sBs` (defect `δ(ε')`,
legitimate since `su s` is `δ(ε')`-unitary in `sRs`).  Then
`ψ(û), ψ(ŵ) ∈ B₀` are unitaries of `S₀B₀S₀` and `ψ(x̂) ∈ B₀`, each
within `δ(ε') + f(η)` of `S₀uS₀, S₀wS₀, S₀xS₀`.  For the original
packet: by Step 2's Fourier extraction applied inside `B₀` — the
element

```text
v_k := (1/m) Σ_j ψ(û)^j · m·ψ(x̂) · ψ(û)^{-j} · ω^{-jk} · ψ(ŵ)^{-k}
```

lies in `B₀` exactly (products of members of `B₀`), and unwinding the
same chain of estimates it is within `δ(ε') + Cf(η)` of

```text
S₀ (b_k ⊗ c^k)(1⊗c^{-k}) S₀ = S₀ (b_k⊗1) S₀
```

(each replacement — `ψ(û)` by `S₀uS₀`, `ψ(x̂)` by `S₀xS₀`, `ψ(ŵ)` by
`S₀wS₀`, compressions rejoined across near-commuting projections —
costs one `δ(ε') + f(η)` and there are at most `C` of them).  Since
`E_{B₀}` is contractive and fixes `v_k`:

```text
‖S₀(b_k⊗1)S₀ − E_{B₀}(S₀(b_k⊗1)S₀)‖ ≤ 2(δ(ε') + Cf(η)).
```

With Step 2 (`‖[b_k⊗1, S₀]‖ ≤ δ(ε') + 2f(η)`), the pair `(B₀, S₀)`
witnesses local AFD for `{b_k ⊗ 1}` at tolerance `ε` once `ε'` is
chosen small enough.  Transport back through the isomorphism.  ∎

**Model checks.**  (i) `m = 1`: the encoding is `u = w = 1`,
`x = b_1`, and the theorem is a tautology.  (ii) Commuting packets:
the construction is consistent with — and strictly weaker on that
locus than — `x2-local-afd-holds-on-abelian-packets`, as it must be.
(iii) The dead-corner escape this proof exists to close: with the
shift `w` absent from the encoded packet, the hypothesis may return
`s` living in a single diagonal corner not carrying the data (e.g.
`s ≤ p_2` for an encoding that stores `b_k` in column 1), and
decoding fails; near-commutation with `w` is exactly what forces the
near-equal blocks of Step 1.  This is why the reduction lands at
three operators, not two.  (iv) Step 3 is not vacuous bookkeeping:
without the averaged perturbation, `SB S` is a finite-dimensional
operator SYSTEM, not an algebra, and Popa's criterion demands an
algebra with support exactly the commuting projection.
