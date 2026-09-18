# Proximal ping-pong for Lawrence–Krammer on the point-push F_2 in B_4 (2026-09-17, sw-120)

Target: `zaremsky-3-02-braid-groups-embed-in-glnz` (first open case: is `B_4` Z-linear?).
Result node: `lk-b4-never-proximal-on-finite-index-subgroups`.

## Idea tested

`B_4 = F_2 ⋊ B_3` with `F_2 = <a, b>`, `a = s1 s3^-1`, `b = s2 a s2^-1` (the kernel of `B_4 -> B_3`).
If `rho` is a representation of `B_4` with `ker rho ∩ F_2 = 1`, then `ker rho` is central: for `k ∈ ker rho` and
`f ∈ F_2`, `[k, f] ∈ ker rho ∩ F_2 = 1`, and the centralizer of `F_2` in `B_4` is the center (`B_4 -> Aut(F_2)`
has kernel `Z(B_4)`, Dyer–Formanek–Grossman). So a unit specialization `LK(q_0, t_0)` that is faithful on `F_2`
would give Z-linearity of `B_4`.

Plan: certify faithfulness on `F_2` (or on a finite-index subgroup) by proximal ping-pong: a P_Θ-Schottky pair
on a flag variety of `K^6`, over some valued field, then transfer to unit parameters. A Schottky certificate is
a check on generators only, so it would avoid the length non-uniformity that stops the Krammer cone argument at
unit values. A P_Θ-Schottky group has every nontrivial element Θ-proximal, so a necessary condition is an
eigenvalue-modulus gap `|λ_k| > |λ_(k+1)|` for every `k ∈ Θ` and every element.

## Result

The necessary condition fails in the strongest form: **for every field with an absolute value, every
`(q_0, t_0)`, every `k = 1..5`, some element of every finite-index subgroup of `F_2` has `|λ_k| = |λ_(k+1)|`.**
Proof in `research/lk-b4-never-proximal-on-finite-index-subgroups-proof.md`. It rests on two
exact factorizations (`factor_witnesses.py`, output `factor_witnesses_out.txt`):

- `charpoly LK(a) = (x-1)^2 (x+q)(x+q^-1)(x+q^2 t)(x+q^-2 t^-1)`;
- `charpoly LK([a,b]) = (x - q^4 t^2)^3 (x - q^-2 t^-2)^2 (x - q^-8 t^-2)`, with `[a,b] = abAB`.

## Files

- `lk.py`: Krammer's matrices for `B_n` in sympy. For `n = 4` the braid relations hold and each `s_i` has
  characteristic polynomial `(x+q)^2 (x-1)^3 (x+q^2 t)` (`lk_out.txt`).
- `factor_witnesses.py`: the two factorizations above, plus `Δ a Δ^-1 = a^-1`, `Δ_4^2 = q^8 t^2 I`, and the
  same `3, 2, 1` multiplicity pattern for `Δ_4^2 Δ_3^-2` (`factor_witnesses_out.txt`).
- `trop.py L`: exact Laurent-polynomial products for all reduced words of length `<= L` and characteristic
  polynomials by Faddeev–LeVerrier. It keeps the monomial support of each coefficient of every cyclically reduced
  word (`spectra_L5.pkl`, 372 words; not committed, regenerate with `nice -n 10 python3 trop.py 5`, about 5 min).
- `troplib.py`, `analyze.py`, `prox.py`, `gaps.py`: the first (sampled) scan of 720 rays
  `w = (v(q), v(t)) = (cos θ, sin θ)` for monomial valuations. Outputs `analyze_out.txt`, `prox_out.txt`,
  `gaps_out.txt`: every word is tropically hyperbolic, and no ray has a uniform gap at any `k`.
- `exact_cover.py`: the monomial-valuation statement without sampling. Eigenvalue valuations are piecewise linear
  in `w`, so it tests every critical ray (monomial ties, Newton-point collinearities) and one interior ray per arc,
  in exact integer and rational arithmetic (`exact_cover_out.txt`: 394 critical rays, 788 test rays, no uniform
  gap at any `k`; witnesses of length `<= 4`, and length 1 suffices for `k = 3`). This is a special case of the
  theorem and agrees with it.

## What this rules out, and what it does not

Ruled out, for `LK_4` in Krammer's form: every proximal Schottky / P_Θ-Anosov certificate for any subgroup of
`B_4` that contains a nontrivial power of a conjugate of `a` and of `[a,b]`, in particular any finite-index
subgroup of `F_2` or of `B_4`. This holds over every valued field (monomial or non-monomial valuations,
p-adic, real, complex) and at every specialization, formal or not.

Not ruled out:

- non-proximal ping-pong, where the attracting sets come from Jordan-block or reducible dynamics (the way
  parabolic elements generate free subgroups of `SL_2(Z)`). By the theorem, any ping-pong for `LK_4` on a
  finite-index subgroup of `F_2` must have this shape;
- ping-pong for other representations of `B_4`;
- faithfulness mechanisms that are not ping-pong.
