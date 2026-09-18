---
rg: 2
id: ct-z-normalizers-are-2-and-3-regular
kind: claim
title: Every homeomorphism of the profinite integers normalizing CT(Z) restricts to a bijection of N_0 (after the flip) that is both 2-regular and 3-regular with polynomial growth; with Bell's generalized Cobham theorem this gives Out(CT(Z)) = C_2, answering Kourovka 17.57
requires:
  - out-ct-z-is-c2-iff-normalizers-are-somewhere-affine
  - bell-generalized-cobham-theorem
artifacts:
  - research/artifacts/gq-bh-bh-kourovka-problems.md
---

**ESTABLISHED** (lane proof, not reviewed). No priority is claimed.

Items 1–2 are self-contained. Item 3 imports Bell's Theorem 1.4 (Sém. Lothar. Combin.
54A (2006), Art. B54Ap), which is pinned at source in `bell-generalized-cobham-theorem`.
The earlier citation to "SLC 55, B55f" was wrong.

`out-ct-z-is-c2` gives a second, independent route to the same conclusion. It replaces
Bell by Adamczewski–Bell arXiv:1303.2019, Theorem `thm: main`, read at source, and
writes out the steps from regular to quasi-polynomial to affine class in full.

Notation is as in `out-ct-z-is-c2-iff-normalizers-are-somewhere-affine`:
- `F = CT(Z) = [[G]]` acts on `Ẑ`.
- `N` is its normalizer in `Homeo(Ẑ)`.
- `σ(x) = −x − 1`.

Take `φ ∈ N`. By item 2 of that node, `φ(Z) = Z`, and after replacing `φ` by `σφ` we
may assume `φ(N_0) = N_0`. Put `Φ := φ|_{N_0}`, a bijection `N_0 → N_0`.

## 1. Digit recursions with periodic coefficients

Fix `b ≥ 2`, a digit `0 ≤ e < b`, and a residue `0 ≤ r < b`.
- **A dilation element.** `z ↦ bz + e` is the canonical box map `B(r, b) → B(br + e, b²)`,
  since `br + e < b²`. Extend it to some `g ∈ F`, which is possible because
  `Ẑ ∖ B(r, b)` and `Ẑ ∖ B(br + e, b²)` are nonempty clopen sets.
- **Its conjugate.** `h = φgφ^{-1} ∈ F` is canonical, i.e. `w ↦ A_i + B_i w` with
  rational `A_i` and `B_i > 0`, on each piece of a finite box partition.
- **The recursion.** For `k ∈ B(r, b) ∩ N_0`,
  `Φ(bk + e) = h(Φ(k)) = β(k) Φ(k) + α(k)`, where `α = A∘φ` and `β = B∘φ` are locally
  constant on the box.
- **Periodicity.** Taking the union over the `b` residues `r`, and a common modulus
  `P`:

      Φ(bk + e) = β_{b,e}(k) Φ(k) + α_{b,e}(k),   with β_{b,e}, α_{b,e} periodic mod P.

## 2. Regularity and growth

For `b ∈ {2, 3}`, `Φ` is `b`-regular over `Q`.
- By induction on `j`, `Φ(b^j n + r) = B_{j,r}(n) Φ(n) + A_{j,r}(n)`, where `A_{j,r}`
  and `B_{j,r}` are periodic mod `P`, with the same `P` for all `j`.
- So the `b`-kernel of `Φ` lies in `{χ·Φ + χ' : χ, χ' periodic mod P} =: W`, a `Q`-space
  of dimension `≤ 2P`. In Bell's notation (Def. 1.2), `M_Q(Φ; b)` is finitely
  generated.
- The `b`-kernel sequences are also integer-valued, so `M_Z(Φ; b)` is finitely generated
  too: evaluation at `dim W` suitable points embeds the integer-valued part of `W` in
  `Z^d`, and `Z` is Noetherian. So Bell's Theorem 1.5, stated for `(Z, k)`-regular
  sequences, applies as stated.
- `Φ` is integer-valued. The recursion with bounded coefficients gives
  `|Φ(n)| ≤ C n^D`.

## 3. Conclusion: Out(CT(Z)) = C_2

1. **Linear recurrence.** Bell, Theorem 1.4 with `R = Q`, `k = 2`, `l = 3`, gives
   one for `Φ`, over `Q`.
2. **Quasi-polynomial.** Integer values and polynomial growth make the characteristic
   roots roots of unity. This is Bell's Theorem 1.5, or the self-contained steps 4–6
   of `out-ct-z-is-c2`. So there are `N` and `n_0` such that, on each class
   `i mod N` (`n ≥ n_0`), `Φ` agrees with a polynomial `p_i ∈ Q[t]`.
3. **Some class is affine.**
   - Injectivity rules out `deg p_i = 0`.
   - If every `deg p_i ≥ 2`, then `#{n : Φ(n) ≤ Y} = O(√Y)`. But `Φ(N_0) = N_0`
     forces this count to be `Y + 1`.
   - So some class has `Φ(i + Nt) = c_0 + c_1 t` (`t ≥ t_0`), with integers
     `c_1 > 0` and `c_0`.
4. **Extension to a box.** By density of `{i + Nt : t ≥ t_0}` in `B(i, N)`, `φ` is
   affine on `B(i, N)`.
5. **Conclusion.** That is condition (b) of
   `out-ct-z-is-c2-iff-normalizers-are-somewhere-affine`, hence
   `Out(CT(Z)) = ⟨σ⟩ ≅ C_2`. This answers Kourovka 17.57 positively.

## Remarks

- **What is not needed.** The germ-group rigidity (item 3 of the parent node) is not
  used here. Only the finite-piece structure of conjugates of the dilation elements
  `z ↦ bz + e` is used, for two multiplicatively independent bases.
- **Why one prime is not enough.** For `V` (`P = ∅`), only base-2 dilations exist, and
  2-regularity alone does not force piecewise affinity. That is consistent with
  `Out(V) ≅ O_2` being infinite.
