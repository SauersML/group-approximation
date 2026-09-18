# Second adversarial check of Kourovka 17.57 (bh-pal-kourovka57, 2026-09-18)

**Question** (Kourovka 17.57, S. Kohl): is `Out(CT(Z)) = ⟨n ↦ −n−1⟩ ≅ C_2`?

**Scope.** `gq-bh-bh-free-43-kourovka-17-57-check.md` already passed the reduction
(`out-ct-z-is-c2-iff-normalizers-are-somewhere-affine`) and the Bell–Cobham route
(`ct-z-normalizers-are-2-and-3-regular`). This check re-derives the **second route**, the
Adamczewski–Bell steps 1–8 of `out-ct-z-is-c2`. It also looks for holes that the first check did not
target.

**Verdict: PASS.** The result is conditional on two published theorems, used as stated:
- Matui, arXiv:1210.5800, Theorem `spatial` + Proposition `tfg=F`;
- Adamczewski–Bell, *A problem about Mahler functions*, Ann. Sc. Norm. Super. Pisa (5) 17 (2017),
  Theorem 1.1 (= arXiv:1303.2019 `thm: main`).

No gap was found. There are three wording fixes, none of which changes the argument.

## Re-derived steps

1. **Dilation recursion.** `g`: `z ↦ bz + e` is the canonical map `B(r, b) → B(br + e, b²)`. Its
   complements are finite unions of `b − 1` and `b² − 1` boxes. Splitting each box of the first into
   `b + 1` boxes gives `(b−1)(b+1) = b² − 1` pieces, so `g` extends to an element of `F`.
   - Take `h = φgφ⁻¹ ∈ F`. It is `w ↦ r'' + (m''/m')(w − r')` on the pieces of a finite box
     partition, so `h(w) = A + Bw` with `A ∈ Q` and `B ∈ Q_{>0}` locally constant.
   - `A∘φ` and `B∘φ` are locally constant on the compact space `Ẑ`, hence periodic mod some `P` on `Z`.
   - Hence `Φ(bk + e) = β(k)Φ(k) + α(k)`, with `α, β` periodic mod `P`. **PASS.**
2. **Regularity.** Write `r = bs + e`. Induction on `j` puts every kernel sequence
   `n ↦ Φ(b^j n + r)` in `W = {χΦ + χ'}` (`χ, χ'` periodic mod `P`), and `dim W ≤ 2P`. **PASS.**
3. **Regular ⇒ Mahler.**
   - Every `v` in the kernel span satisfies `Σ_n v(n)zⁿ = Σ_r z^r (Λ_r v)(z^b)`, so
     `V(z) = A(z)V(z^b)` with `A = Σ_r z^r M_r`.
   - The `d + 1` series `F(z^{b^i})`, `0 ≤ i ≤ d`, lie in the `Q(z)`-span of the `d` components of
     `V(z^{b^d})`. This is a homogeneous dependence; take the largest index with a nonzero
     coefficient. That is `b`-Mahler in the sense of Adamczewski–Bell (`P_n ≠ 0`). **PASS.**
4. **Rational ⇒ quasi-polynomial.**
   - Integer values and the cyclic shift module `M ↪ Z^{d'}` make the minimal recurrence polynomial `χ`
     monic in `Z[x]`.
   - Polynomial growth gives analyticity in `|z| < 1`, so every root satisfies `|α| ≤ 1`.
   - `χ ∈ Q[x]`, so conjugates are roots too.
   - Kronecker then makes every nonzero root a root of unity. **PASS.**
5. **An affine class.**
   - No class is constant, since `Φ` is injective.
   - If every class had degree ≥ 2, then `#{n : Φ(n) ≤ Y} = O(√Y)`, against `Y + 1`.
   - A degree-1 class `Φ(i + Nt) = c_0 + c_1 t` has integer `c_1 = Φ(i+N(t+1)) − Φ(i+Nt) > 0`.
   **PASS.**
6. **Extension to a box.** `t ↦ i + Nt` is a homeomorphism `Ẑ → B(i, N)`, because `Ẑ` is
   torsion-free. `{t ≥ t_0}` is dense, so `φ(i + Nt) = c_0 + c_1 t` on `B(i, N)`. Its image is the
   box `B(c_0 mod c_1, c_1)`. That is condition (b) of the reduction. **PASS.**

## Holes hunted that the first check did not name

- **Hausdorff germ groupoid** (Matui works with Hausdorff étale groupoids). Two canonical maps that
  agree on a nonempty open set agree on infinitely many integers. Rational affine maps agreeing on an
  infinite set are equal. So germs are determined on overlaps, and G is Hausdorff. **Holds.**
- **Zero root of `χ`.** Choose `n_1` so that the shifted sequence satisfies its minimal recurrence
  from index 0. Only nonzero roots enter step 4 anyway. **Harmless.**
- **The Mahler definition** is quoted in the node with a leading `1` (inhomogeneous). Step 3 gives the
  homogeneous form, which implies it. **Harmless.**

## Wording fixes for `out-ct-z-is-c2`

- Cite the published version: Ann. Sc. Norm. Super. Pisa Cl. Sci. (5) 17 (2017) 1301–1355.
- In step 4, say "choose `n_1` so that `0` is not a root of `χ`".
- In step 8, name the image box `B(c_0 mod c_1, c_1)`.

## Priority

Not re-checked here. The node claims no priority. The Palomar scope requires "solved here, not in the
literature", and that search belongs to bh-openq-lists.

## Lean consequence

A fully unconditional Lean proof needs two things:
- Matui's spatial theorem for `CT(Z)`: a Rubin-type reconstruction. A direct proof on `Z` is plausible
  but long.
- Adamczewski–Bell, or Bell's Cobham theorem.

Both are far outside Mathlib. The elementary layer is formalized in
`GroupApproximation/ClassTransposition/Out/`:
- σ normalizes `CT(Z)`;
- `CT(Z)` preserves `N_0`;
- the centralizer of the class transpositions in `Perm(Z)` is trivial;
- conjugation by σ has order exactly 2 in `Out(CT(Z))`.
