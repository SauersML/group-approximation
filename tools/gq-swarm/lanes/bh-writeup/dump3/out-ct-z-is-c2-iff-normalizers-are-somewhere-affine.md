---
rg: 2
id: out-ct-z-is-c2-iff-normalizers-are-somewhere-affine
kind: claim
title: Kourovka 17.57 reduces to local rigidity — Out(CT(Z)) = C_2 iff every homeomorphism of the profinite integers normalizing CT(Z) and fixing N_0 is affine on some box; every normalizer already preserves Z, preserves or swaps N_0 and Z_<0, and fixes every integer's germ group pointwise
requires:
  - ct-p-z-groups-are-pairwise-nonisomorphic
  - ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers
artifacts:
  - research/artifacts/gq-bh-bh-kourovka-problems.md
---

**ESTABLISHED as a reduction** (lane proof, not reviewed). No priority is claimed.
Kourovka 17.57 is now answered **yes** on main: `ct-z-normalizers-are-2-and-3-regular`
and `out-ct-z-is-c2` prove condition (b) from dilation recursions in bases 2 and 3 and a
Cobham-type theorem, bypassing the local germ approach recorded under "What remains".

Inputs:
- Matui arXiv:1210.5800, read at source: Theorem `spatial`, Proposition `tfg=F`, and
  the lemma before `spatial>iso`.
- The two required nodes.

## Setting

Kourovka 17.57 (S. Kohl) asks whether `Out(CT(Z)) = ⟨σ⟩ ≅ C_2`, where
`σ(n) = −n − 1`.

Take `P` = all odd primes, so `P'` = all primes and `X = Ẑ = ∏_p Z_p`. By
`ct-p-z-groups-are-pairwise-nonisomorphic` (Setup), `CT(Z) = F := [[G]]`, where `G` is
the germ groupoid of canonical box maps on `Ẑ`. Let

    N := {φ ∈ Homeo(Ẑ) : φ F φ^{-1} = F}.

`σ` extends to `x ↦ −x − 1` on `Ẑ`. It conjugates the canonical box map
`B(r', m') → B(r, m)` to the canonical box map
`B(m' − 1 − r', m') → B(m − 1 − r, m)`. So `σ ∈ N`. Also `σ ∉ F`, since `F` preserves
`N_0` and `σ(N_0) = Z_{<0}`.

## Theorem

1. **Spatial.** `Aut(CT(Z)) ≅ N` and `Out(CT(Z)) ≅ N/F`.
   - Matui `spatial` and `tfg=F` make every automorphism conjugation by some `φ ∈ N`.
   - The centralizer of `F` in `Homeo(Ẑ)` is trivial. If `ψ(x) ≠ x`, pick a clopen
     `A ∋ x` with `ψ(A) ∩ A = ∅` and an involution `τ ∈ F` with `∅ ≠ supp τ ⊆ A`.
     Then `ψτψ^{-1}` is supported in `ψ(A)`, so `ψτψ^{-1} ≠ τ`.
2. **Integers are intrinsic.** Every `φ ∈ N` satisfies `φ(Z) = Z`, and
   `φ(N_0) ∈ {N_0, Z_{<0}}`.
   - By Step 2 of `ct-p-z-groups-are-pairwise-nonisomorphic`, the points with
     nontrivial germ group are `Ẑ ∩ Q`, and `Ẑ ∩ Q = Z`: a rational number that is a
     `p`-adic integer for every `p` is an integer. Conjugation by `φ` preserves "nontrivial
     germ group", so `φ(Z) = Z`.
   - `G`-orbits are permuted by `φ`. The `G`-orbits inside `Z` are exactly `N_0` and
     `Z_{<0}`.
     - Canonical box maps send `r' + tm'` to `r + tm` with the same `t`, and `t ≥ 0`
       iff the point is nonnegative.
     - Class transpositions `τ_{x(m), y(m)}` with `m > max(|x|, |y|)` act
       transitively on each of `N_0` and `Z_{<0}`.
3. **Germ groups are fixed pointwise.** For every `n ∈ Z`, the germ group is all of
   `Γ = Q_{>0}^×`. Indeed `T_m(n) = ⌊n/m⌋`, which equals `0` or `−1` for all large
   `m`, so every `m/m'` lies in `Γ_n`. Every `φ ∈ N` intertwines germs at `n` and
   `φ(n)` by the identity of `Γ`: for each `γ ∈ Q_{>0}^×`,

       φ(n + γ(x − n)) = φ(n) + γ(φ(x) − φ(n))   for x in a neighborhood of n (depending on γ).

   Proof. Conjugation induces `α_n : Γ → Γ`.
   - By Steps 3–4 of the 17.60 node, `α_n` maps the axis labeled `q` at `n` to the
     axis labeled `q` at `φ(n)`. So it maps `H_q` to `H_q` for every prime `q`, and it
     maps `A_q`-contracting germs to `A_q`-contracting germs.
   - `q ∈ ⋂_{p ≠ q} H_p = ⟨q⟩` contracts `A_q`, so `α_n(q) = q^e` with `e ≥ 1`. The
     same holds for `α_n^{-1}`, so `e = 1`.
   - Hence `α_n = id`.
4. **Reduction.** The following are equivalent.
   - (a) `Out(CT(Z)) = ⟨σ⟩ ≅ C_2`.
   - (b) Every `φ ∈ N` with `φ(N_0) = N_0` is *affine on some box*: there are
     rationals `A` and `C ≠ 0` and a box `B` with `φ(z) = A + Cz` for `z ∈ B`.
   - (c) Every `φ ∈ N` restricts on `Z` to a residue-class-wise affine permutation.

   **(b) ⇒ (c).** Let `φ(z) = A + Cz` on `B`, and fix `x ∈ Ẑ`.
   - `F` acts minimally. By Matui's lemma, every germ of `G` extends to an element of
     `F`. So some `g ∈ F` has `g(x) ∈ B`.
   - Near `x`, `φ = h^{-1} ∘ φ ∘ g` with `h = φgφ^{-1} ∈ F`.
   - `g` is canonical near `x`, `φ` is affine near `g(x)`, and `h^{-1}` is canonical
     near `φ(g(x))`. So `φ` is affine, with rational slope and offset, near `x`.
   - By compactness `φ` is affine on each piece of a finite box partition, so
     `φ|_Z` is residue-class-wise affine.
   - For `φ` with `φ(N_0) = Z_{<0}`, apply this to `σφ`, which fixes `N_0` and is in
     `N`.

   **(c) ⇒ (a).** Take `φ ∈ N`, replacing it by `σφ` if necessary so that
   `φ(N_0) = N_0` (by item 2). Then `φ|_Z ∈ RCWA^+(Z) = CT(Z)` by
   `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers`. So `φ ∈ F`, because
   `Z` is dense. Hence `N = F ⊔ σF`.

   **(a) ⇒ (b).** Every element of `F` is affine on boxes.

## What remains, and why it is genuinely local (superseded by `out-ct-z-is-c2`)

(b) is a local rigidity statement for a germ `f` of `(Ẑ, 0)`, with `f(0) = 0`, that
commutes with all dilations `u ↦ γu` (`γ ∈ Q_{>0}`) as germs, by item 3. It also
satisfies the translation relations
`f(d + x) = f(d) + s_d f(x)` (`x ∈ N_d Ẑ`, `s_d ∈ Q_{>0}`) for integers `d`. These come
from conjugating the class transpositions `τ_{0(M), d(M)}`.

One real attempt, recorded here:
- **What it gives.**
  - The slopes form a cocycle: `s_{d+x} = s_d s_x` for `x ∈ N_d Z`.
  - They are dilation invariant: `s_{γd} = s_d` near `0`.
  - Hence `s = 1` at some special points, e.g. `y = (q^j − 1)N` when `q` is prime to
    the relevant modulus.
- **Where it breaks.** It does not give `s ≡ 1` on a box. Each neighborhood (`N_d`,
  and the dilation box `U_γ`) depends on the element, and the argument is circular in
  those moduli.

**Calibration.** For `P = ∅` the group is Thompson's `V`, and `Out(V) ≅ O_2` is
infinite (Brin; BCMNO, recorded in
`out-v-contains-the-root-problem-for-the-full-2-shift`). So normalizing
homeomorphisms of such full groups need not be piecewise affine. Any proof of (b) must
use the multiplicity of primes: the germ group `Q_{>0}^×` of rank `∞` together with
the dense set of integer points. With one prime, the germ group `⟨2⟩` leaves a free
fundamental domain.
