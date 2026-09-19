---
rg: 2
id: hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan-proof
kind: route
title: Finite balls of the Olshanskii--Osin--Sapir monster are balls of a hyperbolic stage, so residually finite stages make the monster LEF
target: hyperbolic-rf-gives-torsion-free-lef-quotientless-kazhdan
requires:
  - kazhdan-torsion-free-tarski-monster-satisfies-kk
---

## 0. Imports

All from `kazhdan-torsion-free-tarski-monster-satisfies-kk` and its route, section 1, which quotes
[OOS] (Olshanskii--Osin--Sapir, *Lacunary hyperbolic groups*, Geom. Topol. 13 (2009),
arXiv:math/0701365), theorem `ExoticQuotients`, part 2, and its proof verbatim:

> Let $G$ be an arbitrary torsion free non--cyclic hyperbolic group with a finite set of generators
> $S$. Then there exists an infinite non-Abelian torsion free quotient group $Q_2$ of $G$ admitting
> a \gsc presentation and such that all proper subgroups of $Q_2$ are cyclic.

> [...] $G(i)=\langle G(i-1)|R_i\rangle$, and the group $Q_2$ is defined to be the limit of the
> sequence $G=G(0)\to G(1)\to \dots \to G(i)\to \dots$.

Used facts:
- **(M1)** Every stage `G(i)` is a torsion-free hyperbolic group. This is item (I1) of that route,
  the induction hypothesis "(torsion--free) hyperbolic group $G(i-1)$".
- **(M2)** `Q` is the direct limit of the epimorphisms `G(i-1) → G(i)`. Fix the finite generating
  set `S` of `G = Γ` and let `F = F(S)`. Put `N_i = ker(F → G(i))`. Then `N_0 ⊆ N_1 ⊆ ...` and
  `Q = F/N` with `N = ∪_i N_i`.
- **(M3)** `Q` is infinite, non-abelian and torsion-free, and every proper subgroup of `Q` is cyclic.
- **(M4)** For `G = Γ`, a torsion-free cocompact lattice in `Sp(n,1)` with `n ≥ 2`, `Q` is Kazhdan.
  This is the Corollary of `kazhdan-torsion-free-tarski-monster-satisfies-kk`: `Γ` is Kazhdan
  (Kostant) and hyperbolic, and property (T) passes to quotients. `Γ` is non-cyclic, since it is
  infinite and Kazhdan.

Standard facts used:
- **(S1)** An amenable discrete Kazhdan group is finite.
- **(S2)** A finitely presented LEF group is residually finite (Gordon--Vershik).
- **(S3)** Subgroups and extensions of amenable groups are amenable.

**LEF.** `Q` is LEF if, for every finite `A ⊆ Q`, some finite group `E` and injective map
`φ: A → E` satisfy `φ(ab) = φ(a)φ(b)` whenever `a, b, ab ∈ A`.

## 1. No nontrivial finite quotient (unconditional)

Let `π: Q → E` be onto a finite group `E ≠ 1`.
1. `ker π` is a proper subgroup of `Q`, so it is cyclic by (M3).
2. So `Q` is cyclic-by-finite, hence amenable by (S3).
3. By (M4), `Q` is also Kazhdan, so it is finite by (S1). This contradicts (M3).

`Q` is finitely generated as a quotient of `Γ`, and it is torsion-free and nontrivial by (M3).

## 2. LEF under `(RF_Γ)`

Let `A ⊆ Q` be finite, and pick `r` such that every element of `A` is represented by a word of
length at most `r` in `F`.

**Step 1: a stage that agrees with `Q` on the ball.** The set `W` of words of length at most `3r` is
finite. By (M2), every element of `W ∩ N` lies in some `N_i`, and the `N_i` increase, so some `j`
has `W ∩ N ⊆ N_j ⊆ N`. Hence for words `u, v, x` of length at most `r`:
- `u = v` in `Q` if and only if `u = v` in `G(j)`, because `u⁻¹v ∈ W`;
- `uv = x` in `Q` if and only if `uv = x` in `G(j)`, because `uvx⁻¹ ∈ W`.

**Step 2: a finite quotient of that stage.** By (M1), `G(j)` is a torsion-free hyperbolic quotient of
`Γ`, so it is residually finite by `(RF_Γ)`.
- Let `D` be the finite set of nontrivial elements of `G(j)` represented by words of length at
  most `2r`.
- Intersect one finite-index normal subgroup avoiding each element of `D`. This gives a
  finite-index normal subgroup `M` of `G(j)` with `M ∩ D = ∅`.
- Put `E = G(j)/M`.

**Step 3: the local embedding.** For `a ∈ A`, choose a word `u_a` of length at most `r` representing
`a`, and let `φ(a)` be the image of `u_a` in `E`.
- *Well defined:* two such words are equal in `Q`, hence in `G(j)` by Step 1.
- *Injective:* suppose `φ(a) = φ(b)`. The element `u_a⁻¹u_b` of `G(j)` lies in `M` and is
  represented by a word of length at most `2r`, so it is not in `D`. Hence it is trivial in
  `G(j)`, and `a = b` by Step 1.
- *Multiplicative:* if `a, b, ab ∈ A`, then `u_a u_b = u_{ab}` in `Q`, hence in `G(j)` by Step 1.
  So `φ(a)φ(b) = φ(ab)`.

So `Q` is LEF. LEF groups are sofic and operator MF (`isSofic_of_isLEF`, `isOperatorMF_of_isLEF`,
as cited in `torsion-free-lef-kazhdan-non-rf-seed`).

## 3. Not finitely presented under `(RF_Γ)`

If `Q` were finitely presented, then (S2) and section 2 would make it residually finite. Being
infinite, it would then have a nontrivial finite quotient, which contradicts section 1.

## 4. Remark: mapping tori of `Q` contain no `F_2` (unconditional)

Let `ψ ∈ Aut(Q)` and `P = Q ⋊_ψ Z`, and suppose `H ≤ P` is free of rank 2. Since `Q` is normal in
`P`, the intersection `H ∩ Q` is normal in `H`.

**Case `Q ≤ H`.** Then `Q` is a subgroup of a free group, so it is free. It is non-abelian, so its
rank is at least 2. An index-2 subgroup of it is then a proper non-cyclic subgroup, contradicting
(M3).

**Case `H ∩ Q` proper in `Q`.** Then `H ∩ Q` is cyclic by (M3), say `⟨c⟩` with `c ≠ 1`.
- Write `a, b` for free generators of `H`. Each of them conjugates `c` to `c^{±1}`.
- So `a²` and `b²` centralize `c`.
- Centralizers of nontrivial elements of a free group are cyclic, so `a²` and `b²` commute. That is
  false in `F(a, b)`.

So `H ∩ Q = 1`, and `H` embeds in `P/Q ≅ Z`, which is impossible.

This is recorded only as a constraint for L3-type requirements. No statement about finite
presentability is claimed.

## 5. The contrapositive

Assume (EKL2-tf). By (M3), (M4) and section 1, `Q` is a nontrivial torsion-free Kazhdan group with
no nontrivial finite quotient, so it is not LEF. Section 2 then shows that `(RF_Γ)` fails: some
stage `G(j)`, a torsion-free hyperbolic quotient of `Γ`, is not residually finite.

Torsion-free cocompact lattices in `Sp(n,1)` exist by Selberg's lemma (Corollary of
`kazhdan-torsion-free-tarski-monster-satisfies-kk`). So `torsion-free-non-residually-finite-hyperbolic-group`
follows.

## Checked against

- **Lacunary hyperbolic does not imply LEF.** Section 2 uses only (M2), the increasing union of
  kernels, together with residual finiteness of the stages. It uses no injectivity-radius estimate,
  and without `(RF_Γ)` it gives nothing.
- **Kazhdan limit versus cubulated stages.** Here the stages are quotients of `Γ`, so they are
  Kazhdan and not cubulated (Niblo--Reeves). This is why no special-cube-complex residual
  finiteness theorem (Wise, Agol) can discharge `(RF_Γ)`. The obstruction is unavoidable: for any
  increasing-kernel limit of finitely presented stages with a Kazhdan limit, cofinitely many stages
  are Kazhdan. The reason is Shalom's theorem that a Kazhdan group is a quotient of a finitely
  presented Kazhdan group `F/⟨⟨R⟩⟩`, with `R` finite, so `R ⊆ N_j` for large `j`. Shalom's theorem
  is quoted from memory and is used only in this remark.
