---
rg: 2
id: closed-mcg-finite-index-injections-citation
kind: route
title: Import Behrstock--Margalit's Theorem 3 and specialize it to closed surfaces of genus at least three
target: closed-mcg-finite-index-injections-are-conjugations
requires: []
---

Citation import, not a reproof. Read on 2026-09-16 from the arXiv PDF of
arXiv:math/0504328v2, title page and Section 1.

**Source.** J. Behrstock and D. Margalit, *Curve complexes and finite index
subgroups of mapping class groups*.

**Conventions**, verbatim from Section 1:

> "Let S = Sg,n be a surface, by which we always mean a connected, orientable
> surface of genus g with n punctures. The extended mapping class group of S
> is: Mod(S) = π0(Homeo±(S))"

So their `Mod(S)` is `Mod^±` in the notation of the target.

**The theorem**, verbatim:

> "Theorem 3. If S is a surface which is not S0,2, S0,3, S0,4, S1,0, S1,1,
> S1,2, or S2,0, then every injection of a finite index subgroup of Mod(S)
> into Mod(S) is the restriction of an inner automorphism of Mod(S). If S is
> one of these exceptional surfaces, then there is an isomorphism of finite
> index subgroups of Mod(S) which is not the restriction of an inner
> automorphism."

**Attribution of the closed case**, verbatim from the same page:

> "this specific question was first investigated by Irmak, who showed that the
> answer is no for S2,0 (see below) and yes for all other Sg,n with g ≥ 2
> [17] [16] [15]."

Their reference [17] is E. Irmak, *Superinjective simplicial maps of complexes
of curves and injective homomorphisms of subgroups of mapping class groups*,
Topology 43(3) (2004) 513--541. [16] is arXiv:math.GT/0211139 and [15] is
arXiv:math.GT/0407285. Irmak's papers were not read here.

**Genus 2**, verbatim, for the Scope note of the target:

> "In the case of S2,0, if Γ is a finite index subgroup of Mod(S2,0) and
> ρ : Γ → Mod(S2,0) is an injection, then ρ is given by ρ(g) = f gf −1ισ(g),
> where f ∈ Mod(S2,0), ι is the hyperelliptic involution, and σ : Γ → Z2 is a
> homomorphism"

**Specialization.**
1. Take `S = S_(g,0)` with `g ≥ 3`. It is not on the exceptional list.
2. The target allows any finite-index `Λ ≤ Mod^±(S_g)`, which is a
   finite-index subgroup of their `Mod(S)`. A finite-index subgroup of
   `Mod(S_g)` is one of these, because `Mod(S_g)` has index 2 in `Mod^±(S_g)`.
3. An injection `ψ: Λ → Mod^±(S_g)` is then an injection of a finite-index
   subgroup of their `Mod(S)` into `Mod(S)`.
4. So Theorem 3 gives `φ ∈ Mod^±(S_g)` with `ψ = (x ↦ φ x φ^-1)|_Λ`, which is
   the target. `∎`
