---
rg: 2
id: closed-mcg-finite-index-injections-are-conjugations
kind: claim
title: For genus at least three every injection of a finite-index subgroup of a closed-surface mapping class group into the extended mapping class group of the same surface is a conjugation
distinct_from:
  finite-index-injections-into-braid-quotients-are-geometric: that specializes the same Behrstock--Margalit theorem to punctured spheres and to B_n modulo its centre; this specializes it to closed surfaces of genus at least three.
  closed-mcg-in-asymptotic-mcg-is-bordered-or-infinite-in-v: that sorts copies of closed-surface mapping class groups inside Aramayona--Funar groups; this is the rigidity of copies inside the extended mapping class group of the same closed surface.
---

**ESTABLISHED (literature import).** Let `S_g` be the closed orientable surface
of genus `g ≥ 3`. Write `Mod^±(S_g)` for its extended mapping class group and
`Mod(S_g)` for the orientation-preserving subgroup. Let `Λ ≤ Mod^±(S_g)` have
finite index, for instance a finite-index subgroup of `Mod(S_g)`. Let
`ψ: Λ → Mod^±(S_g)` be an injective homomorphism. Then there is
`φ ∈ Mod^±(S_g)` with `ψ(x) = φ x φ^-1` for all `x ∈ Λ`.

This is Behrstock--Margalit, Theorem 3, for the surface `S_(g,0)`. That surface
is not on its exceptional list. The theorem combines their results with those of
Korkmaz, Irmak and Bell--Margalit; the closed case `g ≥ 3` is credited to Irmak.
Source and verbatim statements: `closed-mcg-finite-index-injections-citation`.

**Scope.**
- **Genus 2 is exceptional.** There Behrstock--Margalit give injections of the
  form `ρ(x) = f x f^-1 ι^σ(x)`, with `ι` the hyperelliptic involution and `σ` a
  homomorphism to `Z/2`.
- **Same surface only.** Injections into mapping class groups of closed surfaces
  of larger genus are not constrained here. Aramayona--Leininger--Souto
  (arXiv:0811.0841v1, abstract) construct injections between mapping class
  groups of different closed surfaces.
- **Orientation.** Even if `ψ` lands in `Mod(S_g)`, the conjugator `φ` may
  reverse orientation.
