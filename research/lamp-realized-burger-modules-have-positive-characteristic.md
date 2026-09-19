---
rg: 2
id: lamp-realized-burger-modules-have-positive-characteristic
kind: claim
title: "Class-kill for lamp realizations of Burger modules: in any C(Ω,A) ⋊ Λ, invariant finitely generated submodules carry finite actions, and a realization of R^2 (injective, or modulo constants) on which e_12(1) acts forces char R > 0; so the Z^2, Z[1/2]^2 and Z[t^±]^2 Burger/EJZK pairs never sit in a lamp group"
distinct_from:
  char-p-burger-lamp-realizations-refute-haagerup: that is the positive criterion in characteristic p; this shows why the characteristic must be positive, for every coefficient group and every acting group
  coordinate-shadows-rigidify-abelian-normalizers-in-nv: that concerns abstract Z^2 subgroups of nV and their normalizers; this concerns modules of locally constant functions and holds for any group acting on any compact space, not just nV
  cantor-integer-maps-pair-lacks-relative-property-t: that shows the full pair (C(C,Z) ⋊ V, C(C,Z)) lacks relative (T); this shows that no Burger-type submodule of C(Ω,A) exists in characteristic 0, which is a different, submodule-level obstruction
  abelian-lamp-wreaths-cannot-create-u3-q-or-aff-q: that is about subgroups of abelian lamp wreath products over Q; this is about equivariant copies of R^2 inside continuous-function lamp modules
artifacts:
  - research/lamp-realized-burger-modules-have-positive-characteristic-proof.md
---

**ESTABLISHED** by `lamp-realized-burger-modules-have-positive-characteristic-proof` (elementary,
no imports). Lane proof by swarm-0917-w17-w17-nv-break. Not independently reviewed.

## Setting

- `Ω` is a compact space and `A` a discrete abelian group.
- `C(Ω, A)` is the group of continuous, i.e. locally constant, maps. Each has finite image.
- A group `Λ` acts on `Ω` by homeomorphisms, and on `C(Ω, A)` by `λ·f = f∘λ^-1`.
- This covers every lamp host used on the board:
  - `C(C^n, F) ⋊ nV ≤ nV`;
  - `C(C, Z) ⋊ V ≤ 2V`;
  - `C(C, Γ) ⋊ V`.

## Theorem C

- **(a) Finite actions on finitely generated submodules.** If `N ≤ C(Ω, A)` is finitely generated
  and `Λ`-invariant, then `Λ` acts on `N`, and on `N/(N ∩ A·1)`, through a finite group.
- **(b) Positive characteristic.** Let `R` be a unital ring and `M = R^2`, with `Λ` acting on `M`
  through a homomorphism `q` to `GL_2(R)` such that `e_12(1) ∈ q(Λ)`. Suppose `ι : M → C(Ω, A)` is
  additive with `λ·ι(m) − ι(q(λ)m) ∈ A·1` for all `λ, m`, and injective modulo constants
  (`ι(m) ∈ A·1` forces `m = 0`). Then `N·1_R = 0` for some `N ≥ 1`.
  - `N` can be taken to be the exponent of the finite set of differences
    `{ι(e_1)(x) − ι(e_1)(y)}`.
  - If `A` is torsion-free, no such `ι` exists at all.

## Consequences (the class killed)

Every route of the form "find a Burger-type relative (T) pair `(M ⋊ Γ, M)` whose module sits
equivariantly in a lamp group of locally constant functions" dies when:
- `M = Z^2` with `Γ ≤ SL_2(Z)` non-amenable (Burger): by (a), since `Γ` is infinite; also by (b);
- `M = R^2` with `R = Z[1/2]`, `Z[t,t^-1]`, `O_K`, or any ring of characteristic `0`
  (EJZK/Shalom): by (b);
- `A` is torsion-free, e.g. `C(C, Z)`, whatever `R` is: by (b).

**Invariant.** The value set `V(f) = f(Ω)`. It is finite, and it is preserved by composition with
homeomorphisms (up to translation, modulo constants).

**Death step.** The unipotent orbit `k ↦ k ι(e_1) + ι(e_2)` has values in one bounded family of
translates of `V(ι(e_2))`, for all `k ∈ Z`. This forces `ι(e_1)` to be torsion-valued modulo
constants, so `ι(N e_1)` is constant. For finitely generated `N`, the same finiteness gives a
finite partition of `Ω` that `Λ` permutes.

**Survivors.** Only characteristic `p` modules with torsion coefficients, i.e. the setting of
`char-p-burger-lamp-realizations-refute-haagerup`. There the module is infinite-dimensional over
`F_p`, so (a) says nothing.
