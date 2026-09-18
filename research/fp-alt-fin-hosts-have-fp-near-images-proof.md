---
rg: 2
id: fp-alt-fin-hosts-have-fp-near-images-proof
kind: route
title: Direct proof from simplicity of the finitary alternating group and the normal subgroup structure of GL_n(Q)
target: fp-alt-fin-hosts-have-fp-near-images
requires: []
---

Direct proof. Not independently reviewed. Notation as in the target.

**Item 1.** `Alt_fin(X)` and `FSym(X)` are normal in `Sym(X)`, since
conjugation preserves finite support and parity. So `Γ_fin` is normal in `Γ`,
and `Alt_fin(X) <= Γ_fin <= FSym(X)`. As `[FSym(X) : Alt_fin(X)] = 2`,
`Γ_fin` is one of the two.
- Let `c` be a 3-cycle. Then `<<c>>_Γ <= Alt_fin(X)`, and it contains
  `<<c>>_(Alt_fin(X))`, which is `Alt_fin(X)` because `Alt_fin(X)` is simple
  (`X` infinite).
- Let `τ` be a transposition and suppose `Γ_fin = FSym(X)`, so `τ ∈ Γ`. For
  2-subsets `{a,b}`, `{c,d}` of `X` pick `σ ∈ Sym(X)` of finite support with
  `σ{a,b} = {c,d}`. Composing with a transposition of two points outside
  `{a,b} ∪ {c,d} ∪ supp σ` if necessary makes `σ` even. So `Alt_fin(X)` acts
  transitively on transpositions by conjugation, `<<τ>>_Γ` contains every
  transposition, and `<<τ>>_Γ = FSym(X)`.

**Item 2.** If `Γ = <S | R>` is finitely presented, then by item 1
`Γ* = Γ/<<w>>_Γ` for one element `w`, so `Γ* = <S | R ∪ {w}>` with `w`
written as a word in `S`. Finite generation passes to quotients.

**Item 3.** `H ∩ FSym(X)` is normal in `H` because `FSym(X)` is normal in
`Sym(X)`. It is locally finite because `FSym(X)` is: finitely many finitary
permutations have supports inside one finite set `F`, so they generate a
subgroup of `Sym(F)`. The map `H -> Γ*` has kernel `H ∩ Γ_fin = H ∩ FSym(X)`.
If `H` has no nontrivial locally finite normal subgroup, the kernel is trivial.

**Item 4.** Let `L` be a locally finite normal subgroup of the group named.
- `(Q,+)` and `U_n(Q)` are torsion-free, and a locally finite group is a
  torsion group, so `L = 1`.
- `Aff(Q)`. The translations `D ≅ (Q,+)` form a normal subgroup. `L ∩ D = 1`
  since `D` is torsion-free, so `[L, D] <= L ∩ D = 1`. The centralizer of `D`
  in `Aff(Q)` is `D` itself (`x -> ax + b` commutes with `x -> x + 1` only if
  `a = 1`). So `L <= D`, hence `L = L ∩ D = 1`.
- `GL_n(Q)` and `SL_n(Q)`, `n >= 2`. Use two standard facts for a field `K`
  with more than three elements: `SL_n(K)` is perfect, and `PSL_n(K)` is
  simple.
  - `L_0 = L ∩ SL_n(Q)` is normal in `SL_n(Q)`. Its image in `PSL_n(Q)` is
    trivial or everything. It cannot be everything: then `L_0 · Z = SL_n(Q)`
    with `Z` the finite centre of `SL_n(Q)`, so `SL_n(Q)` would be locally
    finite, but it contains elements of infinite order. So `L_0 <= Z`, which is
    `{±I}` for `n` even and `{I}` for `n` odd.
  - For `g ∈ L` the commutator `[g, s]` lies in `L ∩ SL_n(Q) = L_0`, which is
    central. For central values, `s -> [g, s]` is a homomorphism
    `SL_n(Q) -> L_0`, since `[g, st] = [g, t] · t^-1 [g, s] t`. `SL_n(Q)` is
    perfect and `L_0` abelian, so it is trivial, and `g` centralizes
    `SL_n(Q)`.
  - `SL_n(Q)` acts absolutely irreducibly on `Q^n`, so its centralizer in
    `GL_n(Q)` is the scalars `Q^x I` (Schur). So `L` consists of scalars of
    finite order, `L <= {±I}`. For `SL_n(Q)` with `n` odd, `-I ∉ SL_n(Q)`, so
    `L = 1`.
- `PGL_n(Q)`, `n >= 2`. The preimage `L~` of `L` in `GL_n(Q)` is normal.
  `L~ ∩ SL_n(Q)` is normal in `SL_n(Q)`; as above it is central or all of
  `SL_n(Q)`. If it is all of `SL_n(Q)`, then `L` contains `PSL_n(Q)`, which is
  not locally finite. Otherwise `[L~, SL_n(Q)]` is central in `SL_n(Q)`, and
  the argument above makes `L~` centralize `SL_n(Q)`, so `L~ <= Q^x I` and
  `L = 1`.

**The consequence in item 4.** Let `GL_n(Q) <= Γ` with `Γ` finitely
presented. By item 3 and the above, `GL_n(Q)/K` embeds in `Γ*`, where
`K = GL_n(Q) ∩ FSym(X) <= {±I}`. The listed groups embed in `GL_n(Q)/K`:
- `A -> diag(A, 1) K` embeds `GL_(n-1)(Q)`, since `diag(A,1) = -I` is
  impossible;
- `SL_n(Q)` (`n` odd), `Aff(Q)` (as the matrices `[[a, b], [0, 1]]` in the
  top-left corner), `U_n(Q)` and `(Q,+)` are subgroups of `GL_n(Q)` whose
  locally finite normal subgroups are trivial, so each meets `K` trivially
  and embeds.

If `Γ` contains `PGL_n(Q)`, then `PGL_n(Q)` embeds in `Γ*` by item 3, since
its locally finite radical is trivial. `Γ*` is finitely presented by item 2,
and its near action on `X` is faithful by definition.
