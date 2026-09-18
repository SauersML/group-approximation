---
rg: 2
id: fiber-detecting-block-characters-force-npc-graph-manifolds
kind: claim
title: If every JSJ block of a loopless closed graph manifold has a rational character that detects its own fiber and kills its neighbors' fibers, then every block has charge zero and the manifold is non-positively curved; so a host design that supplies such characters cannot reach the non-virtually-fibered case
distinct_from:
  nonfibered-graph-manifold-groups-have-no-fg-normal-subgroups: that constrains how these groups meet normal free or surface subgroups of a host; this constrains local product structure around each block, through the Svetlov--Buyalo--Kobel'skii charge criterion.
  nonfibered-closed-graph-manifold-groups-satisfy-pbh: that is the open membership in B_A; this rules out one family of host designs for it and proves no membership.
  three-manifold-groups-linear-unless-closed-graph-manifold: that imports linearity; this imports the non-positive curvature criterion for graph manifolds.
---

**ESTABLISHED** (lane proof; item 2 imports a published criterion, read at source; not
independently reviewed; no novelty claimed for items 1--2, which are a direct reading of
Svetlov's definitions and Theorem III).

**Source.** P. Svetlov, *Homological properties of graph manifolds*, arXiv:math/0112308v2
(TeX `gelme.tex`, read on MSI).
- Class `M` (l.46--53): "a compact closed orientable Haken 3-manifold [whose] JSJ-surface
  splits M into Seifert pieces with orientable base orbifolds of negative Euler
  characteristic". The pieces `M_v` are the vertices of the graph `Γ_M(V, W)`; for a
  boundary torus `T_w` of `M_v`, `T_{-w}` is the torus of the neighboring block glued to it.
- `f_v ∈ H_1(M_v)` is the fiber class and `f_w ∈ H_1(T_w)` its preimage (l.200--203);
  `b_w = f_w ∧_w f_{-w} ∈ Z ∖ {0}` (l.303--306).
- Adjoint elements and Euler numbers (l.310--318): `z_v ∈ H_1(∂M_v)` is adjoint if
  `f_w ∧_w p_w(z_v) = 1` for all `w ∈ ∂v`, and then `ι_*(z_v) = -e_{M_v}(z_v) f_v`.
- Charge (l.394--396): `k_v = -e_{M_v}(φ_v)`, where `p_w(φ_v) = f_{-w} / b_w` for `w ∈ ∂v`.
- Matrix `H_M` (l.523--545): diagonal entries `s(v) k_v - Σ_{w(v)=v} 1/|b_w|`, where the sum is
  over loops at `v`; off-diagonal entries `-Σ_{w(v)=v'} 1/|b_w|` if `k_v k_{v'} > 0` and `0`
  otherwise.
- Theorem III (l.590--608): `M ∈ M` carries a non-positively curved metric iff "either 1)
  `H_M ≡ 0` or 2) the matrix `H_M` has a negative eigenvalue" (item NPC is credited there to
  Buyalo--Kobel'skii).

## Statement

Let `M ∈ M` have a JSJ graph `Γ_M` without loops (no torus of a block is glued to a torus
of the same block).

1. **Charge detection.** For a block `M_v` the following are equivalent:
   - (a) `k_v = 0`;
   - (b) some `λ ∈ H^1(M_v; Q)` has `λ(f_v) != 0` and `λ(ι_* f_{-w}) = 0` for every `w ∈ ∂v`,
     that is, `λ` detects the block's fiber and kills the fiber of every neighboring block
     on the common torus.
2. **All charges zero.** If `k_v = 0` for every block, then `H_M = 0`, so `M` is
   non-positively curved. Hence `M` is virtually fibered (Svetlov, as quoted in
   `three-manifold-groups-pbh-off-nonfibered-graph-manifolds`) and `pi_1(M)` is virtually
   special (Liu, ibid.).
3. **Host designs.** Let `M ∈ M` be loopless and not non-positively curved, for instance not
   virtually fibered. Then some block `M_v` has `k_v != 0`, so its fiber class is a rational
   combination of the neighbors' fiber classes in `H_1(M_v; Q)`. Consequently no embedding
   `pi_1(M) -> H` has the following *local product* shape: for every block, the image of
   `pi_1(M_v)` lies in a subgroup `P_v <= H` carrying a homomorphism `π_v : P_v -> Q` that is
   nonzero on the fiber and zero on the neighbors' fibers. Examples of that shape:
   - `P_v = K_v x A_v` with `A_v` abelian, the fiber having nonzero `A_v`-part and the
     neighbors' fibers lying in `K_v`;
   - in a mapping class group, fibers realized by powers of twists about curves `z_v`, with
     `pi_1(M_v)` mapped into `Mod(Y_v) x <T_{z_v}>` for a subsurface `Y_v` disjoint from `z_v`
     and not bounded by it, and neighbors' fibers mapped into `Mod(Y_v)`.

## Proof

**Item 1, (b) ⇒ (a).** `φ_v` is adjoint: `f_w ∧_w (f_{-w}/b_w) = b_w / b_w = 1`. So
`ι_*(φ_v) = -e_{M_v}(φ_v) f_v = k_v f_v` in `H_1(M_v; Q)`. Apply `λ`:
`k_v λ(f_v) = λ(ι_* φ_v) = Σ_w λ(ι_* f_{-w}) / b_w = 0`, and `λ(f_v) != 0`.

**Item 1, (a) ⇒ (b).** A character `λ` as in (b) exists iff `f_v` is not in the span `S` of
the classes `ι_* f_{-w}` in `H_1(M_v; Q)`. Write `f_{-w} = β_w f_w + b'_w c_w` on `T_w`, where
`c_w` is the boundary class of a fixed horizontal section of the orbifold bundle over the
base with its cone points removed, oriented so that `f_w ∧_w c_w = 1` for every `w` (the
induced boundary orientations give the same sign on every torus, so this is one global
choice). Then `b'_w = f_w ∧_w f_{-w} = b_w`. In `H_1(M_v; Q)` the classes
`c_w` satisfy exactly one relation, `Σ_w c_w ∈ Q f_v`, besides being independent of `f_v`
and of each other (the base has negative Euler characteristic and at least one boundary
circle, and cone-point classes are rational multiples of `f_v`). So an element
`Σ_w μ_w ι_* f_{-w}` of `S` lies in `Q f_v` only if all `μ_w b'_w` are equal, i.e. it is a
multiple of `Σ_w ι_* f_{-w}/b_w = k_v f_v`. If `k_v = 0` this multiple is `0`, and `f_v != 0` in
`H_1(M_v; Q)` (the classes `c_w`, `f_v` span a space of dimension equal to the number of
boundary tori, with the single relation above), so `f_v ∉ S` and `λ` exists.

**Item 2.** With every `k_v = 0` and no loops, every diagonal entry of `H_M` is `0` and no
off-diagonal entry is nonzero, since `k_v k_{v'} > 0` never holds. So `H_M ≡ 0`, and Theorem
III (NPC), case 1, applies.

**Item 3.** The composite `π_v ∘ (restriction)` is a character of `pi_1(M_v)` as in item 1(b),
so `k_v = 0` for every block, and item 2 makes `M` non-positively curved, a contradiction.
The two examples have `π_v` the projection to `A_v`, respectively to the `T_{z_v}` exponent
(the product `Mod(Y_v) x <T_{z_v}>` is direct because `z_v` is disjoint from `Y_v` and not
isotopic to a boundary curve of it).

## Scope and use

- Loops: a loop contributes `-1/|b_w|` to a diagonal entry, so item 2 needs the loopless
  hypothesis. For the open node this costs nothing: a finite cover obtained from the map
  `pi_1(M) -> pi_1(Γ_M) -> (Z/2)^{loops}` unwraps every loop, blocks lift isomorphically, and
  such covers stay non-virtually-fibered.
- The item-1 criterion is local and homological, so it survives finite covers: if a block
  of `N` has such a character, every block of every cover above it does.
- What a successful host must therefore do, in at least one block of every cover: realize
  a fiber that is, modulo commutators of the block, a rational combination of the neighbors'
  fibers. In mapping class groups this points at chain or lantern type relations among
  twists, not at products of disjoint supports. Not attempted.
