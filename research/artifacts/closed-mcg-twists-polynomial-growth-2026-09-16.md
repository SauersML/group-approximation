# Dehn twists of closed-surface mapping class groups act polynomially on free groups

Swarm lane on `some-closed-surface-mcg-embeds-in-no-out-free-group`, 2026-09-16.
Graph nodes: claim `closed-mcg-twists-map-to-polynomially-growing-outer-autos`,
route `closed-mcg-twists-map-to-polynomially-growing-outer-autos-proof`.
Working notes and dead ends: `notes/some-closed-surface-mcg-embeds-in-no-out-swarm-2026-09-16.md`.

No novelty is claimed. The pattern (a Dehn twist is central in its centralizer and
lies in the commutator subgroup of that centralizer, so it dies under every
homomorphism to `Z` there) is the one Bridson used for semisimple actions of mapping
class groups on CAT(0) spaces. The literature search behind this artifact was
bounded; see Section 10.

## 0. Statement

**Theorem B.** Let `g ≥ 3`, `n ≥ 0`, and let `φ : MCG(S_g) → Out(F_n)` be any
homomorphism. For every simple closed curve `c ⊂ S_g`, both `φ(T_c)` and
`φ(T_c)^{-1}` lie in `PG(F_n)`.

**Corollary C.** In the same situation, if `c_1, …, c_r` are pairwise disjoint simple
closed curves, then every element of `φ(⟨T_{c_1}, …, T_{c_r}⟩)` lies in `PG(F_n)`,
and there is `N ≥ 1` with `φ(T_{c_i})^N ∈ UPG(F_n)` for every `i`.

**Theorem B′ (finite-index subgroups).** Let `g ≥ 3`, let `Γ ≤ MCG(S_g)` have finite
index, and let `φ : Γ → Out(F_n)` be any homomorphism. If `c_1, …, c_r` are pairwise
disjoint simple closed curves and `T_{c_i}^{k_i} ∈ Γ` with `k_i ≠ 0`, then every
element of `φ(⟨T_{c_1}^{k_1}, …, T_{c_r}^{k_r}⟩)` lies in `PG(F_n)`, and some positive
power of each `φ(T_{c_i}^{k_i})` lies in `UPG(F_n)`. (Section 8.)

The engine is a statement about `Out(F_n)` alone:

**Lemma A.** Let `D ≤ Out(F_n)`, let `ψ` be central in `D`, and suppose
`ψ^k ∈ [D, D]` for some `k ≥ 1`. Then `ψ ∈ PG(F_n)`.

## 1. Conventions

- `S_{h,b}` is the compact connected orientable surface of genus `h` with `b`
  boundary components; `S_g = S_{g,0}`. `MCG(Σ)` is the group of
  orientation-preserving homeomorphisms of `Σ` fixing `∂Σ` pointwise, modulo
  isotopies fixing `∂Σ` pointwise, as in Farb--Margalit, *A primer on mapping class
  groups* (Princeton, 2012; section and proposition numbers below as recalled, not
  re-read in this session).
- `T_c` is the left Dehn twist about a simple closed curve `c`. Isotopic curves give
  equal twists; `T_c = 1` if `c` bounds a disk.
- **(FM1)** For `f ∈ MCG(Σ)`, `f T_c f^{-1} = T_{f(c)}` (Farb--Margalit Fact 3.7).
- **(FM2)** For a subsurface `Σ ⊂ S` (a closed subset which is a surface), extending
  homeomorphisms by the identity induces a homomorphism `MCG(Σ) → MCG(S)` taking
  `T_c` to `T_c` (Farb--Margalit Theorem 3.18, the inclusion homomorphism). Only
  well-definedness and the twist formula are used, not injectivity.
- **(FM3) Lantern relation** (Farb--Margalit Proposition 5.1). If `P ⊂ Σ` is an
  embedded four-holed sphere with boundary curves `b_1, …, b_4`, and `x, y, z ⊂ P`
  are the three curves arranged as in the lantern (each of `x, y, z` cuts `P` into
  two pairs of pants, and the three splittings of `{b_1, …, b_4}` into pairs are
  `{b_1 b_2 | b_3 b_4}`, `{b_1 b_3 | b_2 b_4}`, `{b_1 b_4 | b_2 b_3}`), then
  `T_x T_y T_z = T_{b_1} T_{b_2} T_{b_3} T_{b_4}` in `MCG(P)`, hence in `MCG(Σ)`
  by (FM2). Only the image of this relation in the abelianization is used, so the
  order of the factors and the exact assignment of `x, y, z` to splittings do not
  matter.
- `Out(F_n)` acts on the space `B` of lines of `F_n` (BFH Section 2.2): an
  automorphism extends to a homeomorphism of `∂F_n`, inner automorphisms act
  trivially on `B`, and `θ ↦ θ_#` is a left action by homeomorphisms.
- `[D, D]` is the commutator subgroup and `D^{ab} = D/[D, D]`.

## 2. Inputs from Bestvina--Feighn--Handel

Source: M. Bestvina, M. Feighn, M. Handel, *The Tits alternative for Out(F_n) I:
Dynamics of exponentially-growing automorphisms*, Ann. of Math. 151 (2000), 517--623,
arXiv:math/9712217v2 (1 Mar 2000). Read in this session (2026-09-16) from the arXiv
PDF by text extraction, which dropped Greek letters, so the statements below restore
symbols by hand.

- **(I1) Definitions 3.1.1.** `U ⊂ B` is an *attracting neighborhood* of `λ ∈ B` for
  the action of `O` if `O_#(U) ⊂ U` and `{O^k_#(U) : k ≥ 0}` is a neighborhood basis
  for `λ` in `B`.
- **(I2) Definitions 3.1.5.** A closed subset `Λ^+ ⊂ B` is an *attracting lamination*
  for `O` if it is the closure of a single point `λ` that (1) is birecurrent; (2) has
  an attracting neighborhood for the action of some iterate of `O`; (3) is not
  carried by an `O`-periodic free factor of rank one. `L(O)` is the set of attracting
  laminations for `O`.
- **(I3) Lemma 3.1.4, second part.** If `λ ∈ B` is birecurrent, then `θ_#(λ)` is
  birecurrent for all `θ ∈ Out(F_n)`.
- **(I4) The lemma stated right after Definitions 3.1.5:** "`L(O)` is
  `O`-invariant", with the proof: `O_#(λ)` is birecurrent by Lemma 3.1.4; `O_#(V)` is
  an attracting neighborhood of `O_#(λ)` for `O^s` when `V` is one for `λ`; a
  periodic rank-one free factor carrying `O_#(λ)` pulls back to one carrying `λ`. Its
  position (between Definitions 3.1.5 and 3.1.7) makes it Lemma 3.1.6; the extraction
  printed `3.1.16`, which is also the number of a different lemma, so the number is
  unverified. Only its proof pattern is used. (Referee, 2026-09-16: an independent
  text extraction of the arXiv v2 PDF confirms that this lemma is printed as
  "Lemma 3.1.16. L(O) is O-invariant." right after Definitions 3.1.5, and that
  "Lemma 3.1.16. A generic line of Λ+ ∈ L(O) is never a circuit." appears later; the
  proof quoted above matches.)
- **(I5) Lemma 3.1.9.** If `f : G → G` is a relative train track map representing `O`
  and `H_r` is an aperiodic exponentially-growing stratum, then there is an attracting
  lamination for `O` with a generic leaf whose realization in `G` has `H_r` as the
  highest stratum crossed. (BFH: "Having proved that `L(O)` is not empty…")
- **(I6) Lemma 3.1.10(1).** If `λ` is generic for some `Λ^+ ∈ L(O)` and `f : G → G`
  is a relative train track map representing `O`, the highest stratum crossed by the
  realization of `λ` is exponentially growing.
- **(I7) Lemma 3.1.13.** `L(O)` is finite. The proof shows: if `f` is a relative train
  track map for `O` with an exponentially-growing stratum `H_r` whose transition
  matrix is not aperiodic, then after replacing `f` by `f^s` and refining the
  filtration, `H_r` divides into `s` exponentially-growing strata; so some iterate
  `O^p` is represented by an eg-aperiodic relative train track map; and
  `L(O^p) = L(O)`.
- **(I8) Section 5.1, before Theorem 5.1.8.** `O` has *polynomial growth* if some (and
  hence every) relative train track map representing `O` has no exponentially-growing
  strata; `PG(F_n)` is the set of these. `UPG(F_n)` is the set of elements of `PG(F_n)`
  with unipotent image in `GL(n, Z)`.
- **(I9) Corollary 3.3.1.** With `Stab(Λ^+) = {ψ ∈ Out(F_n) : ψ_#(Λ^+) = Λ^+}`, "there
  is a homomorphism `PF_{Λ^+} : Stab(Λ^+) → Z` such that `ψ ∈ Ker(PF_{Λ^+})` if and
  only if `Λ^+ ∉ L(ψ)` and `Λ^+ ∉ L(ψ^{-1})`."
- **(I10) Corollary 5.7.6**, as quoted in the BFH introduction: every PG subgroup
  contains a finite-index UPG subgroup.
- **(I11)** Every element of `Out(F_n)`, `n ≥ 2`, has a relative train track
  representative (Bestvina--Handel, Ann. of Math. 135 (1992), Theorem 5.12; not
  re-read).

For `n ≤ 1`, `Out(F_n)` is finite and every element has bounded growth, so all
statements are trivially true; from now on `n ≥ 2`.

## 3. Attracting laminations: finiteness, powers, naturality

**Lemma 1.** Let `ψ, θ ∈ Out(F_n)` and `p ≥ 1`.
(a) `L(ψ)` is finite.
(b) `L(ψ^p) = L(ψ)`.
(c) `L(ψ) = ∅` if and only if `ψ ∈ PG(F_n)`.
(d) `θ_#(L(ψ)) = L(θ ψ θ^{-1})`.

*Proof.* (a) is (I7).

(b) is stated in (I7); here is the check against (I2). Condition (1) does not involve
the outer automorphism. Condition (3) is the same for `ψ` and `ψ^p`, since a
conjugacy class of free factors is `ψ`-periodic iff it is `ψ^p`-periodic. For
condition (2), an iterate of `ψ^p` is an iterate of `ψ`. Conversely, let `U` be an
attracting neighborhood of `λ` for `ψ^s`. Since `ψ^s_#` is a bijection,
`ψ^s_#(U) ⊂ U` gives `ψ^{s(k+1)}_#(U) ⊂ ψ^{sk}_#(U)` for all `k`, so the sets
`ψ^{sk}_#(U)` decrease; hence `ψ^{sp}_#(U) ⊂ U`, and the subfamily
`{ψ^{spk}_#(U)}_{k ≥ 0}` of the decreasing neighborhood basis `{ψ^{sk}_#(U)}` is
again a neighborhood basis. So `U` is an attracting neighborhood of `λ` for
`(ψ^p)^s`.

(c) Suppose `ψ ∉ PG(F_n)`. By (I11) choose a relative train track map `f`
representing `ψ`; by (I8) it has an exponentially-growing stratum. By the argument
quoted in (I7), for suitable `s ≥ 1` the map `f^s` with refined filtration is a
relative train track map representing `ψ^s` in which that stratum divides into
aperiodic exponentially-growing strata. By (I5), `L(ψ^s) ≠ ∅`, and by (b),
`L(ψ) ≠ ∅`. Conversely, if `Λ^+ ∈ L(ψ)`, then by (I6) every relative train track map
representing `ψ` has an exponentially-growing stratum (the highest stratum crossed
by a generic leaf), so `ψ ∉ PG(F_n)` by (I8).

(d) This is the proof of (I4) with `θ` in place of `O`. Let `Λ^+ ∈ L(ψ)` with generic
leaf `λ`. As `θ_#` is a homeomorphism of `B`, `θ_#(Λ^+)` is the closure of
`θ_#(λ)`. (1) `θ_#(λ)` is birecurrent by (I3). (2) If `U` is an attracting
neighborhood of `λ` for `ψ^s`, then `θ_#(U)` is a neighborhood of `θ_#(λ)`,
`(θψ^sθ^{-1})_#(θ_#(U)) = θ_#(ψ^s_#(U)) ⊂ θ_#(U)`, and
`(θψ^sθ^{-1})^k_#(θ_#(U)) = θ_#(ψ^{sk}_#(U))`, which is a neighborhood basis of
`θ_#(λ)` because `θ_#` is a homeomorphism. So `θ_#(U)` is an attracting
neighborhood of `θ_#(λ)` for `(θψθ^{-1})^s`. (3) If `θ_#(λ)` were carried by a
`θψθ^{-1}`-periodic rank-one free factor `[[F]]`, then `λ` would be carried by
`θ^{-1}[[F]]`, which is `ψ`-periodic of rank one; this is excluded. Hence
`θ_#(Λ^+) ∈ L(θψθ^{-1})`. Applying this to `θ^{-1}` and `θψθ^{-1}` gives the reverse
inclusion. ∎

## 4. Transfer of a central element

**Lemma 2.** Let `D_0` be a normal subgroup of finite index `m` in a group `D`. There
is a homomorphism `V : D → D_0^{ab}` such that `V(g) = g^m [D_0, D_0]` for every
`g` in the center of `D`.

*Proof.* Choose a transversal `t_1, …, t_m` of `D_0` in `D`. For `g ∈ D` and each `i`
there are unique `σ_g(i)` and `h_i(g) ∈ D_0` with `g t_i = t_{σ_g(i)} h_i(g)`; each
`σ_g` is a permutation. Put `V(g) = ∏_i h_i(g) [D_0, D_0]`. From
`g g' t_i = g t_{σ_{g'}(i)} h_i(g') = t_{σ_g σ_{g'}(i)} h_{σ_{g'}(i)}(g) h_i(g')` we
get `h_i(g g') = h_{σ_{g'}(i)}(g) h_i(g')`, and multiplying over `i` in the abelian
group `D_0^{ab}` gives `V(g g') = V(g) V(g')`.

Let `g` be central and let `f` be the order of `g D_0` in `D/D_0`. Since `D_0` is
normal and `g` is central, `g t_i D_0 = t_i g D_0`, so `σ_g` acts on the cosets by
right multiplication by `g D_0`; all its cycles have length `f`, and there are `m/f`
of them. Iterating the cocycle identity along the cycle of `i` gives
`h_i(g^f) = h_{σ_g^{f-1}(i)}(g) ⋯ h_{σ_g(i)}(g) h_i(g)`. On the other hand
`g^f t_i = t_i g^f` with `g^f ∈ D_0`, so `h_i(g^f) = g^f`. Hence, modulo
`[D_0, D_0]`, the product of the `h_j(g)` over one cycle is `g^f`, and over all cycles
`V(g) = (g^f)^{m/f} = g^m`. ∎

## 5. Lemma A

**Lemma A.** Let `D ≤ Out(F_n)`, let `ψ ∈ D` be central in `D`, and suppose
`ψ^k ∈ [D, D]` for some `k ≥ 1`. Then `ψ ∈ PG(F_n)`.

*Proof.* Suppose not. By Lemma 1(a),(c), `L(ψ)` is finite and nonempty. For `θ ∈ D`,
Lemma 1(d) gives `θ_#(L(ψ)) = L(θψθ^{-1}) = L(ψ)`, so `D` permutes the finite set
`L(ψ)`. Let `D_0` be the kernel of this permutation action: a normal subgroup of
finite index `m` in `D`, contained in `Stab(Λ^+)` for every `Λ^+ ∈ L(ψ)`. Fix one
`Λ^+ ∈ L(ψ)`.

Put `χ = ψ^m`; it lies in `D_0` because `D/D_0` has order `m`. Let `V` be as in
Lemma 2. Since `V` is a homomorphism to an abelian group and `ψ^k ∈ [D, D]`,
`V(ψ^k) = 1`. Since `ψ` is central, `V(ψ^k) = V(ψ)^k = ψ^{mk}[D_0, D_0]`. Therefore
`χ^k ∈ [D_0, D_0]`.

The restriction of `PF_{Λ^+}` (I9) to `D_0` is a homomorphism `D_0 → Z`, so it kills
`[D_0, D_0]`; hence `k · PF_{Λ^+}(χ) = PF_{Λ^+}(χ^k) = 0` and `PF_{Λ^+}(χ) = 0`. By
(I9), `Λ^+ ∉ L(χ)`. But `L(χ) = L(ψ^m) = L(ψ)` by Lemma 1(b), and `Λ^+ ∈ L(ψ)`.
Contradiction. ∎

**Remark.** Lemma A uses no finiteness assumption on `D`. What it uses is that
`PF_{Λ^+}` restricts to a homomorphism on a finite-index subgroup of `D` that is
nonzero on a positive power of `ψ`. Centrality is used twice: it makes `D` permute
`L(ψ)`, and it makes the transfer of `ψ` a power of `ψ`.

## 6. Boundary twists are central commutator products in genus at least two

**Lemma 3 (change of coordinates rel boundary).** Let `Σ` be a compact connected
orientable surface and `α, β ⊂ int Σ` nonseparating simple closed curves. There is
an orientation-preserving homeomorphism `f` of `Σ`, equal to the identity on `∂Σ`,
with `f(α) = β`. Consequently `T_α` and `T_β` are conjugate in `MCG(Σ)` and have the
same image in `MCG(Σ)^{ab}`.

*Proof.* Let `Σ_α`, `Σ_β` be the surfaces obtained by cutting along `α`, `β`, with
new boundary components `α', α''` and `β', β''`. Both are connected (the curves are
nonseparating), orientable, with the same Euler characteristic `χ(Σ)` and the same
number `b + 2` of boundary components, hence of the same genus. By the classification
of surfaces there is an orientation-preserving homeomorphism `F : Σ_α → Σ_β` taking
`α' ↦ β'`, `α'' ↦ β''` and each old boundary component `∂_j` to itself (any
permutation of boundary components is realized). Orientation-preserving
homeomorphisms of a circle are isotopic to the identity, so after modifying `F` in
collars of the boundary we may assume `F = id` on each `∂_j` and
`F|_{α''} = ι_β ∘ F|_{α'} ∘ ι_α^{-1}`, where `ι_α : α' → α''` and
`ι_β : β' → β''` are the gluing maps (both reverse boundary orientation, so the
right-hand side and `F|_{α''}` both preserve it). Then `F` descends to the required
`f`. The conjugacy is (FM1). ∎

**Lemma 4.** Let `Σ = S_{h,b}` with `h ≥ 2`, `b ≥ 1`, and let `∂` be a boundary
component. Then `T_∂` is central in `MCG(Σ)` and `T_∂ ∈ [MCG(Σ), MCG(Σ)]`.

*Proof.* *Centrality.* Let `c` be a curve parallel to `∂` in a collar. For `f`
fixing `∂Σ` pointwise, `f(c)` cobounds an annulus with `∂`, so `f(c)` is isotopic to
`c` and `f T_c f^{-1} = T_{f(c)} = T_c` by (FM1); and `T_∂ = T_c`.

*A lantern with six nonseparating curves.* Let `P = S_{0,4}` with boundary curves
`b_1, …, b_4`, and `R = S_{h-2, b+2}` (defined since `h ≥ 2`) with boundary
components `c_2, c_3, c_4, d_2, …, d_b`. Glue `b_i` to `c_i` for `i = 2, 3, 4` by
orientation-reversing homeomorphisms. The result `X` is connected and orientable, has
boundary components `b_1, d_2, …, d_b` (so `b` of them), and
`χ(X) = χ(P) + χ(R) = −2 + (2 − 2(h − 2) − (b + 2)) = 2 − 2h − b`, so `X ≅ S_{h,b}`,
by a homeomorphism taking `b_1` to `∂`. Transport `P` into `Σ` and push it slightly
into the interior, so that `b_1` is parallel to `∂`. Let `x, y, z ⊂ P` be the lantern
curves (FM3).

Each of `b_2, b_3, b_4, x, y, z` is nonseparating in `X`. Cutting `X` along `b_2`
leaves `P ∪ R` glued along `b_3, b_4`: connected. Cutting along `x`, which splits `P`
into pairs of pants `Q_1 ⊃ {b_1, b_2}` and `Q_2 ⊃ {b_3, b_4}`, leaves `Q_1 ∪ Q_2 ∪ R`
with `Q_1` glued to `R` along `b_2` and `Q_2` glued along `b_3, b_4`: connected, since
`R` is connected. The same argument applies to `b_3, b_4` and to `y`, `z`, because
each pair of pants obtained by cutting `P` along `y` or `z` contains at least one of
`b_2, b_3, b_4`.

*Abelianize.* Write `[·]` for classes in `MCG(Σ)^{ab}`, additively. By Lemma 3 the six
nonseparating curves give one common class `t`. The lantern relation gives
`3t = [T_{b_1}] + 3t`, so `[T_∂] = [T_{b_1}] = 0`. ∎

(For `h = 1` the conclusion fails: `MCG(S_{1,1})^{ab} ≅ Z`, and the boundary twist
`(T_a T_b)^6` has class `12`. This is where genus at least three enters Theorem B.)

## 7. Proof of Theorem B

Let `c ⊂ S_g`, `g ≥ 3`. If `c` bounds a disk, `T_c = 1`. Otherwise choose a subsurface
`Σ ⊂ S_g` and a boundary component `∂` of `Σ` with `∂` isotopic to `c`:

- if `c` is nonseparating, `Σ` is the complement of an open annular neighborhood of
  `c`, so `Σ ≅ S_{g-1,2}` and `g − 1 ≥ 2`;
- if `c` is separating and essential, the two sides have genera `h, g − h ≥ 1` with
  sum `g ≥ 3`, so one side `Σ ≅ S_{h,1}` has `h ≥ 2`.

Let `ι : MCG(Σ) → MCG(S_g)` be the inclusion homomorphism (FM2) and `C = ι(MCG(Σ))`.
Then `ι(T_∂) = T_c`. By Lemma 4, `T_∂` is central in `MCG(Σ)` and lies in its
commutator subgroup, so `T_c` is central in `C` and `T_c ∈ [C, C]`; the same holds for
`T_c^{-1}`. Put `D = φ(C) ≤ Out(F_n)`. Then `φ(T_c)^{±1}` is central in `D` and lies in
`[D, D]`. Lemma A with `k = 1` gives `φ(T_c)^{±1} ∈ PG(F_n)`. ∎

## 8. Corollary C: multitwists

**Lemma 5.** Let `ψ_1, …, ψ_r ∈ Out(F_n)` commute pairwise, with `ψ_i` and `ψ_i^{-1}` in
`PG(F_n)` for each `i`. Then every element of `A = ⟨ψ_1, …, ψ_r⟩` lies in `PG(F_n)`.

*Proof.* Let `a = ∏ ψ_i^{k_i} ∈ A` and suppose `a ∉ PG(F_n)`. By Lemma 1, `L(a)` is
finite and nonempty, and each `ψ_i` commutes with `a`, so permutes `L(a)` by Lemma
1(d). Choose `p ≥ 1` such that every `ψ_i^p` fixes every element of `L(a)`, and fix
`Λ^+ ∈ L(a)`. Then `ψ_i^p ∈ Stab(Λ^+)`. By Lemma 1(b),(c),
`L(ψ_i^p) = L(ψ_i) = ∅` and `L(ψ_i^{-p}) = L(ψ_i^{-1}) = ∅`, so
`PF_{Λ^+}(ψ_i^p) = 0` by (I9). Hence `a^p = ∏ (ψ_i^p)^{k_i}` lies in `Stab(Λ^+)` and
`PF_{Λ^+}(a^p) = Σ k_i PF_{Λ^+}(ψ_i^p) = 0`. By (I9), `Λ^+ ∉ L(a^p) = L(a)`: a
contradiction. ∎

*Proof of Corollary C.* The twists `T_{c_i}` commute (disjoint supports), so the
`φ(T_{c_i})` commute and satisfy the hypotheses of Lemma 5 by Theorem B. So
`A = φ(⟨T_{c_1}, …, T_{c_r}⟩)` is a PG subgroup. By (I10) it contains a finite-index
UPG subgroup `A_0`; if `φ(T_{c_i})^{N_i} ∈ A_0`, take `N = N_1 ⋯ N_r`. ∎

**Lemma 6 (powers).** For `ψ ∈ Out(F_n)` and `p ≥ 1`, `ψ ∈ PG(F_n)` iff
`ψ^p ∈ PG(F_n)`.

*Proof.* Lemma 1(b),(c): `L(ψ^p) = L(ψ)`, and each is empty iff the corresponding
element is in `PG(F_n)`. ∎

*Proof of Theorem B′.* Fix `c = c_i` and `k = k_i`; we may assume `c` does not bound a
disk (otherwise `T_c = 1`). Choose `Σ ⊂ S_g`, `∂` and `ι` as in Section 7, and put
`C = ι(MCG(Σ))`. By Lemma 4, `T_c = ι(T_∂)` is central in `C` and lies in `[C, C]`.
Since `Γ` has finite index in `MCG(S_g)`, `Γ ∩ C` has finite index in `C`; let `N` be
its normal core in `C`, the intersection of the `C`-conjugates of `Γ ∩ C`, which is
normal of some finite index `m` in `C` and contained in `Γ`. Let `V : C → N^{ab}` be
the transfer of Lemma 2. As `N^{ab}` is abelian and `T_c ∈ [C, C]`, `V(T_c) = 1`; as
`T_c` is central in `C`, `V(T_c) = T_c^m [N, N]`. So `T_c^m ∈ [N, N] ≤ N`, and `T_c^m`
is central in `N`. Put `D = φ(N)`. Then `φ(T_c^m)^{±1}` is central in `D` and lies in
`[D, D]`, so `φ(T_c^m)^{±1} ∈ PG(F_n)` by Lemma A. Now
`φ(T_c^k)^{±m} = φ(T_c^m)^{±k}` (both sides are defined, since `T_c^k ∈ Γ` and
`T_c^m ∈ Γ`). If `k > 0`, the right side is a positive power of `φ(T_c^m)^{±1}`, which
is in `PG(F_n)` by Lemma 6, so `φ(T_c^k)^{±1} ∈ PG(F_n)` by Lemma 6 again. If `k < 0`,
the same holds with `φ(T_c^m)^{∓1}` in place of `φ(T_c^m)^{±1}`, since
`φ(T_c^m)^{±k} = (φ(T_c^m)^{∓1})^{|k|}`.

So `ψ_i = φ(T_{c_i}^{k_i})` satisfy `ψ_i^{±1} ∈ PG(F_n)`, and they commute because the
`T_{c_i}` do. Lemma 5 gives that `φ(⟨T_{c_1}^{k_1}, …, T_{c_r}^{k_r}⟩)` is a PG subgroup,
and (I10) gives the UPG powers as in the proof of Corollary C. ∎

**Remark.** Theorem B′ needs no statement about first Betti numbers of finite-index
subgroups of mapping class groups: the transfer from the full subsurface group `C`
already puts a power of the twist in the commutator subgroup of the core `N`.

## 9. What this gives for Zaremsky Problem 3.10(b)

- **A necessary condition, not an obstruction.** Any embedding
  `MCG(S_g) ↪ Out(F_n)`, `g ≥ 3`, must send every Dehn twist, and every multitwist
  group, into polynomially growing outer automorphisms, with a common power in
  `UPG(F_n)`. Growth alone cannot rule out an embedding: the bordered group
  `MCG(S_{g,1})` embeds in `Aut(F_{2g})` by Dehn--Nielsen--Baer and hence in
  `Out(F_{2g+1})`, and there Dehn twists act as Dehn twist automorphisms (linear
  growth); the lantern argument applies verbatim to that group.
- **Finite-index subgroups.** By item 2 of
  `aut-free-embeddability-passes-to-finite-index-overgroups`, embeddability in some
  `Aut(F_n)` is shared by `MCG(S_g)` and all its finite-index subgroups, so an
  obstruction for Aut hosts must hold for every finite-index subgroup. Theorem B′ is
  the version of Theorem B with that robustness.
- **Genus two is consistent.** Lemma 4 fails for `h = 1`, and `MCG(S_2)` has
  abelianization `Z/10`; closed genus-two mapping class groups do embed
  (`low-genus-closed-mcgs-embed-in-aut-free-groups`).
- **Where an obstruction would have to live.** The centralizer of `φ(T_c)` contains
  `φ(MCG(S_{g-1,2}))`, and `φ(T_c)` has a UPG power. An obstruction would need
  structure of centralizers of UPG elements in `Out(F_n)` (Kolchin-type invariant free
  factor systems, canonical splittings of linearly growing elements) combined with the
  rank bound. See the notes file for the tentative plan; nothing there is claimed.

## 10. Literature consulted (2026-09-16)

- Bestvina--Feighn--Handel, arXiv:math/9712217v2: Definitions 3.1.1, 3.1.5, Lemmas
  3.1.4, 3.1.6 (number inferred), 3.1.9, 3.1.10, 3.1.13, Corollary 3.3.1, Section 5.1
  definition of `PG`; read from the PDF.
- M. R. Bridson, R. D. Wade, *Actions of higher-rank lattices on free groups*,
  arXiv:1004.3222v2 (13 Apr 2011): Corollary 2.9 (every nontrivial subgroup of `IA_n`
  maps onto `Z`) and Section 3 (fully irreducible images excluded via
  quasi-homomorphisms); read. Mapping class groups appear there only as targets, not
  as sources of homomorphisms.
- M. Korkmaz, *Low-dimensional linear representations of mapping class groups*,
  arXiv:1104.4816v2 (2 Aug 2011), Theorem 5: for `g ≥ 3` and `n ≤ 2g − 1` every
  homomorphism from `MCG(S_g)` to `Aut(F_n)` or `Out(F_n)` is trivial; read.
- M. R. Bridson, K. Vogtmann, *Automorphism groups of free groups, surface groups and
  free abelian groups*, arXiv:math/0507612v1 (29 Jul 2005), Questions 15--17; read.
- Bridson's theorem on semisimple actions of mapping class groups on CAT(0) spaces
  (Dehn twists act elliptically in genus at least three) is the template; the paper
  was not re-read in this session.
- Farb--Margalit, *A primer on mapping class groups*: statements (FM1)--(FM3) as
  recalled; not re-read.

No source found in this bounded search states Theorem B. WebSearch was exhausted in
this session, so the novelty search is incomplete; no novelty is claimed.

## 11. Where a referee should look

1. Lemma 1(c), direction `ψ ∉ PG ⇒ L(ψ) ≠ ∅`: it uses the internal step of the proof
   of BFH Lemma 3.1.13 (passing to `f^s` turns every exponentially-growing stratum
   into aperiodic exponentially-growing strata) together with Lemma 3.1.9.
2. Lemma 1(d): naturality of "carried by a periodic rank-one free factor" under
   `θ_#`, and that `θ_#` is a homeomorphism of the non-Hausdorff space `B`.
3. (I9) is applied to `χ = ψ^m` restricted to `D_0 ≤ Stab(Λ^+)`; `PF_{Λ^+}` is defined on
   all of `Stab(Λ^+)`, so the restriction is a homomorphism.
4. Lemma 4: the gluing construction and the nonseparation of the six lantern curves.
5. Theorem B′: the transfer is taken from `C` to the core `N` of `Γ ∩ C`, not from
   `Γ`; the only facts used are that `T_c` is central in `C` and lies in `[C, C]`.
