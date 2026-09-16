# Outer extensions of finitely presented simple MIF groups lie in the permutational Boone--Higman class (2026-09-16)

Lane: swarm, target `decidable-groups-embed-in-outer-extensions-of-fp-simple-groups`.
This is the derivation behind `outer-extensions-of-fp-simple-mif-groups-satisfy-pbh`
(route `outer-extensions-of-fp-simple-mif-groups-pbh-proof`). Not independently
reviewed.

## 0. Summary

Let `S` be a finitely presented simple MIF group, let `Inn(S) <= B <= Aut(S)` with
`B/Inn(S)` finitely presented, and let `n >= 2`. We extend the Belk--Fournier-Facio--
Hyde--Zaremsky actor `A = Aut_S(S * F_n)` by `B`, acting on the same set
`X = Hom_S(S * F_n, S)`. The kernel of the enlarged action is exactly the copy of `S`
given by inner automorphisms of `S * F_n` by elements of `S`. The quotient is a type
(A) actor containing `B`. So `B` satisfies permutational Boone--Higman (PBH).

The only new ingredient beyond BFFHZ is Lemma 2. An endomorphism of an MIF group
given by a one-variable word map with constants is trivial or inner. Its proof is
a normal-form comparison in `S * <x> * <y>`.

Consequences:
- every outer extension `1 -> S -> I -> Q -> 1` with `S` finitely presented, simple
  and MIF, `Q` finitely presented and `Q -> Out(S)` injective lies in `B_A`;
- for a finitely generated group `G`, lying in `B_A` is equivalent to embedding in
  such an extension with an MIF kernel;
- any witness for the target statement that goes beyond PBH must use non-MIF kernels.

**Dependencies (graph ids).**
- `relative-automorphism-of-fp-simple-mif-group-has-type-a-action` (BFFHZ Theorem E):
  `A` is finitely presented, all point stabilizers of `A` on `X` are finitely
  generated, `A` has finitely many orbits on `X x X`, and the action is faithful.
- `type-a-action-gives-boone-higman-for-subgroups` (Zaremsky Corollary B).
- `fp-simple-highly-transitive-groups-satisfy-pbh` (BFFHZ Theorem C), only for the
  converse in Corollary 7.

Everything else is proved below. Transitivity of `A` on `X` is BFFHZ Lemma 2.1, and
its one-line proof is reproduced in §1.

## 1. Conventions

- **MIF.** A group `G` is *mixed identity free* (MIF) if for every `n` and every
  `1 != w in G * F_n` some `G`-homomorphism `G * F_n -> G` sends `w` to a nontrivial
  element (BFFHZ, §2, verbatim definition quoted in §9). A nontrivial MIF group is
  infinite, since a finite group `G` satisfies the law `x^{|G|} = 1`. It is centreless,
  since `[z, x]` is a mixed identity for central `z != 1`. It is nonabelian.
- **Evaluation.** For `w in S * F_n` and `t = (t_1, ..., t_n) in S^n`, write `w(t)`
  for the image of `w` under the `S`-homomorphism `x_j -> t_j`. So
  `X = Hom_S(S * F_n, S)` is identified with `S^n` via `f -> (f(x_1), ..., f(x_n))`.
- **The actor.** `A = Aut_S(S * F_n)` is the group of automorphisms of `S * F_n`
  restricting to the identity on `S`.
- **Hats.** For `beta in Aut(S)` let `hat(beta) in Aut(S * F_n)` be `beta` on `S` and
  the identity on `F_n`. Then `beta -> hat(beta)` is an injective homomorphism.
- **Inner automorphisms.** For `s in S` let `iota_s` be the inner automorphism
  `w -> s w s^-1` of `S * F_n`, and `c_s = iota_s|_S`.
- **Transitivity** (BFFHZ Lemma 2.1). Given `f, f' in X`, the `S`-automorphism
  `x_j -> f'(x_j) f(x_j)^-1 x_j` carries `f` to `f'` under precomposition. Its inverse
  is `x_j -> f(x_j) f'(x_j)^-1 x_j`. So `A` is transitive on `X`.
- **The class `B_A`.** `B_A` is the class of groups embedding in a group with a type
  (A) action, as in `boone-higman-type-a-class-closed-under-finite-extensions`. It is
  closed under subgroups by definition.
- **Type (A).** Γ acting on `Omega` is of *type (A)* when the action is faithful, Γ is
  finitely presented, point stabilizers are finitely generated, and there are
  finitely many orbits on `Omega x Omega`. Finitely many orbits on ordered pairs gives
  finitely many orbits on 2-element subsets, which is Zaremsky's formulation.

## 2. From an abstract extension to a subgroup of Aut(S)

**Lemma 1.** Let `1 -> S -> I -> Q -> 1` be exact, with `S` nonabelian simple and the
conjugation map `Q -> Out(S)` injective. Then the conjugation homomorphism
`c : I -> Aut(S)` is injective. Its image `B = c(I)` contains `Inn(S) = c(S)`, and
`B/Inn(S) ~= Q`. If `S` and `Q` are finitely presented, so is `I ~= B`.

*Proof.*
1. `ker c = C_I(S)`, and `C_I(S) ∩ S = Z(S) = 1`.
2. Let `z in C_I(S)` with image `q in Q`. Then `q` acts on `S` by `c_z = id`, so
   `q` is trivial in `Out(S)`. By injectivity `q = 1`, so `z in S ∩ C_I(S) = 1`.
3. `c` maps `S` onto `Inn(S)` and induces `I/S ~= B/Inn(S)`.
4. An extension of a finitely presented group by a finitely presented group is
   finitely presented (P. Hall). ∎

This is the observation OE1 of `outer-extension-word-problem-is-kernel-bounded`,
reproved here so the route does not depend on that node.

## 3. Word endomorphisms of MIF groups

**Lemma 2.** Let `S` be MIF and `u in S * <x>`. Suppose that `t -> u(t)` is an
endomorphism of `S`. Then `u = 1` or `u = a x a^-1` for some `a in S`, as elements of
`S * <x>`. In particular, an automorphism of `S` given by a one-variable word map with
constants is inner.

*Proof.*

**Step 1: a mixed identity.** Consider the `S`-homomorphisms
`m, i_x, i_y : S * <x> -> S * <x, y>` given by `x -> xy`, `x -> x` and `x -> y`. Put

    v = m(u) · i_y(u)^-1 · i_x(u)^-1  in  S * <x, y> .

For `(t, t') in S^2`, evaluating gives `v(t, t') = u(t t') u(t')^-1 u(t)^-1 = 1`,
because `u(·)` is a homomorphism. So `v` is a mixed identity. Since `S` is MIF,
`v = 1`, that is,

    m(u) = i_x(u) · i_y(u)   in   S * <x> * <y> .                     (*)

**Step 2: normal forms.** In a free product of groups every element has a unique
reduced expression `g_1 ... g_m`, with each `g_i` a nontrivial element of a factor
and consecutive `g_i` from different factors. Call `g_i` a *syllable*. Call it *free*
if it lies in `<x>` or `<y>`.

Write `u` in reduced form in `S * <x>`:

    u = s_0 x^{e_1} s_1 x^{e_2} ... x^{e_k} s_k ,

with `k >= 0`, all `e_i != 0`, `s_1, ..., s_{k-1} != 1`, and `s_0, s_k in S` possibly
trivial.

**Case k = 0.** Then `u = s_0`, and (*) reads `s_0 = s_0 s_0`, so `u = 1`.

**Case k >= 1.**

1. *Left side of (*).* `m(u) = s_0 (xy)^{e_1} s_1 ... (xy)^{e_k} s_k`. For `e > 0`,
   `(xy)^e` is the reduced string `x, y, x, y, ..., x, y` of `2e` free syllables. For
   `e < 0` it is `y^-1, x^-1, ..., y^-1, x^-1`. The inner `s_i` are nontrivial and
   separate consecutive blocks, and trivial `s_0`, `s_k` are simply omitted. So the
   displayed expression is reduced. It has `2 Σ|e_i|` free syllables, and the free
   syllables of block 1 end with a `<y>`-syllable (if `e_1 > 0`) or begin with one
   (if `e_1 < 0`).
2. *Right side of (*).* `i_x(u) i_y(u)` is

       s_0 x^{e_1} s_1 ... x^{e_k} (s_k s_0) y^{e_1} s_1 ... y^{e_k} s_k .

   If `s_k s_0 = 1` that syllable is omitted, and `x^{e_k}`, `y^{e_1}` are adjacent
   syllables from different factors. So this expression is reduced. It has exactly
   `2k` free syllables, and every `<x>`-syllable precedes every `<y>`-syllable.
3. *Counting.* By uniqueness of reduced forms the numbers of free syllables agree:
   `Σ|e_i| = k`. Since every `|e_i| >= 1`, all `e_i = ±1`.
4. *Order.* If `k >= 2`, the free syllables of `m(u)` contain a `<y>`-syllable from
   block 1 followed by an `<x>`-syllable from block 2. This does not happen on the
   right side, a contradiction. So `k = 1` and `u = s_0 x^e s_1` with `e = ±1`.
5. *Sign.* If `e = -1`, the first free syllable of `m(u) = s_0 y^-1 x^-1 s_1` is
   `y^-1`, while that of `i_x(u) i_y(u) = s_0 x^-1 (s_1 s_0) y^-1 s_1` is `x^-1`, a
   contradiction. So `e = 1`.
6. *Conclusion.* Now `m(u) = s_0 · x · y · s_1` has no `S`-syllable between `x` and
   `y`, while `i_x(u) i_y(u) = s_0 · x · (s_1 s_0) · y · s_1`. Uniqueness forces
   `s_1 s_0 = 1`, so `u = a x a^-1` with `a = s_0`.

The last sentence of the lemma follows: an automorphism is not the trivial
endomorphism, since `S != 1`. ∎

**Remark.** Only the two-variable case of MIF is used. Some hypothesis is needed.
For a finite nonabelian simple group every self-map is a word map with constants
(Maurer--Rhodes; not re-read here, and not used anywhere in the proof), so outer
automorphisms of such groups are word maps. The finite case is harmless for the
target statement, since there `Q` embeds in the finite group `Out(S)`.

## 4. The enlarged actor

Fix `n >= 2` and a subgroup `B <= Aut(S)`. Put

    Γ_B = { γ in Aut(S * F_n) : γ(S) = S and γ|_S in B } ,      ρ(γ) = γ|_S .

**Lemma 3.**
1. `ρ : Γ_B -> B` is a surjective homomorphism with kernel `A`, split by `hat`. So
   `Γ_B = A ⋊ hat(B)`.
2. The formula

       γ · f  =  ρ(γ) ∘ f ∘ γ^-1        (γ in Γ_B, f in X)

   defines a left action of `Γ_B` on `X`. On `A` it is `α · f = f ∘ α^-1`, the
   inverse of BFFHZ's right action by precomposition. So it has the same orbits on
   `X` and on `X x X`, the same stabilizers and the same kernel.
3. If `S` is finitely presented and MIF and `B` is finitely presented, then `Γ_B` is
   finitely presented.

*Proof.*
1. `γ(S) = S` makes `ρ` a homomorphism. Its kernel is `A` by definition, and
   `ρ(hat(β)) = β`.
2. For `s in S`, `γ^-1(s) in S`, so `f(γ^-1(s)) = γ^-1(s)` and
   `(γ·f)(s) = ρ(γ)(γ^-1(s)) = s`. Hence `γ·f in X`. Moreover
   `(γδ)·f = ρ(γ)ρ(δ) f δ^-1 γ^-1 = γ·(δ·f)`, and the identity acts trivially.
3. `A` is finitely presented by BFFHZ Theorem E (its clause (i), via their Proposition
   1.1). A semidirect product of two finitely presented groups is finitely presented.
   Take the generators and relators of both factors, together with one relation
   `b a b^-1 = w_{a,b}` for each pair of generators, where `w_{a,b}` is a word in the
   generators of `A`. ∎

## 5. The kernel

Let `K ⊴ Γ_B` be the kernel of the action on `X`, and assume `Inn(S) <= B`.

**Proposition 4.** Let `S` be MIF (and `n >= 2`, `Inn(S) <= B <= Aut(S)`).
1. `iota_s in K` for every `s in S`.
2. `K ∩ A = 1`.
3. `ρ(K) = Inn(S)`.
4. `K = { iota_s : s in S } ~= S`. If `S` is generated by `s_1, ..., s_r`, then `K` is
   generated by `iota_{s_1}, ..., iota_{s_r}`.
5. `hat(B) ∩ K = 1`, so `β -> hat(β) K` embeds `B` in `Λ_B := Γ_B / K`.

*Proof.*
1. `iota_s(S) = S` and `ρ(iota_s) = c_s in Inn(S) <= B`, so `iota_s in Γ_B`. For
   `f in X` and `w in S * F_n`:

       (iota_s · f)(w) = s f(s^-1 w s) s^-1 = s s^-1 f(w) s s^-1 = f(w) .

2. This is BFFHZ Lemma 2.2. Directly: if `α in A` acts trivially, then for each `j`
   the element `α^-1(x_j) x_j^-1` evaluates to `1` at every `t in S^n`. So it is a
   mixed identity and hence trivial, and `α = id`.
3. By item 1, `Inn(S) <= ρ(K)`. Conversely let `γ in K` and `β = ρ(γ)`. Put
   `w = γ^-1(x_1)`. For every `f in X`, `(γ·f)(x_1) = f(x_1)` reads
   `β(f(w)) = f(x_1)`. Let `π : S * F_n -> S * <x>` be the `S`-homomorphism with
   `x_1 -> x` and `x_k -> 1` for `k >= 2`, and put `u = π(w)`. For `t in S`, let
   `f_t in X` send `x_1 -> t` and `x_k -> 1` for `k >= 2`. Then `f_t(w) = u(t)`, so
   `β(u(t)) = t`, that is, `u(t) = β^-1(t)` for all `t in S`. By Lemma 2, `β^-1` is
   inner, hence so is `β`.
4. By item 2, `ρ|_K` is injective, and by item 3 its image is `Inn(S)`. The subgroup
   `{iota_s}` of `K` already maps onto `Inn(S)`, so it is all of `K`. The map
   `s -> iota_s` is an isomorphism `S -> K` (injective because `S * F_n` is
   centreless), which gives the generators.
5. If `hat(β) in K`, then for every `f`,
   `(hat(β)·f)(x_1) = β(f(hat(β)^-1(x_1))) = β(f(x_1))` must equal `f(x_1)`. Since
   `f(x_1)` ranges over `S`, `β = id`. ∎

Note that item 5 does not use MIF. Items 2 and 3 are the only places where MIF
enters.

## 6. The type (A) action

**Theorem 5.** Let `S` be a finitely presented simple MIF group. Let
`Inn(S) <= B <= Aut(S)` with `B/Inn(S)` finitely presented, and let `n >= 2`. Then
`Λ_B = Γ_B / K` acts on `X = Hom_S(S * F_n, S)` with type (A), and `B` embeds in
`Λ_B`. Hence `B ∈ B_A`. By Zaremsky Corollary B, every subgroup of `B` has solvable
word problem and embeds in a finitely presented simple group.

*Proof.* `B` is finitely presented as an extension of `Inn(S) ~= S` by `B/Inn(S)`.
1. **Faithful.** `K` is the kernel.
2. **Finitely presented.** `Γ_B` is finitely presented (Lemma 3.3), and `K` is
   generated by finitely many elements (Proposition 4.4). So `Λ_B` is obtained from a
   finite presentation by adding finitely many relators.
3. **Finitely generated stabilizers.** Fix `f in X`.
   - *Surjectivity.* Consider `ρ : Stab_{Γ_B}(f) -> B`. Given `β in B`, put
     `f' = hat(β)·f`. By transitivity (§1) there is `α in A` with `α·f' = f`. Then
     `α hat(β) in Stab_{Γ_B}(f)` and `ρ(α hat(β)) = β`. So `ρ` is surjective.
   - *Kernel.* The kernel is `Stab_A(f)`, which is finitely generated by Theorem E,
     clause (ii).
   - *Conclusion.* So `Stab_{Γ_B}(f)` is an extension of a finitely generated group by
     the finitely generated group `B`, hence finitely generated. Since `K` lies in every
     stabilizer, `Stab_{Λ_B}(f) = Stab_{Γ_B}(f) / K` is finitely generated.
4. **Finitely many orbits of pairs.** `A ∩ K = 1`, so `A` embeds in `Λ_B` and acts
   there as before. By Theorem E, clause (iii), `A` has finitely many orbits on
   `X x X`, and every `Λ_B`-orbit is a union of `A`-orbits.

Proposition 4.5 gives `B <= Λ_B`. Apply `type-a-action-gives-boone-higman-for-subgroups`. ∎

In the concrete group `Λ_B`, the relation `iota_s ≡ 1` identifies `hat(c_s)` with
`τ_s^-1`, where `τ_s in A` is the translation-conjugation `x_j -> s x_j s^-1` (indeed
`iota_s = hat(c_s) ∘ τ_s`). So `Λ_B` is an extension `1 -> A -> Λ_B -> B/Inn(S) -> 1`.
Its `A`-part is BFFHZ's actor. The outer part `B/Inn(S)` is glued on through `hat`,
with the inner part of `B` absorbed into `A`.

**Alternative derivation of Theorem 5 through a committed node.** Put `Γ <= Sym(X)`
for the image of `A`, and `Q <= Sym(X)` for the image of `hat(B)`.
1. `hat(B)` normalizes `A` inside `Γ_B`, so `Q` normalizes `Γ`. By Theorem E and
   Proposition 4.2, `Γ ~= A` is a faithful type (A) actor on `X`.
2. By Proposition 4.5, `β -> image of hat(β)` is an isomorphism `B -> Q`. So `Q` is
   finitely generated.
3. Under this isomorphism `Q ∩ Γ` corresponds to `Inn(S)`.
   - If the image of `hat(β)` equals that of some `α in A`, then
     `hat(β) α^-1 in K`, so `β = ρ(hat(β) α^-1) in ρ(K) = Inn(S)` (Proposition 4.3).
   - Conversely, `hat(c_s)` and `τ_s^-1` have the same image, since
     `iota_s = hat(c_s) τ_s in K`.
4. So `Q/(Q ∩ Γ) ~= B/Inn(S)` is finitely presented. Then
   `normalizer-image-of-type-a-actor-is-type-a` says `ΓQ = Λ_B` acts with type (A).

This derivation replaces Lemma 3.3 and the counting in Theorem 5 by that node. It
still needs Proposition 4.3, and so Lemma 2, to compute `Q ∩ Γ`. So the new input is
the same either way. The route file uses the self-contained proof above.

## 7. Corollaries

**Corollary 6 (outer extensions).** Let `1 -> S -> I -> Q -> 1` be exact, with `S`
finitely presented, simple and MIF, `Q` finitely presented, and `Q -> Out(S)`
injective. Then `I ∈ B_A`. So every subgroup of `I` has solvable word problem and
embeds in a finitely presented simple group.

*Proof.* By Lemma 1, `I ~= B = c(I)` with `Inn(S) <= B` and `B/Inn(S) ~= Q` finitely
presented. Apply Theorem 5. ∎

**Corollary 6' (subgroups of Aut(S)).** Let `S` be finitely presented, simple and MIF.
Let `H <= Aut(S)` be such that the image of `H` in `Out(S)` lies in a finitely
presented subgroup `P <= Out(S)`. Then `H ∈ B_A`. In particular, if `Out(S)` is
finitely presented, then `Aut(S) ∈ B_A`.

*Proof.* Let `B` be the preimage of `P` in `Aut(S)`. Then `Inn(S) <= B`,
`B/Inn(S) = P`, and `H <= B ∈ B_A`. ∎

**Corollary 6'' (automorphisms that extend to an MIF overgroup).** Let
`1 -> S -> I -> Q -> 1` be exact, with `S` nonabelian simple and `Q -> Out(S)`
injective. Suppose `S <= M` with `M` finitely presented, simple and MIF. Suppose
also there is a homomorphism `ψ : I -> Aut(M)` such that `ψ(i)` preserves `S` and
restricts to conjugation by `i` there. If the image of `ψ(I)` in `Out(M)` lies in a
finitely presented subgroup, then `I ∈ B_A`.

*Proof.* If `ψ(i) = id`, then `i` centralizes `S`, so `i = 1` by Lemma 1, step 2. So
`ψ` is injective. Apply Corollary 6' to `ψ(I) <= Aut(M)`. ∎

So a witness beyond PBH also needs a kernel whose outer automorphisms do not extend
in this way to any finitely presented simple MIF overgroup with a finitely presented
outer image. If `ψ(s)` is conjugation by `s` in `M` for `s in S`, the outer image is
a quotient of `Q`. For example, when `Q` is Thompson's `F`, all its quotients are
finitely presented (every proper quotient of `F` is abelian; standard, not re-read).

**Corollary 7 (per-group equivalence).** For a finitely generated group `G` the
following are equivalent:
- (a) `G ∈ B_A`, i.e. `G` satisfies PBH;
- (b) `G` embeds in an extension `I` as in Corollary 6, i.e. an outer extension with a
  finitely presented simple MIF kernel.

*Proof.*
- (b) ⟹ (a) is Corollary 6 together with closure of `B_A` under subgroups.
- (a) ⟹ (b). BFFHZ Theorem C, (i) ⟹ (iv) (`fp-simple-highly-transitive-groups-satisfy-pbh`),
  embeds `G` in a finitely presented simple MIF group `M`. It is infinite and
  nonabelian (§1). Take `S = M` and `Q = 1`. ∎

**Corollary 8 (what the target statement can add).** Suppose a finitely generated
group `G` with solvable word problem embeds in an outer extension
`1 -> S -> I -> Q -> 1` as in `decidable-groups-embed-in-outer-extensions-of-fp-simple-groups`,
but `G ∉ B_A`. Then:
1. `S` is not MIF (Corollary 6), and `S` is infinite: if `S` is finite then `Q`
   embeds in the finite group `Out(S)`, so `I` is finite, and a finite group acting
   on itself by left multiplication is a type (A) actor;
2. if `S ∈ B_A`, then `Q` is infinite. Indeed, if `Q` were finite then `S` would have
   finite index in `I`, and `B_A` is closed under finite-index overgroups
   (`boone-higman-type-a-class-closed-under-finite-extensions`, item 2).

So the MIF case of the target is exactly PBH. The target can separate from PBH only
through infinite non-MIF finitely presented simple kernels. For kernels already in
`B_A`, it must also use infinite finitely presented groups of outer automorphisms.

By BFFHZ Remark 3.5 (text in §9), for finitely generated simple groups highly
transitive implies MIF. The highly transitive finitely presented simple groups listed
there are Thompson's `V`, finitely presented commutator subgroups of
Röver--Nekrashevych groups, twisted Brin--Thompson groups and Burger--Mozes groups.
Every outer extension of these by a finitely presented group of outer automorphisms is
in `B_A`. The graph already records this for the twisted Brin--Thompson inputs placed
in the actor (target, Attempt 2). Corollary 6 removes the restriction to inputs placed
in the actor.

## 8. Non-MIF kernels: the exact residue

Drop MIF. Let `S` be finitely presented and infinite simple, with
`Inn(S) <= B <= Aut(S)`, `B/Inn(S)` finitely presented, and `n >= 2`. Keep `Γ_B`, the
action, `K` and `Λ_B`. Put `K_A = K ∩ A` (the kernel of BFFHZ's action) and
`W = ρ(K) ⊴ B`.

**What survives without MIF.**
- `iota_s ∈ K`, so `Inn(S) <= W` (Proposition 4.1).
- `hat(B) ∩ K = 1`, so `B` still embeds in `Λ_B` (Proposition 4.5).
- `Γ_B` is finitely presented. `A` is finitely presented by BFFHZ Proposition 1.1
  ("If G is finitely presented and has trivial center, then Aut_G(G*F_n) is finitely
  presented").
- Stabilizers of `Λ_B` are finitely generated, by the argument of Theorem 5.3 with
  BFFHZ Lemma 2.1 and Proposition 2.6 ("If G is finitely generated then Stab(φ₀) is
  finitely generated").
- `Λ_B` has finitely many orbits of pairs, by BFFHZ Proposition 2.3 ("Suppose G is an
  infinite simple group, and n≥2. Then the action ... is highly transitive").

So `Λ_B` is a type (A) actor containing `B` iff `Λ_B` is finitely presented, iff `K` is
finitely normally generated in `Γ_B`.

These three BFFHZ statements were read from the arXiv v2 TeX source on 2026-09-16.
They are not imported as graph claims, apart from 2.3 and 2.6, which sit in
`relative-automorphism-action-is-highly-transitive`. So this section is a remark and
is not part of the claim.

**Proposition 9.** Under these hypotheses `K` is finitely normally generated in `Γ_B`,
and hence `B ∈ B_A`, provided:
- (a) `K_A` is finitely normally generated in `A`, i.e. `A/K_A` is finitely presented.
  This is BFFHZ Question 3.2 for `S`.
- (b) `W/Inn(S)` is finitely normally generated in `B/Inn(S)`.

*Proof.*
1. **Generators.** `K_A` is normal in `Γ_B`, being the intersection of two normal
   subgroups. Choose:
   - `a_1, ..., a_p` normally generating `K_A` in `A`;
   - generators `s_1, ..., s_r` of `S`;
   - `k_1, ..., k_m ∈ K` whose images `ρ(k_i) Inn(S)` normally generate
     `W/Inn(S)` in `B/Inn(S)`.
2. **The subgroup `N`.** Let `N` be the normal closure in `Γ_B` of all the `a_i`,
   `iota_{s_j}` and `k_i`. Then `N <= K` and `N >= K_A`.
3. **Its image.** Since `ρ` is onto, `ρ(N)` is the normal closure in `B` of the
   `c_{s_j}` and the `ρ(k_i)`. That is the normal closure of `Inn(S)` together with
   the `ρ(k_i)`, which is `W`.
4. **Conclusion.** So `ρ(N) = ρ(K)` and `N` contains `ker(ρ|_K) = K_A`, hence
   `N = K`. ∎

**Where this dies.**
- (a) is open for every finitely presented simple non-MIF group. BFFHZ, after
  Question 3.2: "for G non-MIF and n≥2 it is definitely non-trivial, so it is unclear
  what to expect, even for example for Thompson's group T". The graph's refutation
  `bffhz-computable-core-fp-upgrade-is-false` concerns cores that are only computably
  presented, so it does not touch (a).
- (b) concerns the *word automorphisms* in `B`. Lemma 2 kills them for MIF kernels.
  For non-MIF infinite kernels nothing is known here. Normal subgroups of finitely
  presented groups need not be finitely normally generated, but no example of a
  bad `W` was found.
- When (a) holds, `S` itself already lies in `B_A` (BFFHZ, text after Question 3.2:
  the translation copy of `G` meets the kernel trivially). By Corollary 8.2 the
  proposition then adds something only when `Q` is infinite.

**Relation to type [A_2].** Without MIF, the action of `Γ_B` on `X` is of type `[A_2]`
in the sense of Fournier-Facio--Wu--Zaremsky (arXiv:2603.24687v2, as recorded in
`a2-kernel-removal-iff-image-satisfies-pbh`): `Γ_B` is finitely presented, stabilizers
are finitely generated, and pair orbits are finite. Its kernel is `K`. By that node,
the kernel is removable iff `Λ_B` lies in `B_A`, and then `B <= Λ_B` lies in `B_A`.
Proposition 9 gives one sufficient condition in terms of `S` and `B`. Its hypothesis
(a) is the case `B = Inn(S)` of the same question.

## 9. Literature and verification

**Primary source read in full for the cited statements.** Belk--Fournier-Facio--Hyde--
Zaremsky, *Boone-Higman embeddings of Aut(F_n) and mapping class groups of punctured
surfaces*, arXiv:2503.21882v2 (submitted 2025-03-27, revised 2025-04-14). The arXiv
e-print TeX source (`main.tex`) was downloaded and read on 2026-09-16.

Numbering: `\newtheorem{theorem}{Theorem}[section]`, with all environments on one
counter. The introduction is `\section*`, and the numbered sections are §1 "Groups
of G-automorphisms", §2 "The action" and §3 "Proof of the main results". The numbers
below were read off this counter. Quotes are verbatim, with TeX macros spelled out.

- **MIF (§2, before Lemma 2.2).** "Recall that a group G is called mixed
  identity-free (MIF) if for all n and all 1≠w∈G*F_n, there exists a G-homomorphism
  φ: G*F_n→G such that φ(w)≠1."
- **Proposition 1.1.** "If G is finitely presented and has trivial center, then
  Aut_G(G*F_n) is finitely presented." Their proof passes through Carette's
  Theorem 4.1 for `Aut_i(G*F_n)`, which was not re-read here.
- **Lemma 2.1.** "The action of Aut_G(G*F_n) on Hom_G(G*F_n,G) is transitive." The
  proof uses the automorphism "that fixes G and sends each x_i to
  ψ(x_i)(φ(x_i)^{-1})x_i".
- **Lemma 2.2.** "Suppose that G is MIF. Then the action of Aut_G(G*F_n) on
  Hom_G(G*F_n,G) is faithful." It is followed by: "We reiterate that this is the
  only place in all the analysis of the action where we need G to be MIF."
- **Proposition 2.3.** "Suppose G is an infinite simple group, and n≥2. Then the
  action of Aut_G(G*F_n) on Hom_G(G*F_n,G) is highly transitive."
- **Observation 2.4.** "When n=1, the action of Aut_G(G*F_1) on Hom_G(G*F_1,G) is
  faithful for any G≠{1} with trivial center. When n≥2 and G is not MIF, the action
  is never faithful."
- **Proposition 2.6.** "If G is finitely generated then Stab(φ_0) is finitely
  generated."
- **Theorem C.** "For a finitely generated group G (with solvable word problem) the
  following are equivalent: (i) G satisfies the permutational Boone--Higman
  conjecture, i.e., it embeds in a group admitting an action of type (A). (ii) G
  embeds in a finitely presented (simple) twisted Brin--Thompson group. (iii) G embeds
  in a finitely presented simple group that is highly transitive. (iv) G embeds in a
  finitely presented simple group that is MIF."
- **Theorem E.** "For any finitely presented simple MIF group G, the group
  Aut_G(G*F_n) (n≥2) admits an action of type (A), and hence satisfies the
  (permutational) Boone--Higman conjecture." Its proof in §3 cites Lemma 2.2,
  Proposition 1.1, Proposition 2.6 with Lemma 2.1, and Proposition 2.3. So the four
  clauses used in Lemma 3.3 and Theorem 5 are exactly the clauses of Theorem E.
- **Question 3.2.** "For G a finitely presented simple group and n≥2, is the quotient
  of Aut_G(G*F_n) by the kernel of its action on Hom_G(G*F_n,G) finitely presented?"
  The following text says: "for G non-MIF and n≥2 it is definitely non-trivial, so it
  is unclear what to expect, even for example for Thompson's group T". It also says:
  "the copy of G inside Aut_G(G*F_n) coming from translating x_1 by elements of G
  intersects the kernel of the action on Hom_G(G*F_n,G) trivially, so G still embeds
  in the quotient."
- **Remark 3.5.** "Note that for finitely generated simple groups, highly transitive
  implies MIF [Hull--Osin, Theorem 5.9] [Le Boudec--Matte Bon, Proposition A.1]".
  Highly transitive examples named there: "Thompson's group V itself, along with all
  finitely presented commutator subgroups of Röver--Nekrashevych groups V_n(G)",
  "all twisted Brin--Thompson groups", and the finitely presented simple
  Burger--Mozes groups.

The cited Hull--Osin and Le Boudec--Matte Bon results were not re-read. The
Carette presentation theorem was not re-read either.

**Novelty check.** No text in BFFHZ discusses `Aut(G)` or outer automorphisms of `G`
acting on `Hom_G(G*F_n,G)`. The only automorphism-group applications there are
`Aut(F_n)` and mapping class groups.

Graph search on 2026-09-16 found the following relevant nodes, and none states
Theorem 5 or Lemma 2:
- `normalizer-image-of-type-a-actor-is-type-a` (general enlargement lemma, used
  above as an alternative);
- `pbh-class-closed-under-relative-holomorphs`;
- `boone-higman-type-a-class-closed-under-finite-extensions`;
- `outer-extension-word-problem-is-kernel-bounded`;
- `titz-witzel-lattices-pbh-from-mif-kernels`;
- `pbh-groups-act-freely-in-relative-automorphism-actors`.

**arXiv listing checks (API metadata and abstracts, 2026-09-16).** None of these
abstracts addresses automorphism groups of MIF groups acting on `Hom_S(S*F_n,S)`, or
outer extensions of finitely presented simple groups.
- 2405.18354v2, Zaremsky, *Finite presentability of twisted Brin-Thompson groups*. Only
  metadata was checked here. Its Theorem A and Corollary B are used as recorded, with
  quotes, in `type-a-action-gives-boone-higman-for-subgroups`.
- 2603.24687v2 (2026-03-25, revised 2026-04-02), Fournier-Facio--Wu--Zaremsky,
  *Abstract twisted Brin--Thompson groups*.
- 2506.02319v2, Fournier-Facio--Kropholler--Lyman--Zaremsky, *Finiteness properties of
  stabilisers of oligomorphic actions*.
- 2509.09788v1 (2025-09-11), Hyde--Lodha, *Embeddings into highly transitive and
  mixed identity free groups*.
- 2607.26267v1 (2026-07-28), Chakraborty, *On essential freeness of actions of mixed
  identity-free groups*.
- 2609.17129v1 (2026-09-15), Le Bars--Leibtag--Vigdorovich, *Selflessness, MIF and
  opposition in groups acting on exotic buildings*.
- 2609.01868v1 (2026-09-01), *On the Self-Similarity of Permutational Wreath Products
  and Their Embedding into Finitely Presented Simple Groups* (title only).
- Titles only, from an earlier search in this session: 2306.16356v3 (*Progress around
  the Boone--Higman conjecture*), 2309.06224v3 (*Hyperbolic groups satisfy the
  Boone-Higman conjecture*), 2408.05673v2 (*On the Boone--Higman Conjecture for groups
  acting on locally finite trees*), 2405.09722v2 (Zaremsky, *Embedding finitely
  presented self-similar groups into finitely presented simple groups*).
- Abstracts only: 1605.09302v2 (Bleak--Cameron--Maissel--Navas--Olukoya, automorphisms
  of the Higman--Thompson groups `G_{n,r}`) and 1908.03816v1 (Olukoya, *Automorphisms of
  the generalised Thompson's group T_{n,r}*). These were consulted only as a possible
  source of non-MIF kernels with large `Out`. They were not used in any proof.

## 10. Weakest points

1. **Lemma 2, Step 2.** The normal-form comparison is elementary but must be checked
   syllable by syllable. The two delicate spots are the omission of trivial `s_0`,
   `s_k` or `s_k s_0`, and the claim that each block `(xy)^{±1}` contains both an
   `<x>`- and a `<y>`-syllable. Both are addressed in items 1, 2 and 4.
2. **Theorem E clauses.** Lemma 3.3 and Theorem 5 use four separate conclusions
   about `A` acting on `X`: finite presentation of `A`, faithfulness, finitely
   generated stabilizers and finitely many pair orbits. The graph import
   `relative-automorphism-of-fp-simple-mif-group-has-type-a-action` carries exactly
   these, via Zaremsky's definition of type (A). The internal BFFHZ proofs
   (Carette's presentation, the stabilizer computation) were not re-derived.
3. **Action conventions.** BFFHZ use the right action `φ -> φ ∘ α`. Lemma 3.2 converts
   it to a left action and checks that stabilizers, orbits and kernels are unchanged.
