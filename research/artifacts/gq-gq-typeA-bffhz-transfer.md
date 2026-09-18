# BFFHZ type (A) method: transfer to GL_n(Q), and where it breaks

Lane `gq-typeA-bffhz`, 2026-09-17. Target: `gl-n-q-embeds-in-fp-simple-group`.

## 1. The BFFHZ mechanism (arXiv:2503.21882v2, read from the arXiv HTML page)

Quoted statements:
- **Theorem E:** "For any finitely presented simple MIF group G, the group Aut_G(G∗F_n) (n≥2) admits an action
  of type (A), and hence satisfies the (permutational) Boone–Higman conjecture." The action is precomposition on
  `Hom_G(G * F_n, G) ≅ G^n`.
- **Proposition 1.1:** "If G is finitely presented and has trivial center, then Aut_G(G∗F_n) is finitely
  presented."
- **Proposition 2.3:** "Suppose G is an infinite simple group, and n≥2. Then the action of Aut_G(G∗F_n) on
  Hom_G(G∗F_n,G) is highly transitive."
- **Proposition 2.6:** "If G is finitely generated then Stab(ϕ₀) is finitely generated." Faithfulness is where MIF
  is used.
- **Aut(F_n):** "Fix some finitely presented simple MIF group, for instance Thompson's group V. Note that Aut(Fn)
  embeds in AutV(V∗Fn), which admits an action of type (A) by Theorem E."
- **Corollary D:** finitely presented simple twisted Brin–Thompson groups are universal among finitely presented
  simple MIF groups, since `M <= Aut_M(M * F_2)`.
- **Corollary F:** permutational Boone–Higman is closed under free products, since `Aut_G(G * F_n)` contains
  `G * G`.

So the method has three inputs: a finitely presented simple MIF group `M`, the free letters, and the automorphisms
mixing them. Aut(F_n) comes entirely from the free letters, and the free letters are residually finite (Aut(F_n)
is residually finite, by Baumslag).

## 2. Transfer to GL_n(Q)

Trivial part: `M <= Aut_M(M * F_m)`. If `M` already contains `GL_n(Q)`, nothing is gained, since `M` is
finitely presented and simple.

Non-trivial part, landed as `bffhz-closures-cannot-create-gl-n-q` with the lemma
`gl-n-q-fixes-a-vertex-in-free-splittings`:
- **Fixed-point lemma.** `GL_n(Q)`, `SL_n(Q)`, `Aff(Q)`, `U_3(Q)` and `(Q,+)` fix a vertex in every tree action
  with trivial edge stabilizers.
  - Divisible elements are elliptic, because translation lengths are integers.
  - A locally cyclic divisible group has a single common fixed vertex.
  - A torus element links the root subgroups.
- **Free products.** Corollary F never creates any of these groups.
- **Mapping tori and ascending HNN extensions over `M * F_m`**
  (`mif-free-product-automorphism-ascending-hnn-is-pbh`). They contain `SL_n(Q)` only if `M` does.
- **The actor.** `SL_n(Q)` must lie in the M-Torelli kernel `K_M = ker(Aut_M(M * F_m) -> Aut(F_m))`. This group
  acts faithfully on `<<M>> = *_{F_m} M^w` by conjugating each factor.
- **With `M = V`** (BFFHZ's choice; `V` contains no Q): the free-product and mapping-torus closures exclude
  GL_n(Q) and every stepping stone.

## 3. Where the method could still reach GL_n(Q)

1. **The M-Torelli kernel `K_M`.** Open question: with `M` Q-free, can `K_M` contain `(Q,+)`? For `m = 1` it cannot IF `K_M` is
   `{x -> gxh}` (a copy of `M × M`); that description is not proved or cited. The single-letter transvection subgroups for `m = 2` are free products of copies of `M`, so
   they cannot either. The general case would need relative train tracks and polynomial growth.
2. **HNN extensions over nontrivial edge groups** (`stable-permutation-hnn-of-type-a-actor-is-type-a` (b)). This is
   the only closure in the neighbourhood that can create divisibility, as `BS(1,2) ⊇ Z[1/2]` shows.
   - A single ascending HNN extension of a group `D` by an endomorphism `φ` whose direct limit contains Q needs
     "growing multipliers".
   - That is impossible for module endomorphisms of finitely generated modules over finitely generated rings: the
     limit is a module over `R[1/f]`, a finitely generated ring, which contains no Q.
   - So the edge data must be nonlinear.
3. **Outer extensions** (`outer-extensions-of-fp-simple-mif-groups-satisfy-pbh` (S)).
   - `GL_n(Q) <= Aut(S)` meets `Inn(S)` in a normal subgroup of `GL_n(Q)`. That subgroup either contains `SL_n(Q)`,
     which is circular, or is scalar.
   - In the scalar case the image of `SL_n(Q)` (that is, `SL_n(Q)` or `PSL_n(Q)`) lies in a finitely presented
     subgroup `P <= Out(S)`. So this route needs a finitely presented `P` containing `SL_n(Q)` or `PSL_n(Q)` (Problem 2.7-type) that acts by outer automorphisms on a finitely presented
     simple MIF group.
   - One realization: `P` normalizes a type (A) actor `Γ <= Sym(X)`, since then it normalizes `SV_Γ`.

## 4. Verdict

The BFFHZ construction, taken as "type (A) from a finitely presented simple MIF base plus free letters", cannot
create the divisibility of GL_n(Q). In the free-product and mapping-torus closures every copy of `(Q,+)` comes from
`M`, and inside the actor every copy lies in the M-Torelli kernel. Whether that kernel can contain Q when `M` does not
is open (entry point 1). Entry points 2 and 3 are the non-circular ones left in this neighbourhood.
