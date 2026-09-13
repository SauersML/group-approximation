# Presentation and amalgam kernel of the binary Jacobson EL_3 (2026-09-12)

Lane `w7-el3j-presentation`. Paper mathematics only. This takes up the two next steps of
`research/artifacts/jacobson-el3-soficity-firewalls-2026-09-12.md` (Section 6): finite presentation of `E`, and the
kernel of the half-amalgam onto `E`. All decisions are held OPEN for `w4-vf-gate`.

## 0. Notation

- `J = F_2<S,T | TS=1>`, `Q = 1-ST`, `E = EL_3(J)`. The head is `x_13(Q)`.
- The symbol is `π : E -> SL_3(F_2[z^(±1)])`, `S -> z`, `T -> z^(-1)`. Its kernel `L` is infinite, simple and locally
  finite (firewall artifact Section 1).
- Commutators are `[a,b] = a b a^(-1) b^(-1)`, so `[x_ij(r), x_jk(s)] = x_ik(rs)`. In characteristic two each
  `x_ij(r)` is an involution.
- Cones inside `E`: `G_+ = EL_3(F_2[S])`, `G_- = EL_3(F_2[T])`, `G_0 = SL_3(F_2)`. Since `F_2[z]` is Euclidean, `π`
  maps `G_+` isomorphically onto `SL_3(F_2[z])` and `G_-` onto `SL_3(F_2[z^(-1)])`.
- Halves: `H_± = π^(-1)π(G_±) = L ⋊ G_±` and `H_0 = L ⋊ G_0`. Put `P = H_+ *_(H_0) H_-` and `N = ker(P -> E)`.
- Laurent cone amalgam: `U = G_+ *_(G_0) G_-`, with canonical `q : U -> E`, `Φ = π q`, and `K_Λ = ker Φ`.
- Coordinate words in `U`:

  ```text
  ρ_- = [x_12(T), x_23(S)] x_13(1),        ρ_+ = [x_12(S), x_23(T)] x_13(1).
  ```

  Here `x_12(T)` is a letter of `G_-` and `x_23(S)` a letter of `G_+`. `ρ_-` is the Toeplitz relator `R_T`.

## 1. Rank four

**Proposition 1.1.** `K_2(4,J) = 0`. So `EL_4(J) ≅ St_4(J)` is finitely presented and Kazhdan, `E` is the image of
`St_3(J)` in `St_4(J)`, and `K_2(3,J) = ker(St_3(J) -> St_4(J))`.

*Proof.* Route `binary-jacobson-steinberg-cover-k2-citation` records `sr(J) = 2` and `K_2(J) = 0`. It quotes
Suslin--Tulenbaev (Weibel III, Remark 5.5.2): `sr(R) = d+1` makes `K_2(n,R) -> K_2(R)` an isomorphism for `n >= d+3`.
With `d = 1` the range starts at `n = 4`, one rank below the route's own use. Then
`steinberg-finite-presentation-and-kazhdan-theorem` at `n = 4` gives finite presentation and property (T). The corner
inclusion `EL_3(J) <= EL_4(J)` is injective, and `St_3(J) -> EL_3(J) -> EL_4(J)` factors through `St_4(J)`. ∎

Rank three lies below the quoted range, so main has no input on `K_2(3,J)`.

## 2. The half-amalgam kernel

**Proposition 2.1 (splitting).** `L` is normal in `P`, and `P = L ⋊ U`.

*Proof.* `L ⊆ H_0` is normal in `H_+` and in `H_-`, which generate `P`, so `L` is normal in `P`. By the universal
properties,

```text
P/L ≅ (H_+/L) *_(H_0/L) (H_-/L) ≅ G_+ *_(G_0) G_- = U.
```

The inclusions `G_± ⊆ H_±` agree on `G_0`, so they define `s_0 : U -> P`. Composed with `P -> P/L ≅ U`, it is the
identity on `G_+` and `G_-`, so it is a section. ∎

From now on `U` is identified with `s_0(U) ⊆ P`, and `p : P -> U` is the projection killing `L`.

**Proposition 2.2 (kernel).**
1. `N ∩ L = 1` and `[N, L] = 1`.
2. `p` maps `N` isomorphically onto `K_Λ`, with inverse `s(u) = q(u)^(-1) u`.
3. `q` is onto. So `E ≅ U / ker q`, `ker q = N ∩ U`, and `q` restricts to a surjection `ℓ : K_Λ -> L` with kernel
   `ker q`.
4. `ℓ(ρ_-) = 1` and `ℓ(ρ_+) = x_13(Q)`.

*Proof.*
1. `P -> E` is injective on `H_+ ⊇ L`, so `N ∩ L = 1`. Both subgroups are normal, so `[N, L] ⊆ N ∩ L = 1`.
2. Let `n = λu ∈ N` with `λ ∈ L` and `u ∈ U`. In `E`, `q(u) = λ^(-1) ∈ L`, so `Φ(u) = 1`. So `p(N) ⊆ K_Λ`, and `p` is
   injective on `N` by point 1. Conversely, if `u ∈ K_Λ`, then `q(u) ∈ L ⊆ P` and `q(u)^(-1) u` maps to `1` in `E`.
3. `J` is spanned by the monomials `S^a T^b`, and `x_ik(S^a T^b) = [x_ij(S^a), x_jk(T^b)]` with `j` the third index. So
   `G_+ ∪ G_-` generates `E`. The rest follows since `q^(-1)(L) = K_Λ`.
4. `q(ρ_-) = x_13(TS + 1) = 1` and `q(ρ_+) = x_13(ST + 1) = x_13(Q)`. Both words lie in `K_Λ`, since `z^(-1)z = 1`. ∎

**Remark 2.3 (where `J` enters).** `N ≅ K_Λ` does not depend on `J`: it is the kernel of the Laurent cone amalgam onto
`SL_3(F_2[z^(±1)])`. The ring `J` enters only through `ℓ`, and

```text
E = (L ⋊ U) / { q(u)^(-1) u : u ∈ K_Λ }.
```

The positive coordinate word `ρ_+` is exactly the word whose `ℓ`-image is the head.

**Corollary 2.4 (Toeplitz commutators are not enough).**
1. Let `X ⊆ N ∩ U`, for example `ρ_-` and its `G_0`-conjugates `[x_ij(T), x_jk(S)] x_ik(1)`. Then
   `<<X>>_P ⊆ ker q ⊆ U`.
2. The head relator `R_Q = s(ρ_+) = x_13(Q) [x_12(S), x_23(T)] x_13(1)` lies in `N` but not in `U`.
3. So `N != <<X>>_P`, and no normal generating set of `N` consists of words in the cone letters.
4. `N = <<ker q ∪ {R_Q}>>_P` and `N/(N ∩ U) ≅ L`.

*Proof.*
1. `P = L U` and `L` centralizes `N ⊇ X`, so `<<X>>_P = <<X>>_U`, which lies in the normal subgroup `ker q` of `U`.
2. `p(R_Q) = ρ_+`. If `R_Q ∈ U`, then `R_Q = ρ_+`, and `q(ρ_+) = 1`, contradicting `q(ρ_+) = x_13(Q) != 1`.
3. This follows from points 1 and 2.
4. Put `M = <<ker q ∪ {R_Q}>>_P ⊆ N`. Then `p(M)` is normal in `U` and contains `ker q` and `ρ_+`. Its image `ℓ(p(M))`
   is normalized by `q(U) = E` and contains the head, so it is a nontrivial normal subgroup of the simple group `L`,
   hence all of `L`. Since `p(M) ⊇ ker ℓ`, `p(M) = K_Λ = p(N)`, so `M = N` by Proposition 2.2.2. The isomorphism
   `N/(N ∩ U) ≅ K_Λ / ker q ≅ L` is Proposition 2.2.2–3. ∎

**Remark 2.5 (not decided).** It is not decided whether `ker q = <<ρ_- and its G_0-conjugates>>_U`, that is, whether
`U/<<ρ_-^(G_0)>> -> E` is injective.
- `one-opposite-steinberg-relator-does-not-close-laurent-cycle` separates the two coordinate words over a Laurent ring
  with a finite model. Corollary 2.4 separates them with the model `E` itself.
- Elements such as `[ρ_+, x_13(S)]` lie in `ker q`, since `[x_13(Q), x_13(S)] = 1`. Whether they lie in `<<ρ_-^(G_0)>>_U`
  is open.
- `U/<<ρ_-^(G_0)>>` also maps onto `St_3(J)` once `St_3(F_2[z]) ≅ SL_3(F_2[z])`. That vanishing of `K_2(3, F_2[z])` is
  not on main at rank three.

## 3. Residual finiteness of the kernel

**Proposition 3.1.** `U` is residually finite. So `N ≅ K_Λ`, and every subgroup of `N`, is residually finite and
sofic.

*Proof.*
1. `SL_3(F_2[z])` is residually finite. For `g != 1`, reduce modulo `z^m` with `m` above every degree in `g - 1`; the
   image of `g` in the finite group `SL_3(F_2[z]/(z^m))` is nontrivial. The same holds for `SL_3(F_2[z^(-1)])`.
2. Let `A *_C B` be an amalgam with `A` and `B` residually finite and `C` finite (G. Baumslag). Take `g != 1`, either in
   `C` or in reduced form with syllables `a_i ∈ A \ C` and `b_i ∈ B \ C`.
   - The finite set `(C \ {1}) ∪ {c^(-1) a_i : c ∈ C}` misses `1`. So some finite-index normal `A' ⊴ A` avoids it, and
     likewise some `B' ⊴ B`.
   - In `Ā *_C B̄`, with `Ā = A/A'` and `B̄ = B/B'`, the group `C` embeds and the syllables stay outside `C`. So
     `ḡ != 1` by the normal form theorem.
   - Let `Ā` act on itself times `|B̄|` points, and `B̄` on itself times `|Ā|` points. Both actions are free, and so is
     their restriction to `C`, with the same number of orbits. Match the two `C`-sets and obtain
     `Ā *_C B̄ -> Sym(n)`, injective on `Ā` and `B̄`.
   - Its kernel meets every conjugate of `Ā` and `B̄` trivially. So it acts freely on the Bass--Serre tree, is free,
     and has finite index. Free groups are residually finite, so `ḡ` survives in a finite quotient.
3. Apply point 2 with `A = G_+`, `B = G_-`, `C = G_0`. ∎

**Consequence 3.2 (firewall).** No subgroup of `N`, in particular none generated by Steinberg cycles of the
half-amalgam, is nonsofic. What the quotient `P -> E` does to soficity is a property of `N` as a *normal* subgroup,
carried by `ℓ`. Soficity of `P = L ⋊ U` itself is not claimed, since that is an amenable-by-sofic extension.

## 4. Finite presentation of E: reductions

**Proposition 4.1.** If `E` is finitely presented, then `E` is neither LEF nor LEA.

*Proof.*
- `E` satisfies the Steinberg relations over `J` in indices 1, 2, 3, so every finite image kills the head
  (`cohn-elementary-group-is-not-lef`, point 1).
- Suppose `E` is LEF, and take a ball containing the defining relators and the head. A partial embedding of that ball
  into a finite group defines a homomorphism from `E` that keeps the head, a contradiction.
- `E` is LEA only if it is LEF (`jacobson-elementary-groups-are-lea-only-if-lef`). ∎

**Proposition 4.2 (reductions).**
1. `L` is the normal closure of the head, since `L` is simple. So if `E` is finitely presented, then
   `E/L = SL_3(F_2[z^(±1)])` is finitely presented.
2. `U` is finitely generated. So if `E` is finitely presented, `ker q` is finitely normally generated in `U` (B. H.
   Neumann). The converse would need `U` to be finitely presented, which main does not record.
3. If `St_3(J)` is finitely presented, then `E` is finitely presented iff `K_2(3,J)` is finitely normally generated in
   `St_3(J)`.
4. If `E` is finitely presented, then some neighbourhood of `E` in the space of marked groups consists of marked
   quotients of `E`. So a marked sequence converging to `E`, none of whose members is a quotient of `E`, would show
   that `E` is not finitely presented.

**Where this stops.** None of the following is decided:
- finite presentation of `St_3(J)`;
- finite presentation of `E`;
- the group `K_2(3,J)`, and whether it is finitely normally generated.

No infinite family of independent relators is found.

For orientation only (not on main, not a proof input): `SL_3(F_q[t])` is not finitely presented (Behr), while
`SL_3(F_q[t^(±1)])` is (Bux--Köhl--Witzel). Point 1 is consistent with the second. The cones `G_±` are of the first
kind, so the converse of point 2 cannot come from a finite presentation of `U`.

## 5. Toward L1

The residue list in `leavitt-disjoint-cylinder-defects-strictly-submultiplicative` (lane `w7-sub-multiletter`) names,
among the ways a relation-only proof could bite, a nonsofic cycle of Steinberg relations and an element of
`K_2(3,R)`. This section does not repeat that list; it tests the two options against `E`.

**K_2 option.** `leavitt-unit-groups-have-no-unstable-k2-at-rank-three` (OPEN, lane `w7-k2-unstable`) records
`K_2(3,R) = 0` for `R = L_(F_2)(1,2)`.
- The ring map `S -> s_0`, `T -> t_0` used in `property-t-free-leavitt-via-jacobson-head-root` induces
  `St_3(J) -> St_3(R)`.
- So `K_2(3,J) -> K_2(3,R) = 0` is zero, and a rank-three Steinberg cycle over `J` gives no `K_2(3,R)` input.
- On the `J` side, rank four has `K_2(4,J) = 0` (Proposition 1.1).

**Cycle option.** In the half-amalgam model the Steinberg cycles are the elements of `N`. By Proposition 3.1, a
"Steinberg cycle generating a nonsofic subgroup" cannot be found inside `N`. A soficity obstruction for `E` has to use
`N ⊴ P`, that is, the homomorphism `ℓ : K_Λ -> L` sending `ρ_+` to the head.

**Transfer to R.**
- *The map is an embedding.* `property-t-free-leavitt-via-jacobson-head-root` records the ring embedding and the image
  `x_13(s_1 t_1) != 1` of the head. Every nontrivial normal subgroup of `E` contains `L` (firewall artifact,
  Proposition 1.4), and the head lies in `L`. So the kernel of `E -> EL_3(R)` is trivial, and soficity of `EL_3(R)`
  would imply soficity of `E`.
- *No direct analogue of the splitting.* `R` is simple, so there is no symbol, no finitary kernel and no Laurent cone
  amalgam. A transfer of Proposition 2.2 would have to replace `L` by the relative elementary subgroup of the ideal
  generated by `s_1 t_1`, which is all of `R`.

## 6. Status

- **Candidate proofs (OPEN until `w4-vf-gate`).** Propositions 1.1, 2.1, 2.2, 3.1, 4.1 and 4.2, and Corollary 2.4.
- **Refuted.** "`N` is normally generated by the Toeplitz commutators and their Weyl conjugates" (Corollary 2.4).
- **Open.**
  - Finite presentation of `E` and of `St_3(J)`.
  - `K_2(3,J)`.
  - Whether `ker q = <<ρ_-^(G_0)>>_U`.
- **Next.**
  1. Test `[ρ_+, x_13(S)]` in a model that kills `ρ_-` and its `G_0`-conjugates.
  2. Find either a marked sequence converging to `E` without quotients of `E`, or finitely many relators whose normal
     closure is `ker q`.
