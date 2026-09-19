---
rg: 2
id: cantor-gluing-kernel-is-the-union-of-finite-alphabet-kernels
kind: claim
title: The gluing kernel of V times the Cantor-alphabet full shift over any group is the increasing union of the finite-alphabet kernels, each a retract of it; so the Cantor-alphabet exactness EX needed over free groups is exactness over every finite alphabet, and with FPG all of P2'b exactness reduces to Z acting on the 2^n-letter full shifts
distinct_from:
  gluing-kernels-descend-from-the-full-shift: that maps an ambient kernel ONTO the kernel of a closed invariant subset; this shows the Cantor-alphabet kernel is the directed UNION of the finite-alphabet kernels, a colimit statement in the other direction.
  v-times-free-product-gluing-kernels-split-over-the-factors: that reduces exactness over F_n to FPG plus EX(Z), the Cantor-alphabet cyclic case; this shows EX(Z) is equivalent to exactness over each finite alphabet 2^n, so the cyclic input is a sequence of finite-alphabet statements.
  splitting-kills-the-finite-shadow-parity-of-the-gluing-group: that settles relations inside symmetric partitions of the two-point model, an image of K_(Z,2^Z); this places that model and the commutation criterion inside one merged route.
---

**ESTABLISHED** (lane proof, elementary; unreviewed; no priority claimed). bh-p2b-exact, 2026-09-18.
It merges the P2′b reductions of bh-p2b-exact, bh-one-relator and bh-invent-16. **EX(Z), FPG and FSG(Z, 2)
stay OPEN.**

## Setting

- Notation of `gluing-kernels-descend-from-the-free-group-full-shift`, with full bisections throughout.
  `Λ` is a finitely generated infinite group.
- `C = {0,1}^N`, and `A_n = {0,1}^n`. The map `p_n : C → A_n` keeps the first `n` digits, and
  `e_n : A_n → C` is `w ↦ w0^∞`, so `p_n ∘ e_n = id`.
- `Y = C^Λ`, and `Y_n = A_n^Λ`. Coordinatewise, `P_n : Y → Y_n` and `E_n : Y_n → Y` are equivariant with
  `P_n E_n = id`, and `E_n(Y_n)` is a closed invariant subset of `Y`.
- `Γ~_Y, K_Y` and `Γ~_n, K_n` are the gluing groups and kernels for `(Λ, Y)` and `(Λ, Y_n)`.

## Theorem

1. **Colimit.** Pullback along `P_n` gives injective maps `ι_n : Γ~_n → Γ~_Y` and `j_n : F(T_n) → F(T_Y)`,
   with `π_Y ι_n = j_n π_n`. Then:
   - `Γ~_Y` is the increasing union of the subgroups `ι_n(Γ~_n)`;
   - `K_Y = ⋃_n ι_n(K_n)`.
2. **Retract.** Restriction to `E_n(Y_n)` gives `q_n : Γ~_Y → Γ~_n` with `q_n ι_n = id`. So each `K_n` is a
   retract of `K_Y`, and `K_n = q_n(K_Y)`.
3. **Exactness is alphabet by alphabet.** The following are equivalent:
   - (i) `K_(Λ, C^Λ) = 1`;
   - (ii) `K_(Λ, A_n^Λ) = 1` for every `n`;
   - (iii) `K_(Λ, A^Λ) = 1` for every finite `A`;
   - (iv) for every `n`, every kernel element of `Γ~_n` commutes with `τ_0 = (00 01)`
     (`v-times-gluing-exactness-is-commutation-with-one-transposition`, item 2).
4. **Finite normal generation does not pass to the union.** `K_Y` is finitely normally generated only if the
   union stabilizes, that is, only if `K_Y` is the normal closure of `ι_n(K_n)` for one `n`. So FSG(Λ, A_n)
   for all `n` would give finite normal generation of `K_Y` only together with such stabilization, and the
   lane knows no argument for it. (`N_Y` is not finitely generated, so the finite-alphabet form FSG does not
   carry over to Cantor alphabets verbatim.)

## The merged route (three lanes)

```
BH ⇐ (★′) ∧ P2′b(Λ₀)                                        group route, v5 gate 5
P2′b exactness over all n-generated groups and all subshifts
   ⇔ K_(F_n, A^(F_n)) = 1                                    bh-one-relator, rank universality
   ⇐ FPG ∧ EX(Z) on C^Z                                      bh-invent-16, free-product splitting
EX(Z) ⇔ ∀n: K_(Z, A_n^Z) = 1                                  item 3 here
      ⇔ ∀n: lifting τ_0 around relator loops of Γ~_(Z, A_n^Z) returns τ_0     commutation criterion
necessary tests (images of K_(Z, A_n^Z)):
   period-m orbits via Z → Z/m                               bh-one-relator item 2; two-point model
```

What each view contributes:
- **Universality (bh-one-relator).** No subshift, rigidity or group geometry enters P2′b. One kernel per rank
  and alphabet governs everything.
- **Splitting (bh-invent-16).** Non-amenable ranks reduce to the cyclic case plus FPG. The cyclic input must
  be exactness, not finite normal generation, because `A^(F_n)` restricted to `⟨s⟩` is a Cantor-alphabet
  shift (item 4).
- **Commutation criterion (bh-p2b-exact).** Every central defect dies: the kernel is relatively perfect and
  the model is the normal closure of `τ_0`. Only non-central monodromy can obstruct exactness.
- **Finite shadows (bh-one-relator, GAP certificate).** In the computed shadows (three to five cones) the
  defect is a label-sum character, and splitting kills it. This is the commutation criterion in its smallest
  instance: the defect becomes central in a finite shadow, then dies by the swindle.
- **The residue common to all three.** Consistency of lifts across partitions that are not simultaneously
  symmetric (bh-one-relator's open point). This is the same thing as the multiplicativity lemma of
  bh-p2b-exact: the lift of `m τ m^(-1)` for a label `m` and a conditioned transposition `τ` must not depend on
  the decomposition used.

## Proof

**Item 1.**
- *Pieces.* `P_n^* : LC(Y_n, V) → LC(Y, V)`, `f ↦ f ∘ P_n`, is injective, because `P_n` is onto. It is also
  `Λ`-equivariant, so it gives an injective map `N_(Y_n) → N_Y` that is the identity on `V × Λ`, and it maps
  `N_(1, Y_n)` into `N_(1, Y)`.
- *Exhaustion.* Every clopen subset of `C^Λ` is a finite union of cylinders `{y : y(g) ∈ U_g, g ∈ F}`, with
  `F` finite and each `U_g ⊆ C` clopen, hence determined by finitely many digits. So every
  `f ∈ LC(Y, V)` is pulled back from some `Y_n`, and `N_Y = ⋃_n P_n^*(N_(Y_n))`, increasing in `n`.
- *The model is the colimit.*
  - `Γ~_Y` is generated by `M ∪ N_Y`. Its defining relations are those of `M`, those of `N_Y`, the
    amalgamation, and `[M_0, N_(1,Y)] = 1`.
  - Each relation of `N_Y`, and each gluing relator, involves finitely many elements of `N_Y`, so all of them
    lie in one `P_n^*(N_(Y_n))`. Since `P_n^*` is injective, the relation already holds in `N_(Y_n)`.
  - So `Γ~_Y = colim_n Γ~_n` along the maps `ι_n` (the identity on `M`, and `P_n^*` on `N`).
- *The full group.*
  - Pulling back pieces, `[u] × Q → [u'] × λQ` becomes `[u] × P_n^(-1)Q → [u'] × λ P_n^(-1)Q`. This defines
    `j_n`, which is injective since `P_n` is onto.
  - `π_Y ι_n = j_n π_n` holds on the generators `M ∪ N_(Y_n)`.
- *Injectivity of `ι_n`.* This follows from item 2.
- *The kernel.* Let `k ∈ K_Y`. It is a finite word in `M ∪ N_Y`, so `k = ι_n(k')` for some `n`. Then
  `j_n(π_n(k')) = π_Y(k) = 1`, so `π_n(k') = 1`, because `j_n` is injective. Conversely,
  `ι_n(K_n) ⊆ K_Y`.

**Item 2.**
- Restriction to `E_n(Y_n)` is the map of item 1 of `gluing-kernels-descend-from-the-free-group-full-shift`,
  read through `E_n`. It gives `q_n` with `q_n(K_Y) = K_n`.
- On `N_(Y_n)`, `q_n ι_n` is `f ↦ f ∘ P_n ∘ E_n = f`, and it is the identity on `M`. So `q_n ι_n = id`, and
  hence `ι_n` is injective.

**Item 3.**
- (i) ⇒ (iii): by descent. `A^Λ` embeds as a closed invariant subset of `C^Λ` via any injection `A → C`,
  and `K_(A^Λ)` is the image of `K_(C^Λ)`.
- (iii) ⇒ (ii): trivial.
- (ii) ⇒ (i): by item 1.
- (ii) ⇔ (iv): by item 2 of the commutation criterion. Its proof uses no freeness. `A_n^Λ` is topologically
  free for infinite `Λ`, and `K = [K, Γ~]` holds for every space.

**Item 4.**
- If `K_Y = ⟨⟨k_1, …, k_r⟩⟩`, then all the `k_i` lie in one `ι_n(K_n)`, by item 1, so `K_Y = ⟨⟨ι_n(K_n)⟩⟩`.
- For the parenthetical claim: `N_Y` is not finitely generated. A finite set of elements of `LC(Y, V)`
  depends on finitely many digits, `Λ` and `V` preserve that finite depth, and conditioned elements on sets
  of greater depth exist. ∎

## Lesson for general BH

**Exactness is the robust form of P2′b, and it is finitary.**
- Exactness descends to subsystems and to quotient groups (bh-one-relator).
- It splits over free products, given FPG (bh-invent-16).
- It passes to directed unions of alphabets, and each finite alphabet is a retract (item 2).

Finite normal generation does none of these cleanly. So the question to attack is: **is the gluing
presentation exact for Z acting on each full shift over 2^n letters?** By the commutation criterion, that
says lifting one Thompson transposition around relator loops has trivial monodromy.

Every central defect is already dead, as the finite shadows show concretely with their parity character. What
remains is one consistency statement: the lifts of label-conjugated transpositions must agree across
non-symmetric partitions. A proof of that statement, with no dynamics in it, settles route 2 of the master
route for every fp overgroup at once.
