---
rg: 2
id: decidable-algebras-embed-in-oracle-leavitt-crossed-products
kind: claim
title: Every finitely generated F_2-algebra with solvable word problem embeds unitally in (LC(Y,F_2) ⋊ Z) ⊗ L_2 for some effective Z-subshift Y (an algebraic Kirchberg embedding with an oracle); with G2 this gives Boone--Higman through Track B
distinct_from:
  algebra-boone-higman-conjecture: that asks for a finitely presented simple envelope; this asks for an embedding in a host that is NOT finitely presented, with an oracle subshift, and leaves finite presentation and simplicity to the row-lifting and rigidity steps.
  decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units: that is the group-level unit question over a torsion-free Farrell-Jones group in any dimension; this is the algebra-level one-dimensional form, which implies it for the canonical inputs.
  subshift-languages-give-monomial-algebras-in-crossed-products: that proves the monomial case; this is the general statement.
---

**OPEN.** Let `A` be a finitely generated unital `F_2`-algebra with solvable word problem. Then there is an
effective subshift `Y` over a finite alphabet with a unital embedding `A -> (LC(Y, F_2) ⋊ Z) ⊗ L`,
`L = L_(F_2)(1,2)`.

## Why it is the one-dimensional core of gate U
1. Apply it to `A = R_Γ`, the canonical Cantor crossed-product algebra of
   `decidable-host-classes-reduce-to-canonical-kazhdan-groups`, with `Γ` decidable, so that `R_Γ` is
   decidable. Then
   `H_Γ = EL_3(R_Γ) <= GL_3((LC(Y) ⋊ Z) ⊗ L) ≅ ((LC(Y) ⋊ Z) ⊗ L)^x`, since `M_3(L) ≅ L`.
2. By `row-factors-lift-z-crossed-products-into-z2-hosts`, this embeds in `(B_X ⊗ L)^x` for every
   `Z^2`-SFT `X` with a row factor onto `Y`.
3. If `X` is free, minimal and quantum rigid (G2), then `B_X` is finitely presented and central simple.
   `K_1 = K_2 = 0` holds by Farrell--Jones for `Z^2` (`farrell-jones-groups-acting-freely-have-k-trivial-leavitt-hosts`).
   So `(B_X ⊗ L)^x` is finitely presented and simple (Khanh import).
4. By the canonical-input principle, Boone--Higman follows.

So Track B is: this claim, plus G2 for prescribed row factors, plus the Khanh import.

## Known cases
- **Every monomial algebra `K<Σ>/(W)` with `W` decidable.** Pad the language: let `Y` be the closure of the
  sequences `# w_1 # w_2 # ⋯` with every `w_i` avoiding `W`. The words over `Σ` occurring in `Y` are
  exactly the words avoiding `W`. By `subshift-languages-give-monomial-algebras-in-crossed-products`,
  `a ↦ 1_([a]) u` embeds the algebra in `LC(Y) ⋊ Z`, without `L`. This includes the benchmark `A_X`.
- **Fixed-host inputs.** Subalgebras of `L`, such as free algebras and Laurent polynomial rings, embed
  with `Y` trivial.

## Constraints on any proof
- **The Leavitt factor is essential beyond linear-sofic inputs.** Without `L` the host has a faithful rank
  function once `Y` is minimal (`amenable-crossed-product-units-are-linear-sofic`). Stable finiteness
  would then transfer to `A`, which fails, for example, for `A = L`.
- **No uniform complexity.** `Y` must depend on `A` (`no-fp-simple-algebra-hosts-every-decidable-algebra`).
  The word problem of the host is the language of `Y`, so `Y` must be decidable as well as effective
  whenever step 3 is to be reached. Minimal SFTs have decidable languages.
- **Linear relations need superposition, not reading.** Pattern-conditioned single translations realize
  only monomial relations: distinct words read disjoint cylinders. A general `A` needs generators that are
  *sums* of conditioned translations tensored with Leavitt words, so that relations arise from
  cancellation of paths. Over `F_2`, the binomial relation `w_1 = w_2` becomes equality of reading sets,
  which is a local, programmable condition.

**Lesson for general BH.** Under Track B, Boone--Higman is equivalent in strength to an *algebraic
Kirchberg embedding with an oracle*: every decidable algebra lies in `L`-valued banded matrices over `Z`
whose entries read an effective subshift. Monomial algebras, where the oracle is the language itself,
are the solved case. The general case is where linear relations must be produced by cancellation among
oracle-conditioned paths. That is the concrete next mechanism to invent.
