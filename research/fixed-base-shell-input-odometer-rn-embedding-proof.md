---
rg: 2
id: fixed-base-shell-input-odometer-rn-embedding-proof
kind: route
title: Pull the shell germs back through the faithful odometer near action, then apply the Kazhdan theorem with the odometer as local group
target: fixed-base-shell-inputs-embed-in-odometer-rn-groups
requires:
  - odometer-prefix-groups-have-fg-index-kernels
  - shell-cantor-embeddings-are-finite-germ-extensions
  - kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
artifacts:
  - research/artifacts/solve-deligne-shell-singfix-2026-09-13.md
---

Use the notation of the target. `NearSym(N)` is the near permutation group of
`N`, and `[f]` is the near class of a permutation `f`.

## 1. The odometer near action

- `B = V_(h,r)(<a>)` acts on `r` copies of the h-adic Cantor set by finite prefix
  tables with a power `a^c` on each leaf.
- `odometer-prefix-groups-have-fg-index-kernels` identifies `n = r*q+i` with the
  root `i` and the h-adic expansion of `q`. It states that the induced cofinite
  action `iota : B -> NearSym(N)` is faithful.
- `iota` is induced by an action, so it is a homomorphism. Put `J = iota(B)`.
  Then `J` is a subgroup of `NearSym(N)` and `iota : B -> J` is an isomorphism.
- The fixed-base hypothesis says that `[rho_g]` lies in `J` for every `g` in `S`.

## 2. The input embeds in `B`

- `g -> [rho_g]` is a homomorphism `P -> NearSym(N)`, because `g -> rho_g` is a
  permutation action.
- It is injective. For `g != 1`, `rho_g` moves every even integer, so it is not
  finitary and its near class is nontrivial. This is the germ faithfulness of
  `shell-cantor-embeddings-are-finite-germ-extensions`: every nonidentity element
  of `P` remains nonidentity as a germ.
- Every `g` in `P` is a product of elements of `S` and their inverses, and `J` is
  a subgroup. So `[rho_g]` lies in `J` for every `g`.
- Hence `psi = iota^-1 o [rho] : P -> B` is a well-defined injective homomorphism.
  This is item 1.

## 3. Kazhdan and FW subgroups

- **The odometer is self-similar.** Write digit words least significant digit
  first. Then `a(d zeta) = (d+1) zeta` for `d < h-1`, and
  `a((h-1) zeta) = 0 a(zeta)`. Every section of a power `a^c` at a digit is again
  a power of `a`, namely `a^(floor((d+c)/h))` at the digit `d`. So
  `<a> <= Aut(T_h)` is self-similar, and it is infinite cyclic.
- **FW subgroups.** Let `G <= P` have property FW, for instance property (T).
  Then `psi(G) <= V_(h,r)(<a>)` has property FW. The multi-root form of
  `kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf` gives a finite-index
  subgroup `G_0 <= G` that embeds in `<a>^n`, which is `Z^n`. So `G_0` is free
  abelian of finite rank, and `G` is virtually free abelian of finite rank.
- **Kazhdan subgroups.** If `G` has property (T), it is also amenable, being
  virtually abelian. A discrete group that is amenable and has property (T) is
  finite. This is standard (Bekka--de la Harpe--Valette, *Kazhdan's Property (T)*);
  the theorem number was not re-checked here. This is item 2.

## 4. Consequences

- **Inputs with an infinite Kazhdan subgroup.** If `P` contains an infinite
  subgroup with property (T), item 2 fails for `P`. So no enumeration of `P`
  satisfies the fixed-base hypothesis, for any `h` and `r`.
- **Deligne's lattice.** `Gamma~` has property (T), by item 3 of
  `deligne-universal-cover-lattice-is-non-rf-kazhdan`. It is infinite, because by
  item 1 there it is a central extension with kernel `Z`. So neither `Gamma~` nor
  any input containing it has a fixed-base shell action. This is item 3.
