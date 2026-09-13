---
rg: 2
id: boundary-kazhdan-families-pairwise-non-isomorphic
kind: claim
title: The paradoxical simple Kazhdan families (A*B tree ends, Γ_p on P^1(Q_p), odometer Nekrashevych, L(1,m)⊗L(1,n)) give pairwise non-isomorphic groups for distinct parameters
---

**OPEN.** Consider the groups `S = EL_N(R)/Z` from:
- `free-product-finite-groups-boundary-simple-kazhdan-not-mf`;
- `p-adic-projective-line-elementary-simple-kazhdan-not-mf`;
- `odometer-nekrashevych-elementary-simple-kazhdan-not-mf`;
- `product-two-graph-kp-elementary-simple-kazhdan-not-mf`;
- `boundary-action-elementary-simple-kazhdan-not-mf`.

The claim is that distinct choices of family, parameters, `q` and `N` give non-isomorphic groups.

## Attempts

- **Coarse invariants fail.** Every such `S` is infinite, finitely generated, simple and Kazhdan, with no MF quotient.
  Each ring contains `M_n(F_q)` for all `n` (a unital Leavitt copy absorbs matrix algebras), so `S` contains
  `SL_(Nn)(F_q)` for all `n`, hence every finite group. None of these properties separate the families.
- **Unit groups.** For purely infinite simple `R`, the printed Thm l.1218 gives
  `GL_N(R)/Rad_MF(GL_N(R)) ≅ K_1(R)`, which separates the unit groups `GL_N(R)`, not `S`. For Leavitt rings,
  `K_1 = k^×/(k^×)^(m-1)`.
  - Algebraic `K_1` of the crossed products `LC(∂Γ, F_q) ⋊ Γ` and of the tensor products is not computed.
  - Whether these rings are purely infinite simple in AGP's algebraic sense is unchecked.
- **Schur multiplier.** `S` is perfect, and for `N` in the stable range `H_2(EL_N(R))` should match `K_2(R)` up to the
  centre (van der Kallen type stability, recalled, not imported). `K_2` of these rings is unknown.
- **Ring recovery.** Isomorphisms `EL_N(R) ≅ EL_N(R')` for `N >= 3` over noncommutative rings are expected to come from
  ring isomorphisms or anti-isomorphisms, up to centre (Golubchik–Mikhalev type, recalled). If such a theorem holds for
  these rings, the question reduces to ring isomorphism, which is still undecided across the families.
- **Characteristic.** `(R, +)` is an infinite elementary abelian `p`-group inside `S`. Whether `S` determines `p` needs
  an argument excluding infinite elementary abelian `ℓ`-subgroups for `ℓ != p`. Diagonal tori in increasing matrix
  corners give such subgroups whenever `ℓ | q^j - 1`, so this invariant does not separate on its own.
