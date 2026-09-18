---
rg: 2
id: torelli-lower-central-quotients-not-rf-proof
kind: route
title: Proof that the Torelli lower-central quotients Mod(S_g)/T_g[c+1] (g >= 3, c >= 2) are not residually finite, via Hain's central line and Deligne's theorem
target: torelli-lower-central-quotients-are-not-residually-finite
requires:
  - torelli-lower-central-quotients-do-not-virtually-split
  - deligne-universal-cover-lattice-is-non-rf-kazhdan
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
artifacts:
  - research/artifacts/gq-bh-bh-free-38-torelli-quotients.md
---

Fix `g >= 3`, `c >= 2`. Write `Q = Q_{g,c}`, `N = N_{g,c}`, `pi: Q -> Sp_2g(Z)`,
and `tau` for the finite torsion subgroup of `N`. Nowak's line numbers refer to
arXiv:2609.12196v1 (TeX in `gq/src/bh-free-38/`).

**Step 1: the central line.** Let `P_g` be the Malcev completion of `T_g`,
`N_c = P_g/P_g[c+1]` that of `N`, and `j: N -> N_c(Q)` the Malcev map (kernel
`tau`).
- Hain's theorem, as stated by Nowak (Thm `thm:hainkernel`, l.2282), gives a
  central extension `1 -> Z_g -> P_g -> U_g -> 1`. Here `U_g` is the prounipotent
  radical of the relative completion `G_g` of Mod with respect to `Sp_2g`, and
  `Z_g ≅ G_a` with `Z_g ⊂ P_g[2]` and `Z_g ∩ P_g[3] = 0`.
- By Nowak Cor `cor:centralline` (l.2317) its image `Z_c ⊂ N_c` is a rational
  central `G_a`.
- Put `D = j^{-1}(Z_c(Q))`. As in Nowak Lemma `lem:rationalkernel` (l.2214),
  `j(N) ∩ Z_c` is a lattice in the line, so `D/tau ≅ Z`.
- `Mod` acts on `P_g` by conjugation, compatibly with `P_g -> U_g`. It preserves
  the line `Z_g`, acting by a character `Mod -> Q^×`. `Mod(S_g)` is perfect for
  `g >= 3`, so that character is trivial. Hence `D` is normal in `Q`, and `Q` acts
  trivially on `D/tau`.

**Step 2: a linear quotient.** `T_g -> U_g` maps `T_g[c+1]` into `U_g[c+1]`, and
`theta: P_g -> U_g` is onto with kernel `Z_g`, so
`N_c/Z_c ≅ U_g/U_g[c+1] =: U'`.
- The map `Mod -> G_g(Q)` descends to `Q -> L(Q)`, where
  `L = G_g/U_g[c+1] = U' ⋊ Sp_2g` by the characteristic-zero Levi decomposition.
- Its kernel is exactly `D`. So `Gamma = Q/D` embeds in `L(Q)`, with
  `Gamma ∩ U'(Q) = j(N)/j(D)`, a lattice in `U'` (Malcev), and image
  `Sp_2g(Z)` in `Sp_2g(Q)`.

**Step 3: a virtual section of `Gamma`.** Take a finite-index `S_0 <= Sp_2g(Z)`
and a subgroup `Sigma_0 <= Gamma` mapping isomorphically onto `S_0`. Induct along
the lower central series of `U'`, whose layers `V` are rational `Sp_2g`-modules.
- **Vanishing of H^1.** For every finite-index `S <= Sp_2g(Z)`,
  `H^1(S; V(Q)) = 0`. This is Margulis–Raghunathan vanishing for higher-rank
  lattices; for the trivial module it uses finite abelianization.
- **Top layer.** The crossed homomorphism describing `Gamma` modulo the lower
  layers is a coboundary, so after conjugating by an element of `U'(Q)` the image
  sits in `V(Q) ⋊ Sp_2g(Q)`.
- **Torsion obstruction.** The remaining obstruction is a class
  `epsilon ∈ H^2(S; Lambda_V)`, where `Lambda_V = Gamma ∩ V(Q)`. It dies in
  `H^2(S; V(Q))`, so it is torsion, say of order `n`.
- **Splitting.** Pushing out along `Lambda_V ⊂ (1/n)Lambda_V` splits it. That
  lattice is `S`-stable, so `Gamma·(1/n)Lambda_V` contains a section, and its
  intersection with `Gamma` has finite index in that section.

**Step 4: the central extension.**
- Let `E_0 = (pi mod D)^{-1}(Sigma_0) <= Q`. It is an extension of `S_0` by `D`.
- `E_0` acts on `D = <tau, d>` trivially on `D/tau`. So it acts through a finite
  group: an automorphism fixing `tau` pointwise and `D/tau` is determined by
  `d -> d t` with `t ∈ tau`.
- Let `E_1` be the kernel of that action, which has finite index in `E_0`, so
  `E_1` centralizes `D`.
- Put `D_1 := E_1 ∩ N`. Since `E_0 ∩ N = D`, we get `D_1 = E_1 ∩ D`, which lies
  in `Z(D)` and so is central in `E_1`. It has finite index in `D`, hence is
  infinite. Being finitely generated and abelian, `D_1 = Z·d_1 ⊕ F` with `F`
  finite.
- Put `E = E_1`. Then `E/F` is a central extension of the finite-index subgroup
  `S_1 = pi(E_1)` by `Z`, with class `e ∈ H^2(S_1; Z)`.

**Step 5: `e` has infinite order.** Suppose not.
- Each torsion class in `H^2(S_1; Z)` comes from `Hom(S_1, Q/Z)` by Bockstein,
  since `H^1(S_1;Q) = 0`. So `e` dies on the common kernel `S_2` of finitely many
  characters, which has finite index.
- The extension then splits over `S_2`: there is `Sigma ≤ E_1` mapping onto `S_2`
  with `Sigma ∩ D_1 ⊆ F`.
- `E_1 ∩ N = D_1` (Step 4). So `Sigma ∩ N ⊆ F` is finite.
- This contradicts `torelli-lower-central-quotients-do-not-virtually-split`.

**Step 6: the class is Deligne's.**
- By Borel's stable-range theorem, `H^2(S_1; Q)` is spanned by the restriction of
  the class `u` of the universal cover of `Sp_2g(R)`. The range is quoted for
  `g >= 3` and not read at source; see the trust surface on the target.
- So `m e - n u` is torsion in `H^2(S_1; Z)` for some integers `m, n ≠ 0`. It
  vanishes on a finite-index `S_3` (Bockstein, as in Step 5).
- On `S_3`, let `X` be the central extension with class `m e = n u`. Both
  `E_e` (the extension with class `e`) and the Deligne lattice
  `E_u = S_3~` sit in `X` with finite index `|m|` and `|n|`, as pushouts along
  `Z -> Z`, multiplication by `m` and by `n`.
- Finite residuals agree along finite-index subgroups:
  `Res(H) = Res(G)` whenever `[G:H] < ∞`.
- `S_3~` has finite index in `Sp_2g(Z)~`, and
  `Res(Sp_2g(Z)~) ⊇ 2Z` (`deligne-universal-cover-lattice-is-non-rf-kazhdan`,
  `deligne-covers-of-sp2g-z-have-finite-residual-2z`).
- Hence `Res(E_e) = Res(X) = Res(S_3~) ⊇ 2Z ≠ 1`.

**Step 7: conclusion.**
- `E_e` is a finite-index subgroup of `E/F`, so `E/F` is not residually finite.
- If `E` were residually finite, so would be `E/F`: a quotient of a residually
  finite group by a finite normal subgroup stays residually finite, because the
  finitely many elements `xF` can be avoided by one finite-index normal subgroup.
- So `E ≤ Q` is not residually finite, and neither is `Q`.
- Commensurability: `E_e` and `S_3~` are finite-index subgroups of `X`.

**Remark (Borel-free alternative, not written out).** Deligne's own argument
reads Step 6 through the congruence completion.
- If `E/F` were residually finite, the closure of its centre would be infinite, so
  some `Z_ℓ` quotient survives.
- The class would then come from `H^2_cts` of the congruence completion of `S`
  (Bass–Milnor–Serre), which is torsion. The main input is Lazard plus
  Whitehead's lemma at `ℓ`, and pro-`p` vanishing away from `ℓ`.
- That would force `e` to be torsion, contradicting Step 5. The step
  "`H^2_cts(S-hat; Z_ℓ) ⊗ Q = 0`" for the full adelic product is the technical
  core, and it is not verified here.
