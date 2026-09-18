---
rg: 2
id: ck-maximal-kernel-four-regimes-proof
kind: route
title: Compare the maximal kernel with the covering kernel and with the congruence kernel of its level, then read finite ideal generators from finite normal generators
target: ck-maximal-kernel-four-regimes
requires: [fp-quotient-iff-kernel-finitely-normally-generated, ck-envelope-level-ideal-screen, elementary-root-kernel-equals-level, projective-elementary-fp-kernel-criterion, universal-sandwich-ring-is-finitely-presented-and-injective, ck-steinberg-marked-cover]
---

Notation as in the claim. Write `x -> xbar` for reduction `GL_n(U) -> GL_n(U/I)`.

## Step 0. Three elementary facts

**(F1) Centre of an elementary group.** For any unital ring `R` and `n >= 2`,
`Z(E_n(R)) = E_n(R) ∩ { d I_n : d in Z(R)^x }`. If `x` commutes with
`e_ij(1) = 1 + E_ij`, then `x E_ij = E_ij x`. Comparing entries in column `j`
gives `x_ki = δ_ki x_jj` for every `k`. Running over all `i != j` shows that
`x = d I_n` is scalar. Commuting with `e_12(r)` gives `dr = rd`. Since `x` is
invertible, `d` is a unit. The converse inclusion is clear.

**(F2) `C_I` is the kernel of `Q -> PE_n(U/I)`.** Reduction maps `Q` onto
`E_n(U/I)`, because elementary generators lift. By (F1), `xbar` is central in
`E_n(U/I)` iff it is a central scalar, iff it is central in `GL_n(U/I)`. So
`C_I` is normal in `Q`, and `Q/C_I = PE_n(U/I)`. If `I != U`, then `e_12(1)`
is not in `C_I`, so `C_I` is proper. Also `lev(C_I) = I`, and `E_n(U,I) <= C_I`.

**(F3) Perfection.** For `n >= 3`, `e_ij(a) = [e_ik(a), e_kj(1)]` with `k`
distinct from `i` and `j`. So `Q` is perfect.

## Step 1. The four regimes

Let `M` be a maximal proper normal subgroup of `Gamma` and `N = rho(M)`.

**R1.** Suppose `K` is not contained in `M`. Then `MK` is normal and strictly
contains `M`, so `MK = Gamma` and `L = MK/M = K/(K∩M)`.

Now suppose `K <= M`. Normal subgroups of `Gamma` containing `K` correspond
to normal subgroups of `Q`. So `N` is a maximal proper normal subgroup of `Q`,
`L = Q/N`, and `I = lev(N)` is a proper two-sided ideal
([[ck-envelope-level-ideal-screen]], items 1–2; the proof there uses only the
Steinberg identities). By definition of the level, `E_n(U,I) <= N`. By (F2),
`C_I` is proper and normal.

**R2.** Suppose `C_I` is not contained in `N`. Then `C_I N` strictly contains
`N`, so `C_I N = Q` and `L = C_I/(C_I ∩ N)`. Since `E_n(U,I) <= C_I ∩ N`, `L`
is a quotient of `C_I/E_n(U,I)`.

**R3/R4.** Otherwise `C_I <= N`, and `N` is the preimage of a normal subgroup
`Nbar` of `Q/C_I = PE_n(U/I)`. If `N = C_I` we are in R4, and `L = PE_n(U/I)`.
If `N != C_I`, then `Nbar` is nontrivial, and it is proper because `N` is.
Suppose `Nbar` contains the image of `e_ij(r)` with `r in U/I`, and choose a
lift `rt` of `r`. Then `e_ij(rt) in N`, because `N` is the full preimage. By
[[elementary-root-kernel-equals-level]] this gives `rt in I`, so `r = 0`. This
is R3.

The four cases are mutually exclusive and exhaust all possibilities.

**`U/I` is simple in R4.** Let `I < J <= U` be a strictly larger ideal. By
(F2), `C_J` is normal in `Q` and contains `C_I = N`, since an element that is
central modulo `I` is central modulo `J`. Pick `a in J \ I`. Then `e_12(a) in C_J`,
but `e_12(a)` is not in `N` because the level of `N` is `I`. Maximality gives
`C_J = Q`, so `e_12(1) in C_J`, which forces `1 in J`.

## Step 2. Killers

Assume `Gamma` is perfect. Then every quotient `L` of it is perfect, and a
nontrivial simple quotient is nonabelian.

- **R1.** `L` is a quotient of `K`. If `K` has no nonabelian simple quotient,
  this is a contradiction.
- **R2.** If `[Q, C_I] <= E_n(U,I) <= N`, the image of `C_I` in `L = Q/N` is
  central. By `C_I N = Q` that image is all of `L`. Hence `L` is abelian,
  which is a contradiction.
- **R3.** Root detection for `PE_n(U/I)` says that `Nbar` contains a nontrivial
  root element, contradicting R3.

**R1 via `K_2` centrality.** Suppose `St_n(U) ->> Gamma ->> Q` is the canonical
factorisation. Then `K` is the image of `K_2(n,U)`. An image of a central
subgroup under a surjection is central, so `K` is abelian and has no
nonabelian simple quotient.

**R2 via `K_2` centrality.** Put `R = U/I` and `Q' = Q/E_n(U,I)`.

The image of `e_ij(a)` in `Q'` depends only on `a mod I`. The Steinberg
relations hold in `Q` for lifts. So `x_ij(r) -> e_ij(rt) E_n(U,I)` defines a
surjection `psi : St_n(R) ->> Q'`, and composing with the reduction
`Q' ->> E_n(R)` gives the canonical map `phi : St_n(R) -> E_n(R)`.

Let `Zhat = phi^{-1}(Z(E_n(R)))`. Every element of `C_I/E_n(U,I)` has its
`psi`-preimages in `Zhat`, so `C_I/E_n(U,I) = psi(Zhat)`.

Now `[Zhat, St_n(R)] <= ker(phi) = K_2(n,R)`. Suppose `K_2(n,R)` is central.
The three-subgroup lemma for normal subgroups gives

    [[G,G], Zhat] <= [[G,Zhat],G] [[Zhat,G],G] = 1

for `G = St_n(R)`, which is perfect for `n >= 3`. Hence `Zhat` is central in
`G`, so `C_I/E_n(U,I)` is central in `Q'`. Its image in `L` is then central.
In R2 that image is all of `L`, which is impossible since `L` is nonabelian.

## Step 3. Exact finiteness in R4

**(1 ⇒ 2).** Let `M` be in R4 and finitely normally generated. Then
`N = rho(M) = C_I` is normally generated in `Q` by finitely many elements
`x_1, ..., x_k`. Fix a finite generating set `F` of the ring `U`, and let
`d_m = (x_m)_11`. Let `I_0` be the two-sided ideal generated by these
finitely many elements:

- all off-diagonal entries of all `x_m`;
- the differences `(x_m)_ll - d_m`;
- the commutators `d_m f - f d_m` for `f in F`.

Each `x_m` is congruent modulo `I` to a central scalar, so `I_0 <= I`. Modulo
`I_0`, each `x_m` is a scalar `dbar_m I_n`. The unit `dbar_m` commutes with
the image of `F`, hence with the subring it generates, which is all of
`U/I_0`. So `x_m in C_{I_0}`. This is a normal subgroup of `Q` by (F2), hence

    C_I = N = <<x_1, ..., x_k>>_Q <= C_{I_0}.

For `a in I`, `e_12(a) in C_I <= C_{I_0}`, so `e_12(abar)` is a scalar modulo
`I_0`, and therefore `a in I_0`. Hence `I = I_0` is finitely generated.
Finally, `L = PE_n(U/I)` is simple by maximality, and it is finitely presented
by [[fp-quotient-iff-kernel-finitely-normally-generated]] (`Gamma` is finitely
presented and `M` is finitely normally generated).

**(2 ⇒ 1).** Let `I` be as in 2. Then `PE_n(U/I)` is nontrivial by (F2). Let
`M` be the kernel of the surjection `Gamma -> Q -> PE_n(U/I)`. Its quotient is
simple, so `M` is maximal proper normal, and `K <= M`. By (F2),
`rho(M) = C_I`, whose level is `I`. So `M` is in R4. The quotient is finitely
presented, so [[fp-quotient-iff-kernel-finitely-normally-generated]] makes `M`
finitely normally generated.

## Step 4. Chatterji--Kassabov specialisation

In [[ck-steinberg-marked-cover]], `U = Z[T]<p,q>/(p(1-g)q-1)` is finitely
generated. By [[universal-sandwich-ring-is-finitely-presented-and-injective]]
it is finitely presented, and `Z[T]` embeds in it. The element `1-g` is full,
and `Gamma` is finitely presented with `rho : Gamma ->> EL_4(U)`. In every
regime with `K <= M`, the subgroup `N = rho(M)` is proper normal in
`EL_4(U)`, so [[ck-envelope-level-ideal-screen]] item 4 embeds the core `S`
in `(U/lev(N))^x`.

`Gamma` is perfect: `Gamma = <<g>>` and `g in S = [S,S]`.

In R4, `U/I` is finitely presented because `U` is finitely presented and `I`
is finitely generated. So [[projective-elementary-fp-kernel-criterion]]
(`n = 4`) turns "PE_4(U/I) finitely presented" into clauses (b) and (c) of
the claim.

The consequence paragraph follows. Condition 2 gives a finitely normally
generated maximal kernel, and that is the hole. Under the killers, every
maximal kernel lies in R4, so 1 ⇔ 2 is the whole hole.
