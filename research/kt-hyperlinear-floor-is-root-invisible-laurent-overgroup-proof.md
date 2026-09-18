---
rg: 2
id: kt-hyperlinear-floor-is-root-invisible-laurent-overgroup-proof
kind: route
title: Kill the SL_d part by a residually finite wreath, then read the floor's entry ring through the compressor-stable subring dichotomy
target: kt-hyperlinear-floor-is-root-invisible-laurent-overgroup
requires:
  - relative-embedding-is-commutant-separation
  - binary-free-and-ordinary-coset-wreaths-share-hyperlinearity
  - kt-compressor-commutant-collapse-is-all-or-nothing
  - kt-intermediate-coset-wreaths-are-nonsofic
---

Notation is as in the target. "Scalar RE" abbreviates scalar relative
embeddability of `L(K)<=L(G)`. External citations, all standard:

- **(Mal'cev)** A split extension `N semidirect Q` with `N` finitely generated
  residually finite and `Q` residually finite is residually finite. Finitely
  generated linear groups are residually finite.
- **(Gruenberg)** `A wr Q` with `A` abelian residually finite and `Q`
  residually finite is residually finite.
- **(Suslin 1977)** For a field `k` and `r>=3`,
  `SL_r(k[x_1,...,x_d])=E_r(k[x_1,...,x_d])`.
- Residually finite groups are sofic, and sofic groups are hyperlinear.

## 0. The floor exists and is conjugation-equivariant

`E` is finitely generated (`r>=3`, `R` finitely generated) and linear over the
domain `R`, hence residually finite. By Mal'cev, `G` is residually finite, so it
is hyperlinear. By `relative-embedding-is-commutant-separation`, the least
scalar-RE subgroup `K_Gamma` containing `Gamma` exists. It is the intersection,
over all canonical CE actor models `sigma` and all projections
`p in sigma(Gamma)' cap M`, of the commutation stabilizers of `p`. By
`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity` (items 1 and 6),
`W_K` is hyperlinear iff `K` is scalar RE, and by leastness this happens iff
`K_Gamma<=K` for `K>=Gamma`.

**Equivariance.** For `g in G`, `Ad lambda(g)` is a trace-preserving
automorphism of `L(G)` mapping the pair `L(C)<=L(G)` onto
`L(gCg^(-1))<=L(G)`. Scalar RE is a property of the pair up to such an
isomorphism, so `K` is scalar RE iff `gKg^(-1)` is. Leastness gives
`K_(gCg^(-1))=g K_C g^(-1)`.

## 1. Part (a): `K_Gamma<=E`

`E` is normal in `G`, so `G` acts on `G/E=SL_d(Z)` through the quotient, and `E`
acts trivially on the lamps. Hence

```text
W_E=(B x E) semidirect SL_d(Z) = E semidirect (Z/2 wr SL_d(Z)),
B=direct_sum_(SL_d(Z)) Z/2.
```

Here `Z/2 wr SL_d(Z)` acts on `E` through its `SL_d(Z)` quotient.
`Z/2 wr SL_d(Z)` is residually finite (Gruenberg), and `E` is finitely generated
and residually finite. By Mal'cev, `W_E` is residually finite, hence sofic and
hyperlinear. So `E` is scalar RE, `Gamma<=E`, and leastness gives
`K_Gamma<=E`. No hypothesis is used.

## 2. Part (b): compression

For `g in P_Gamma` we have `g Gamma g^(-1)<=Gamma`. The map `C -> K_C` is
monotone (`relative-embedding-is-commutant-separation`), and together with
Section 0 this gives

```text
g K_Gamma g^(-1)=K_(g Gamma g^(-1)) <= K_Gamma.
```

Every `L in SL_d(N)` is a compressor, since
`L Gamma L^(-1)=EL_r(beta_L R_+)<=EL_r(R_+)`.

## 3. Part (c): the entry ring of a compressed overgroup

Let `Gamma<=H<=E` with `LHL^(-1)<=H` for all `L in SL_d(N)`. Put

```text
M = R_+-span of { h v : h in H, v in R_+^r } subset R^r.
```

`M` contains `R_+^r` and is `H`-invariant, since `h(sum_k c_k h_k v_k)=sum_k c_k (h h_k) v_k`
with `c_k in R_+`. In particular `M` is `Gamma`-invariant.

**Step 1: `M=I^r` for an `R_+`-module `I`.** Let `I` be the set of all
coordinates of all vectors in `M`. Take `v in M` with `v_j=a`. For `i != j`,
`e_ij(1) in Gamma` gives `e_ij(1)v-v=a e_i in M`. Choosing `k != j` and
applying `e_jk(1)` to `a e_k` gives `a e_j in M`. So `a e_i in M` for every
coordinate `a` and every `i`. The `i`-th coordinate set is the image of `M`
under an `R_+`-linear map, hence an `R_+`-module, and it equals `I`. Therefore
`I^r=direct_sum_i I e_i<=M<=I^r`.

**Step 2: `I=(I:I)=D(H)`.** Each column `h e_k` lies in `M`, so every entry
of `h` lies in `I`, and `D(H)<=I`. The coordinates of `sum c_k h_k v_k` are
`R_+`-combinations of entries, so `I<=D(H)`. For `b in I` we have
`h(b e_k)=b(h e_k) in M=I^r`, so `b h_(ik) in I`. Hence every entry lies in
the ring `(I:I)={a in R : aI subset I}`. This ring is an `R_+`-module, so
`D(H)<=(I:I)`. Since `1 in R_+<=I`, `(I:I)<=I`. Thus `D(H)=I=(I:I)` is a
subring with `R_+<=D(H)<=R`.

**Step 3: stability.** For `L in SL_d(N)` and `h in H`, `LhL^(-1)` is
`beta_L` applied entrywise and lies in `H`. So `beta_L` maps entries to entries.
Since `beta_L` is a ring endomorphism with `beta_L(R_+)<=R_+`, it satisfies
`beta_L(D(H))<=D(H)`.

**Step 4: dichotomy.** The subring dichotomy lemma (Section 3 of
`kt-compressor-commutant-collapse-all-or-nothing-proof`, the route of the
established `kt-compressor-commutant-collapse-is-all-or-nothing`) reads
verbatim: "Let `d>=3`. Let `S` be a subring with `R_+ <= S <= R` and
`beta_L(S) subset S` for every `L in SL_d(N)`. Then `S=R_+` or `S=R`." Hence
`D(H) in {R_+,R}`.

**Step 5: `D(H)=R_+` iff `H=Gamma`.** If `D(H)=R_+`, then `H` consists of
matrices over `R_+` whose inverses are also in `H`, with determinant `1`
because `H<=E<=SL_r(R)`. So `H<=SL_r(R_+)=EL_r(R_+)=Gamma` by Suslin, and
`H=Gamma`. Conversely `D(Gamma)=R_+`.

By Parts (a) and (b), `H=K_Gamma` satisfies the hypotheses of (c).

## 4. Part (d): the wall passes to the floor

Suppose `E` is not contained in `K_Gamma`. By the description of `K_Gamma` in
Section 0, there are a canonical CE actor model `sigma : G -> U(M)`, a
projection `p in sigma(Gamma)' cap M` and `e in E` with `sigma(e)p != p sigma(e)`.
Then `u=2p-1` is a unitary in `C_0=C_(U(M))(sigma(Gamma))` that does not commute
with `sigma(e)`, so condition 4 of
`kt-compressor-commutant-collapse-is-all-or-nothing` fails for `pi=sigma`. That
theorem holds for every homomorphism into every group, so the **wall
alternative** holds for `sigma`:

- `Gamma^sat cap U_kl(R)=U_kl(R_+)`, where `Gamma^sat` is the set of `g` such
  that `sigma(g)` commutes with `C_0`;
- condition 8 fails, so no `diag(x^m,x^(-m),1,...,1)` with `m != 0`
  normalizes `C_0`.

Every `g in K_Gamma` commutes with every projection of `sigma(Gamma)' cap M`.
A von Neumann algebra is the norm-closed span of its projections, so `g`
commutes with all of it, and `K_Gamma<=Gamma^sat`. Hence
`K_Gamma cap U_kl(R)<=U_kl(R_+)`, with equality because `Gamma<=K_Gamma`.

A torus in `K_Gamma` would commute with `C_0` and so normalize it, which is
excluded. If `EL_r(S)<=K_Gamma` with `S` not contained in `R_+`, then
`e_12(f)` with `f in S \ R_+` would lie in `K_Gamma cap U_12(R)`, which is also
excluded.

## 5. Trichotomy

By (a), `Gamma<=K_Gamma<=E`.

- If `K_Gamma=E`, every element of `E` commutes with every `Gamma`-central
  projection in every canonical CE actor model. So condition 4 of the
  all-or-nothing theorem holds in each such model, and with it condition 2
  ((CCR) for every compressor). Every `K>=Gamma` with `E` not contained in `K`
  fails `K_Gamma<=K`, so `W_K` is non-hyperlinear.
- If `K_Gamma=Gamma`, then `W_Gamma` is hyperlinear.
- Otherwise `Gamma<K_Gamma<E`. By (c) and Step 5, `D(K_Gamma)=R`. By (b), the
  subgroup is compressed, and by (d) it contains no non-polynomial root and no
  torus. `W_(K_Gamma)` is hyperlinear by Section 0. It is nonsofic by
  `kt-intermediate-coset-wreaths-are-nonsofic`, since `Gamma<=K_Gamma` and the
  normal closure `E` is not contained in `K_Gamma`. `W_Gamma` is
  non-hyperlinear, because `K_Gamma != Gamma`.

The three cases are mutually exclusive, since `Gamma != E`.

**Decomposition of the `W_Gamma` route to `non-hyperlinear-group`.** `W_Gamma` is
non-hyperlinear iff `K_Gamma != Gamma`, iff (by (a)) some `h in E \ Gamma`
lies in `K_Gamma`. By (c), any such `h` forces `D(K_Gamma)=R`. By (d), `h` is a
root or a torus only when case 1 holds. The target therefore splits into:

1. the strong target: force one Laurent root into `K_Gamma`, which is
   equivalent to case 1 and to (CCR) in every canonical model; or
2. the weak target: force one element of `E \ Gamma` into `K_Gamma`.

The weak target follows from the strong one. If case 3 holds, the weak target
holds and the strong one fails. So a witness for the weak target that is a root
or a torus already proves case 1. A witness of any other shape cannot come from
a root-by-root commutation argument.
