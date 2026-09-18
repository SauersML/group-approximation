---
rg: 2
id: torsion-free-sofic-extrinsic-kazhdan-defect-kernel
kind: claim
title: Construct a sofic non-residually-finite Kazhdan kernel saturated by an extrinsic cyclic defect
distinct_from:
  torsion-free-sofic-singly-generated-kazhdan-defect-core: That stronger route asks for an intrinsic full-radical group before adjoining Z; here the defect need only saturate the kernel after the cyclic action is added.
  defect-saturation-full-mf-radical: That arithmetic quotient has an intrinsic full MF radical and unknown soficity; this asks instead for a sofic kernel whose radical behavior is caused extrinsically by its mapping torus.
  finitely-generated-rf-automorphism-mapping-torus-is-rf: That no-go theorem proves the kernel sought here must be non-residually finite.
  mapping-torus-mf-radical-lies-in-finite-residual: That sharper no-go proves the kernel sought here can have no nontrivial finite quotient at all.
  exact-kazhdan-radical-kernel-cannot-be-lef: That combines the no-finite-quotient condition with the Ozawa--Thom theorem to prove that the desired nontrivial Kazhdan kernel cannot be LEF.
  finite-outer-order-mapping-torus-is-virtually-product: That second no-go theorem shows the genuinely extrinsic route also needs an infinite-order outer action unless the kernel is already non-MF.
  steinberg-images-die-in-torsion-free-groups: That obstruction proves no nontrivial Steinberg image lies in a torsion-free group, which excludes every elementary-sourced kernel or compression source here; this is the positive construction problem that remains.
  mapping-torus-mf-radical-descends-through-kernel-radical: That computes a mapping-torus radical as a pullback from the mapping torus of the kernel's MF quotient; this is the construction problem that the reduction splits.
  filtered-torsion-certificates-die-on-perfect-kernels: That obstruction proves a perfect kernel is invisible to every separated-filtration or radical target, killing congruence, unipotent and radical torsion-freeness certificates; this is the construction problem, which must certify torsion-freeness by some other mechanism.
  mf-kazhdan-quotientless-mapping-torus-exact-radical: That is the purely extrinsic existence question for MF Kazhdan kernels, with no soficity or torsion-freeness; this needs a torsion-free sofic kernel with an explicit defect.
  compression-defects-need-strict-kernel-centralizer-towers: That obstruction proves a defect over an abelian quotient needs a strictly ascending, non-finitely-generated tower of Kazhdan centralizers in the kernel, killing every subgroup of a finite product of KCF and linear groups; this is the construction problem such a kernel must escape.
artifacts:
  - GroupApproximation/Sofic/NormalKazhdanMFRadical.lean
  - GroupApproximation/Sofic/SoficByAmenablePermanence.lean
  - research/torsion-free-lef-kazhdan-non-rf-seed.md
---

Construct a nontrivial torsion-free, sofic group `K` with no nontrivial finite
quotient,
with property `(T)`, an automorphism `phi in Aut(K)`, and a finitely
generated Kazhdan subgroup

```text
L <= G = K semidirectProduct_phi Z
```

such that `G` is finitely presented and `L` carries a one-sided compression
configuration with

```text
D_G(L) = K x {0}.                                      (EK1)
```

Preferably, `K` is itself finitely presented and one element normally
generates `K` in `K`.

This is strictly weaker than constructing a sofic group `K` with
`Rad_MF(K)=K`.  Indeed `K` may itself be MF: the compression defect in
`(EK1)` is an ambient phenomenon created by the cyclic action, just as an MF
lamp subgroup can become the exact MF radical of a non-MF wreath product.
The lower radical inclusion therefore has to be proved in `G`, not in `K`.

The absence of finite quotients is forced rather than cosmetic.
Property `(T)` makes `K` finitely generated.  By
`mapping-torus-mf-radical-lies-in-finite-residual`, the MF radical of `G` is
contained in the finite residual of `K`.  Thus `(EK1)` forces that finite
residual to equal `K`, equivalently that every finite quotient of `K` be
trivial.

This also forces `K` to be non-LEF.  By
`exact-kazhdan-radical-kernel-cannot-be-lef`, a countable LEF Kazhdan group
with no nontrivial finite quotient is trivial.  Thus exact finite local models
and all finite marked-limit constructions are excluded; any positive route
must build genuinely Hamming-approximate sofic models.

## Attempts

1. **Arithmetic linear kernels.**  Ordinary congruence and linear
   property-`(T)` candidates are residually finite.  The mapping-torus
   theorem rules them out even if an appealing automorphism can be written
   down.
2. **Intrinsic arithmetic saturation.**  The existing Hull--Osin quotient
   escapes residual finiteness and saturates one defect, but its soficity is
   unknown.  It remains a valid stronger route through
   `torsion-free-sofic-singly-generated-kazhdan-defect-core`.
3. **Sofic simple envelope.**  The unconditional simple sofic full-radical
   group is not presently known to be torsion-free, finitely presented, or
   Kazhdan, and supplies no controlled automorphism.  It cannot yet satisfy
   `(EK1)`.
4. **Thom's LEF Kazhdan group.**
   `thom-hyperlinear-kazhdan-without-factorization` supplies exactly a sofic,
   non-residually-finite Kazhdan seed, but the concrete group is not finitely
   presented and has a central element of finite order.  The first defect is
   no longer fatal: the target only requires its mapping torus to be finitely
   presented, so a finite automorphic presentation would suffice.  The known
   shift on Thom's concrete quotient is surjective but not injective, however,
   and the central torsion still rules that group out.  A useful variant must
   be torsion-free and carry an actual automorphism whose mapping torus has a
   finite presentation; it need not make `K` finitely presented.
   Passing to finite index cannot remove the torsion: the central element lies
   in the finite residual, so it lies in the kernel of the finite coset action
   associated to every finite-index subgroup and hence belongs to every such
   subgroup.
5. **The de Cornulier--Thom finitely presented variant.**  This repairs finite
   presentation but not the decisive clauses: its soficity is open and its
   centre contains the Prüfer group `Z[1/p]/Z`.  Every map from that divisible
   subgroup to a finite group is trivial, so every finite-index subgroup again
   contains torsion.  Its surjective noninjective dilation is not an
   automorphism and therefore does not define the required split extension.
6. **Titz--Witzel simple lattices.**
   `titz-witzel-simple-kazhdan-cat0-lattices-exist` supplies the complementary
   package: explicit finite presentation, torsion-freeness, simplicity,
   property `(T)`, non-residual-finiteness and one-element normal generation.
   Their soficity is not known.  Moreover, by
   `finite-outer-order-mapping-torus-is-virtually-product`, an MF instance
   would need an infinite-order class in `Out(K)` for a genuinely extrinsic
   obstruction; a finite-order outer action only gives a virtually direct
   product.
7. **Characteristic-zero Thom/Kida--Tucker-Drob seed.**
   `torsion-free-lef-kazhdan-non-rf-seed` now supplies unconditionally all
   four intrinsic kernel properties: finitely generated, torsion-free, LEF
   (hence sofic), non-residually-finite and property `(T)`.  This removes the
   former seed-existence gap, but the sharper finite-residual theorem now
   rules out the entire seed family.  Its characteristic centre has a
   nontrivial finitely generated residually finite linear quotient, so every
   automorphism mapping torus has MF radical contained in that centre.  This
   remains true for companion-matrix refinements and is independent of finite
   presentability or the choice of compression data.
8. **The finite-presentation strengthening is a separate open problem.**
   If this claim is strengthened by requiring `K` itself finitely presented,
   then `K` is a finitely presented sofic Kazhdan non-residually-finite group.
   This is exactly the existence question isolated as Open Problem 6.1 by
   Alekseev--Thom (2026); see
   `fp-kernel-crosses-alekseev-thom-open-problem`.
   The direct route should therefore first retain the infinitely presented
   kernel option and seek finite presentability only for the mapping torus,
   but the kernel must now be finite-residual-full rather than a central
   extension of a visible linear quotient.
9. **Finite marked limits are impossible.**  A marked limit of finite groups
   is LEF.  Combining this with property `(T)` and the required absence of
   finite quotients contradicts the Dadarlat--Ozawa--Thom quotient theorem.
   Hence the alternating-mother strategy cannot provide this kernel, even if
   its torsion and normal-generation gates could otherwise be controlled.
   *Stale (2026-09-17):* the general quotient statement used here is (EKL2),
   which `exact-kazhdan-radical-kernel-cannot-be-lef` records as false
   (witness `lef-kazhdan-group-without-finite-quotients-exists`); only the
   mapping-torus form (EKL1) remains, and it is open.  Item 9, and the
   non-LEF sentence of the statement above, therefore do not currently exclude
   LEF kernels.
10. **Elementary-sourced kernels and compression sources die at the Weyl word
    (2026-09-17, linear-characteristic).**
    `steinberg-images-die-in-torsion-free-groups` proves, from the Steinberg
    relations alone, that `w_12=x_12(1)x_21(-1)x_12(1)` has order dividing `8`
    in `St_n(R)` for every unital ring `R` and `n>=3`, and that one trivial
    Weyl word kills every root.  So every homomorphism from a normally
    elementary group to a torsion-free group is trivial.  Since `G` is
    torsion-free, the kernel `K` and the compression source `L` in `(EK1)`
    contain no nontrivial image of any `St_n(R)`; for such a source in `G`
    the defect `D_G(L)` is trivial.  If a normally elementary Kazhdan group has
    no finite quotients, it has no proper finite-index subgroup either, so
    neither quotients nor finite-index passage extract a torsion-free kernel.
    This kills as kernels or sources: the LEF Kazhdan group
    `EL_3(LC(X,F_q) semidirect Z)` (which revived LEF kernels after item 9
    went stale), the simple Kazhdan non-MF `EL_N` families, the Leavitt and
    Kun--Thom elementary sources, and the Kida--Tucker-Drob parabolic `H(R)`
    together with all its quotients.  The seed of item 7 escaped only by
    finite index in a group *with* finite quotients, which the mapping-torus
    theorem then excludes.  What survives on the linear side is exactly a
    relative group `EL_3(I)` over a finitely generated, noncommutative,
    additively torsion-free, idempotent-free rng with `I=I^2` (forced by
    `(STF3)`), for which no imported theorem gives property `(T)`; or a
    torsion-free infinite-index Kazhdan subgroup; or a non-elementary Kazhdan
    mechanism (buildings, small cancellation).
11. **Descent through the kernel radical (2026-09-17, operator-algebras).**
    `mapping-torus-mf-radical-descends-through-kernel-radical` proves
    `Rad_MF(K semidirectProduct_phi Z) = pi^{-1}(Rad_MF(Q semidirectProduct_psi Z))`
    with `Q = K/Rad_MF(K)`.  So a witness has either `Rad_MF(K) = K` (DI:
    intrinsic, and the automorphism is irrelevant), or yields `(XMF)`
    (DX): a nontrivial MF Kazhdan `Q` with no finite quotients, `[psi]` of
    infinite outer order, and `Rad_MF(Q semidirectProduct_psi Z) = Q`.  The
    genuinely extrinsic part of this hole is exactly
    `mf-kazhdan-quotientless-mapping-torus-exact-radical`, which needs neither
    soficity nor torsion-freeness.  Every Kazhdan compression source has degree
    `0`.  One attempt on `(XMF)` failed: periodizing corona almost-representations
    along `psi`.  It dies at the wrap-around step.  Closing the cycle up to
    `eps` in operator norm needs about `(C/eps)^{|S|d^2}` iterates, so the models
    must be accurate on balls that grow with `d`.  The wrap block has
    operator-norm weight `1`, not `1/N`.  Details are in the `(XMF)` node.
12. **Elementary groups as quotients, through rational relation covers
    (2026-09-17, group-rings).** Item 10 forbids elementary groups inside `K`,
    not as quotients of `K`. `kazhdan-rational-relation-cover-reduction`
    proves a criterion. Let `P ->> Q` be a finitely generated Kazhdan cover of
    a quotientless Kazhdan `Q`, and put `K = P/R_sat`, with `R_sat` the rational
    saturation of `[R,R]`. Then `K` is torsion-free exactly under (RLT): `l`-th
    powers of lifts of `l`-torsion stay non-torsion in `R^ab`. `[K,K]` is always
    a Kazhdan group with no finite quotient, and `K` embeds in
    `V semidirect Q`, which is sofic via Hayes--Sale when `V` is induced. With
    `Q = EL_3(LC(X,F_q) semidirect Z)`, the intrinsic clauses of this node
    reduce to the two independent inputs of
    `relation-cover-rational-lifting-over-quotientless-kazhdan`. The same note
    kills Steinberg covers and every finite-index elementary cover in
    characteristic `p`, via
    `[e_13(pN), e_32(pNu)] = e_12(pu)^{pN^2}`. Hyperbolic Belegradek--Osin
    covers remain untested. (EK1) is not addressed.
13. **Filtered torsion certificates (2026-09-17, linear-characteristic).**
    Item 10 kills elementary sources. This kills the standard *certificates* of
    torsion-freeness for any candidate, including the STF3 survivor `EL_3(I)`.
    `filtered-torsion-certificates-die-on-perfect-kernels` proves:
    - (PN1) a finitely generated perfect group maps trivially to every
      ultraproduct `prod_omega G_n` of groups with separated filtrations
      `[F^a,F^b] <= F^(a+b)`;
    - (PN2) a finitely generated rng with `I = I^2` maps to zero in radicals,
      separated ideal filtrations and norm-small Banach models;
    - (PN3) the same holds for virtually filtered targets of bounded index.

    The kernel here is perfect, because it is finitely generated and
    quotientless. So torsion-freeness cannot be certified through level-`q`
    congruence groups of unbounded rank (Minkowski coordinatewise), unipotent or
    `1 + radical` groups, residually torsion-free nilpotent or bi-orderable
    groups, or `I <= p M_N(Z)` for relative elementary groups, not even in
    ultraproducts.
    - *Invariant.* The minimal filtration depth of the generator images.
    - *Step where every member dies.* The finitely many perfect relations
      `s_i = prod [u,v]`, or `x = A x`, hold exactly in `omega`-most coordinates,
      where the depth doubles, or `1 - A` is invertible by Nakayama or a Neumann
      series.

    Survivors: geometric torsion-freeness (CAT(0) lattices), small cancellation
    or Dehn filling, extension-type certificates such as (RLT) of item 12,
    left-orderability, and linear models avoiding every fixed congruence level.
    This node stays OPEN.
14. **(EK1) descends modulo amenable normal subgroups (2026-09-17, reframing).**
    Item 13 is recorded on the live bus.
    `kazhdan-defect-descends-modulo-amenable-radical` is established. For a
    `phi`-invariant amenable `A normal K`, put `pi : G -> (K/A) semidirect Z`.
    - (AD1): `pi(D_G(L)) <= D(pi L)`.
    - (AD2): (EK1) holds iff the image of the defect is all of `K/A`. The
      quotient `K/D` is amenable and Kazhdan, so it is finite, so it is trivial.
    - (AD3): if `K/A` is KCF, then `D_G(L) <= A < K` for every `phi`
      preserving `A`.

    Consequences:
    - A witness kernel is not KCF even modulo its amenable radical.
    - This kills amenable extensions of Titz--Witzel lattices, including the
      rational relation covers over them from item 12, and amenable extensions
      of torsion-free hyperbolic Kazhdan groups, for every automorphism.
    - Saturation can be tested on `K/Rad_amen(K)`, which may have torsion and
      need not be sofic.

    On the relation-cover route with abelian kernel `A`, (EK1) splits into two
    prerequisites that can each fail:
    - (Sat): the descended defect saturates `Q`. It dies when `Q` is KCF
      modulo its amenable radical.
    - (Lift): exact centralizing roots exist iff the class `[f_c]` in
      `H^1(L; A)` vanishes (AD4). It dies for degree-0 roots of infinite
      order whenever `pi(L)` has torsion and `A` sits in an induced envelope
      (AD5). The reason: `z` must fix `l^m != 0`, and a finitely supported
      vector fixed by `x` forces `x` to have finite order.

    Over `EL_3(LC(X,F_q) semidirect Z)`, the scalar and diagonal roots of
    infinite order from the ring recipes can lift only with nonzero `Z`-degree.
    Not tested:
    - whether degree-nonzero roots can satisfy (AD4);
    - whether `H^1(L; A)` vanishes for torsion-free Kazhdan lifts of `EL_3(R_0)`.

16. **Sources infranormal in the kernel (2026-09-18, minimal-counterexample).**
    `infranormal-kernel-sources-die-in-sofic-mapping-tori` is ESTABLISHED. Let `G` be sofic with
    `G/K = Z`, `K` Kazhdan, and `L <= K` Kazhdan and infranormal in `K`. Put `N = <<L>>^K`.
    - (IS0): Kun--Thom makes `C_G(L) = C_G(N)`. So only compressors with `s^m N s^-m < N`
      strictly contribute to the defect, and they have degree `m != 0`.
    - (IS2): then `K/N` is an infinite non-Hopfian Kazhdan group.
    - (IS3): the defect lies in `< C_K(s^j N s^-j) >`. If it is all of `K`, finite generation and
      a Frobenius bound on the strict degree semigroup (gcd 1) make a translate of `N` central.
      Then `L` is finite, and no strict compressor exists.
    - (IS4): in general `D_G(L) <= U_0 ... U_(g-1)`, where the `U_rho` are proper normal
      subgroups of `K` permuted by `s`, and `g >= 2` is the degree gcd.

    Dead:
    - `L = K`, `L` normal in `K`, `L` normally generating `K`;
    - simple `K`, such as the Titz Mite--Witzel kernels, now with the compressor outside `K`;
    - every `K` with a unique maximal normal subgroup;
    - degree gcd 1.

    No torsion-freeness, finite presentation or quotientlessness is used.
    - *Invariant.* `<<L>>^K` and the strict degree semigroup.
    - *Step where every member dies.* The central-translate step of (IS3).

    Survivors:
    - sources `L` whose compressors in `K` generate a proper, non-Kazhdan subgroup;
    - necklace kernels `K = U_0 ... U_(g-1)` with `g >= 2`, which must also be non-tame in the
      sense of `compression-defects-need-strict-kernel-centralizer-towers`.
15. **Kernel centralizer towers (2026-09-17, reframing, swarm-0917-w6-w6-titz-last2).** This
    attempt extends the KCF kill of `abelian-extensions-kill-kcf-compression-defects` to its natural
    escape: products of KCF kernels, with the automorphism permuting or twisting the factors.
    `compression-defects-need-strict-kernel-centralizer-towers` (ESTABLISHED) proves the following
    for `K normal G` with `G/K` abelian, `L <= K` and `M = C_K(L)`.
    - (CT1) `D_G(L) = 1` if and only if every compressor `s` satisfies `s M s^-1 = M`. The inclusion
      `M <= s M s^-1` always holds.
    - (CT2) If `D_G(L) != 1`, some compressor `s` strictly compresses `L`, and `s^-1` strictly
      compresses `M`. The groups `C_K(s^j L s^-j)` form an infinite strictly ascending tower. Its
      union is not finitely generated and centralizes the intersection of the `s^j L s^-j`.
    - (CT3) If `s` has finite outer order on `K`, some `gamma in K` already realizes the tower.
    - *Class killed.* Tame kernels, meaning Kazhdan centralizers stabilize along every descending
      chain of Kazhdan subgroups. This class contains every subgroup of a finite product of KCF groups
      (Titz Mite--Witzel, torsion-free hyperbolic, torsion-free cocompact CAT(0) of dimension two)
      and linear groups. It includes `K_1 x K_2` and its fibre products, which are not KCF.
    - *Invariant.* The number of changes of `C_K(L_j)` along nested Kazhdan towers.
    - *Step where every member dies.* `[s,z] in C_K(s L s^-1) = s M s^-1 = M`, which puts `s z s^-1`
      back into `C_G(L)`.
    - *Forced biography of a witness.* A Kazhdan `L`, a nontrivial commuting partner `M`, and one
      element whose positive powers strictly compress `L` and whose negative powers strictly
      compress `M`.
    - The same kill applies to compression certificates for (XMF) on `Q semidirectProduct_psi Z`.

    This node stays OPEN.
