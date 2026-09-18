---
rg: 2
id: kazhdan-defect-descends-modulo-amenable-radical-proof
kind: route
title: Push the defect generators through the amenable quotient, then recover the kernel because a Kazhdan amenable quotientless group is trivial
target: kazhdan-defect-descends-modulo-amenable-radical
requires:
  - abelian-extensions-kill-kcf-compression-defects
  - kazhdan-rational-relation-cover-reduction
---

Notation is as in the claim. `A <= K` is normal in `K` and `phi(A) = A`, so `A x {0}`
is normal in `G`, and `Gbar = G/A = (K/A) semidirectProduct_psi Z`, where `psi` is induced by
`phi`.

**Amenable radical.** If `A_1` and `A_2` are amenable normal subgroups, then so is `A_1 A_2`: it is
an extension of `A_1` by `A_1A_2/A_1 ~= A_2/(A_1 cap A_2)`. So the amenable normal subgroups form
a directed family. Its union `Rad_amen(K)` is a directed union of amenable groups, hence amenable
and normal. It contains every amenable normal subgroup, so every automorphism preserves it.

**(AD1).** Let `s in Comp_G(L)`. Then `pi(s) pi(L) pi(s)^-1 = pi(s L s^-1) <= pi(L)`, so
`pi(Comp_G(L)) <= Comp_Gbar(pi L)` and hence `pi(G_comp(L)) <= Gbar_comp(pi L)`. If `z`
centralizes `L`, then `pi(z)` centralizes `pi(L)`. So `pi` maps every generator
`[g z g^-1, l]` of `D_G(L)` to a generator of `D_Gbar(pi L)`. Since `pi` is surjective, the image of
a normal closure is the normal closure of the image. This gives `pi(D_G(L)) <= D_Gbar(pi L)`.

Every generator is a commutator, so it has `Z`-degree `0`, and `D_G(L) <= K x {0}` for any `L`.
If `L` is Kazhdan, its image in `Z` is an abelian quotient of a Kazhdan group, hence finite, hence
trivial. So `L <= K x {0}`.

**(AD2).** Put `D = D_G(L) <= K`. If `D = K` then `pi(D) = K/A`. Conversely, suppose
`pi(D) = K/A`, so `DA = K`. Then

```text
K/D = DA/D ~= A/(A cap D),
```

so `K/D` is amenable, as a quotient of `A`. It is also Kazhdan, as a quotient of `K`. A discrete
amenable group with property (T) is finite: the trivial representation is weakly contained in
`l^2`, so (T) gives a nonzero invariant vector in `l^2`. So `K/D` is a finite quotient of `K`,
hence trivial, and `D = K`.

**(AD3).** Let `A` be `phi`-invariant, amenable and normal, with `Kbar = K/A` KCF. Let `L <= G` be Kazhdan and put
`Lbar = pi(L) <= Kbar` (by (AD1)).

- If `Lbar = 1`, every generator of `D_Gbar(Lbar)` is `[.,1] = 1`.
- If `Lbar != 1`, take `s in Comp_Gbar(Lbar)`. The conjugate `s Lbar s^-1` is a nontrivial Kazhdan
  subgroup of `Kbar`, so `C_Kbar(s Lbar s^-1) = 1`. This is hypothesis (AX) of
  `abelian-extensions-kill-kcf-compression-defects` for `Kbar normal Gbar`, with abelian quotient
  `Z`. Its Lemma gives `D_Gbar(Lbar) = 1`.

By (AD1), `D_G(L) <= A`. If `A = K`, then `K` is amenable and Kazhdan, hence finite, hence trivial,
because it has no nontrivial finite quotient. So for `K != 1` we get `D_G(L) <= A < K`, and (EK1)
fails. The automorphism `phi` entered only through `phi(A) = A`, which is automatic for a
characteristic subgroup such as `Rad_amen(K)` or `Z(K)`. Torsion was not used.

*When the extension kernel is the amenable radical.* Suppose `1 -> A -> K -> H -> 1` with `A`
amenable. If `H` has no nontrivial amenable normal subgroup, then the image of `Rad_amen(K)` in
`H` is trivial, so `Rad_amen(K) = A`. This holds when:

- `H` is simple and non-amenable;
- `H` is torsion-free non-elementary hyperbolic. An amenable normal subgroup of a non-elementary
  hyperbolic group is finite, since an infinite normal subgroup contains loxodromics with
  independent fixed points and hence a free subgroup.

**(AD4).** Let `A` be abelian, written additively, with `K` acting by conjugation. The action
factors through `K/A`; the `Z`-generator acts through `phi`. Let `cbar` centralize `Lbar = pi(L)`
and let `c` be a lift. For `l in L`, `pi(c l c^-1 l^-1) = 1`, so `f_c(l) = c l c^-1 l^-1 in A`.

- *Cocycle.* `f_c(l l') = c l c^-1 (c l' c^-1 l'^-1) l^-1 = f_c(l) + l . f_c(l')`, so
  `f_c in Z^1(L; A)`.
- *Change of lift.* The lifts of `cbar` are exactly the elements `a c` with `a in A`. Then

  ```text
  f_{ac}(l) = a (c l c^-1 l^-1) (l a^-1 l^-1) = f_c(l) + a - l.a = f_c(l) - (delta a)(l),
  ```

  with `(delta a)(l) = l.a - a`.
- *Conclusion.* Some lift centralizes `L` iff `f_{ac} = 0` for some `a`, iff `f_c` is a
  coboundary.
- *Restriction to `L cap A`.* Elements of `A` act trivially on `A`, so `delta a` vanishes there.
  Hence a centralizing lift forces `f_c(a) = c a c^-1 - a = 0` for `a in L cap A`.

**Root gate.** Let `K` be torsion-free, and take `l in L` with `pi(l)` of finite order `m >= 2`.

- Then `l != 1`, so `l^m != 1` by torsion-freeness. Also `l^m in A cap L`.
- Any `z in C_G(L)` commutes with `l^m`, so it fixes the nonzero element `a = l^m` of `A`.

**(AD5).** Let `iota : A -> (+)_{q in Q} W` be injective and `Q`-equivariant, where `Q = K/A`.
Here `Q` moves supports by left multiplication: `supp(x . v) = x supp(v)`. This holds for the
translation action, and for a diagonal action with any `Q`-action on `W`.

- Let `z in C_K(L)` have degree `0`. Its conjugation action on `A` is the action of
  `x = pi(z) in Q`. By the root gate, `x` fixes `v = iota(l^m) != 0`.
- So `x supp(v) = supp(v)`, a finite nonempty set.
- Hence `x^N` fixes a point `y` of `supp(v)` for some `N >= 1`, that is, `x^N y = y`, and
  `x^N = 1` in `Q`.
- So `pi(z)` has finite order.

The action of a root of nonzero degree involves `phi` on `A`, which is not a translation, so it is
not controlled.

**Relation covers.** `kazhdan-rational-relation-cover-reduction` gives `K = P/R_sat` with
`A = R/R_sat` torsion-free abelian, and `K -> V semidirect Q` injective with `A -> V`
`Q`-equivariant. So clause 2 there supplies exactly the hypothesis of (AD5). The witness kernel is
`D = [K,K]`; apply the statements to `D` with `A cap D`. `D` is Kazhdan and quotientless by item 3
of that node, and `A cap D` is abelian normal. For Titz Mite--Witzel `Q`, the quotient `D/(A cap D)`
is `Q`, which is KCF. The amenable radical of `D` contains `A cap D`, and `D/Rad_amen(D)` is a
quotient of the simple group `Q`. It is not trivial, since `D` is not amenable. So it equals `Q`,
and (AD3) applies. `QED`

**Calibration.**

- *Amenability is what (AD2) uses.* Replace `A` by a non-amenable normal subgroup: `K/D` is then
  only a Kazhdan quotientless quotient of `A`, which can be nontrivial.
- *(AD3) is strictly stronger than the KCF kill.* A torsion-free central extension `K` of a KCF
  quotientless Kazhdan group has `Z(K) != 1`, so `K` is not KCF, but `K/Z(K)` is.
- *(AD5) is sharp in the degree.* Only the degree-0 part of `C_G(L)` is constrained. Roots `k t^n`
  with `n != 0` act by `pi(k) o phi_*^n` and may fix vectors.
