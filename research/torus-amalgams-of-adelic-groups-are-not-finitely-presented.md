---
rg: 2
id: torus-amalgams-of-adelic-groups-are-not-finitely-presented
kind: claim
title: No amalgam of GL_n(Q), SL_n(Q) or Aff(Q) with a finitely generated group along a subgroup containing the torus is finitely presented, so prime mixing through the torus needs hidden relations for every prime-permuting group
distinct_from:
  prime-shift-hnn-groups-are-not-finitely-presented: that proves non-finite presentation for the prime shift H = Z through the quotient Z/2 x (Z wr Z); this proves it for every finitely generated second factor, including prime-permuting groups H whose quotient Z wr_P H is finitely presented, so that the quotient argument says nothing.
  prime-shift-kn-fp-reduces-to-a-metabelian-quotient: that is the Bieri--Strebel test for K_n; this is an obstruction in the Baumslag--Solitar relations, which a type (A) prime-permuting group does not remove.
  fg-restricted-product-actions-have-finite-support: that constrains monomial hosts of the adelic action; this constrains the presentation of amalgam envelopes, with no action assumed.
---

**ESTABLISHED** through `torus-amalgams-of-adelic-groups-are-not-finitely-presented-proof`. Refereed:
gq-referee-a PASS, proof-gap lens (report 9a409b0c2, fix W1 applied); gq-referee-b PASS, citation lens (report
581236183; Cornulier read at source). Elementary apart from the cited theorem of Cornulier, used only in item 4.
No priority is claimed for items 1--2.

**Setting.** Let `(Γ, C)` be one of the following pairs.
- `Γ = GL_n(Q)` or `SL_n(Q)` with `n >= 2`, and `C` any subgroup of `Γ` that contains the diagonal subgroup of
  `Γ` and meets the lower root group `x_21(Q)` trivially. Examples: the diagonal subgroup, the monomial
  subgroup, the upper triangular Borel subgroup, and the upper parabolics whose first block has size 1. (An upper
  parabolic with first block of size at least 2 contains `x_21(Q)`; for `C = Γ` the amalgam is just `B`.)
- `Γ = Aff(Q) = Q ⋊ Q^x` acting on `Q`, and `C = Q^x`, the dilations `m_r : x -> r x`. Write `τ : x -> x+1`.

Let `B` be a finitely generated group and `C -> B` an injective homomorphism. Put `Γ(Z) = GL_n(Z)`,
`SL_n(Z)` or `Aff(Z) = <τ, m_(-1)>`.

**Statement.**
1. **No torus amalgam is finitely presented.** `Γ *_C B` is finitely generated, by `Γ(Z)` and `B`, and it
   is not finitely presented.
2. **Where it fails.** For a finite set `S` of primes let `Γ_S = Γ ∩ GL_n(Z[1/S])` (for `Aff`,
   `Aff(Z[1/S])`), `C_S = C ∩ Γ_S`, and `E_S = (Γ_S *_(C_S) C) *_C B`. Then `Γ *_C B` is the directed
   colimit of the `E_S`. For every prime `p ∉ S` the Baumslag--Solitar relation `(BS_p)` holds in `Γ` and
   fails in `E_S`:
   - `GL_n`: `d_p^-1 x_21(1) d_p = x_21(1)^p` with `d_p = diag(p,1,...,1)`;
   - `SL_n`: `t_p^-1 x_21(1) t_p = x_21(1)^(p^2)` with `t_p = diag(p,p^-1,1,...,1)`;
   - `Aff`: `m_p τ m_p^-1 = τ^p`.
3. **Every prime-permutation amalgam.** Let `P` be the set of primes and `H` a finitely generated group
   acting on `P` with finitely many orbits. For `h in H` let `σ_h` be the automorphism of `Q^x` with
   `σ_h(-1) = -1` and `σ_h(p) = h·p`. Let `H` act on the monomial group `N_n(Q)` by applying `σ_h` to the
   diagonal entries, and on `Q^x` by `σ_h`. Then `N_n(Q) ⋊ H` and `Q^x ⋊ H` are finitely generated, so
   `Π_n^H = GL_n(Q) *_(N_n(Q)) (N_n(Q) ⋊ H)` (`n >= 2`) and `Π_1^H = Aff(Q) *_(Q^x) (Q^x ⋊ H)`
   are not finitely presented. For the prime shift `H = Z` these are the groups `Π_n` of
   `prime-shift-hnn-groups-are-not-finitely-presented`, item 1.
4. **The metabelian test cannot see this.** `Π_n^H / <<GL_n(Z)>> ≅ Z ≀_P H` for `n >= 2`, and
   `Π_1^H / <<Aff(Z)>> ≅ Z ≀_P H`, the permutational wreath product. By Cornulier's Theorem 1.1, `Z ≀_P H`
   is finitely presented exactly when `H` is finitely presented, its point stabilizers are finitely generated,
   and it has finitely many orbits on `P × P`.
   - **Example.** Fix a bijection `P -> Z[1/2]/Z` and let Thompson's group `T` act on `P` through it. `T`
     acts 2-transitively on `Z[1/2]/Z = T/F` (Cornulier, Example 3.5), with point stabilizers conjugate
     to `F`. So `Z ≀_P T` is finitely presented.
   - For such `H` the quotient argument of `prime-shift-hnn-groups-are-not-finitely-presented` and the
     Bieri--Strebel criterion of `prime-shift-kn-fp-reduces-to-a-metabelian-quotient`, item 4, give
     nothing, while item 3 still applies. For `H = Z`, `Z ≀ Z` is not finitely presented (Baumslag).
5. **Hidden relations.** Let `σ_(h,n)` be the permutation of `Q^n` applying `σ_h` in every coordinate
   (`σ_h(0) = 0`), and `K_n^H = <GL_n(Q), σ_(h,n) : h in H> ⊆ Sym(Q^n)`, and similarly `A_1^H ⊆ Sym(Q)`.
   - The inclusion of `GL_n(Q)` and the map `(m, h) -> m σ_(h,n)` on `N_n(Q) ⋊ H` agree on `N_n(Q)`, since
     `σ_(h,n) m σ_(h,n)^-1` is `m` with `σ_h` applied to its entries. So they define a surjection
     `Π_n^H -> K_n^H`, and likewise `Π_1^H -> A_1^H`.
     For `H = Z` acting by the shift, `K_n^H = K_n` and `A_1^H = A_1`.
   - If a quotient `K` of `Π_n^H` is finitely presented, then `Π_n^H -> K` is not injective: some relation
     of `K` fails in `Π_n^H`.
   - So finite presentation of `K_n^H` or `A_1^H` needs a relation that fails in `Π_n^H`, for every
     prime-permuting group `H`. That includes the `H` of item 4, for which the specific relation
     `e · diag(r,1,...,1)^-1 in <<GL_n(Z)>>` of the Bieri--Strebel test is no longer forced.
6. **Remark: conjugation keeps the exponent.** In any group containing `Γ`, if `f d_p f^-1 = d_q` with
   `q != p`, then `f` carries `(BS_p)` to `d_q^-1 v d_q = v^p` with `v = f x_21(1) f^-1`. No nontrivial
   `x_21(t)` satisfies that relation, since `d_q^-1 x_21(t) d_q = x_21(qt)`. So a prime-mixing element
   moves the dilation at `p` to the dilation at `q`, but it carries the `p`-relation to another
   `p`-relation, not to `(BS_q)`.

## Consequences for the root

- **Shape killed.** No type (A) actor for `SL_2(Q)`, `GL_n(Q)` or `Aff(Q)` is an amalgam of that group
  with a finitely generated group along the torus, the monomial group or the Borel subgroup. That covers
  the universal prime-shift group, every prime-permuting group `H`, and every twisted or Thompson-type
  group `B` attached along the torus.
- **What a prime-mixing actor must supply.** The relations `(BS_p)` for all but finitely many `p` must
  follow from finitely many relations. By item 6, conjugating the torus alone does not produce them. One
  uniform source is ring structure. In a Steinberg group `St_N(R)` the relations `x_ij(a) x_ij(b) = x_ij(a+b)`
  and `[x_ij(a), x_jk(b)] = x_ik(ab)` hold for all entries, and for a finitely presented ring `R` containing
  `Q` they follow from finitely many (`steinberg-groups-of-fp-rings-are-fp-in-rank-five`). Compare
  `z-localized-embeds-in-fp-kazhdan-steinberg-group` and `char-zero-representable-rings-embed-in-fp-simple-rings`.
- **The candidate prime-shift group `K_2^T`.** With `H = T` as in item 4, the prime-shift group `K_2^T` (not algebraic
  `K_2`) contains `GL_2(Q)` and is 2-transitive on
  `P^1(Q)`. As in `prime-shift-kn-fp-reduces-to-a-metabelian-quotient`, item 1, `k(tw) = σ_(φ(k))(t) k(w)`
  defines a homomorphism `φ` of `K_2^T` onto `T` that splits. The metabelian test only asks that the
  kernel `J` of `Z ≀_P T -> K_2^T / <<GL_2(Z)>>`, which lies in the base `Z[P]`, be finitely generated as a
  `Z[T]`-module. `J = 0` satisfies that. By item 5,
  the prime-shift group `K_2^T` can still be finitely presented only through a hidden relation. It is not recorded as a separate claim.
- **Calibration (MT-C).** The prime-shift group `K_2^T` acts on `Q^2`, not on a restricted product of thickenings of the
  `T_p`, so neither bound of `fg-restricted-product-actions-have-finite-support` or
  `sl-2-q-root-group-is-parabolic-in-every-prime-factor` constrains it. Its `u(1/m!)` is
  `diag(m!,1)^-1 u(1) diag(m!,1)`, with `diag(m!,1)` in the subgroup `<e, σ_T> ≅ Z ≀_P T`.
