---
rg: 2
id: unconfined-quasi-regular-algebras-lack-algebraic-infiniteness
kind: claim
title: The rank-four compression subgroup of EL_n over the Leavitt algebra is unconfined, so the compressed quasi-regular algebra surjects onto the reduced algebra and can be infinite only through a gapped quasi-regular spectrum that the regular representation does not see
distinct_from:
  stably-finite-msg-rung-is-one-universal-algebra: that shows SF(E,L) forces A_q(E,L,u) and C*_max(E) to be infinite and names the production of a proper isometry as the step where Kazhdan-free arguments die; this proves where in A_q any such isometry must live (a unitary modulo the kernel of a surjection onto C*_lambda(E)), kills every group-ring and trace-visible source, and brackets the sub-prerequisite between two single-representation spectral statements.
  elementary-root-subgroups-over-crossed-products-are-not-confined: that proves abelian root subgroups over crossed products are unconfined, for C*-simplicity; this proves the non-amenable stabiliser Stab(e_n), which contains the EL_3 corner, is unconfined over the Leavitt algebra, and uses it for weak containment of the regular representation in a quasi-regular one.
  cstar-simple-iff-amenable-subgroups-not-confined: that is Kennedy's theorem about amenable subgroups and simplicity of C*_lambda; this concerns a non-amenable subgroup and the finiteness of the quasi-regular algebra, not simplicity.
  universal-fixed-projection-forces-kazhdan-subgroup: that kills relative (T) as a source of a universal fixed projection in C*(Gamma); this is about one quasi-regular representation, where the surviving source is a gapped spectral piece in that representation alone.
artifacts:
  - research/unconfined-quasi-regular-infiniteness-proof.md
  - research/stably-finite-msg-rung-is-one-universal-algebra.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED (written proof; not Lean-verified).**  This is an
obstruction and a decomposition for the sub-prerequisite that
`stably-finite-msg-rung-is-one-universal-algebra` isolates: a
Property-`(T)`-free proof that `A_q(E,L,u)` is not stably finite.

**Notation.**  `R=L_(F_2)(1,2)` with `t_i s_j=delta_ij` and
`s_0t_0+s_1t_1=1` (eq. (leavitt) of `non_mf_groups_exist.tex`), and
`E=EL_n(R)` with `n>=4`.  Here `n=20` is the case of the goal.  `L=EL_3(R)`
sits on coordinates `1,2,3`.  `u` is the element of
`lem:ring-compression-cell`, and `M=uLu^-1`, a proper subgroup of `L`.
`pi=lambda_(E/M)`, `A_q=C*_pi(E)` and `J_q=ker(A_q->C*_lambda(E))` (item
2).  A subgroup `H<=G` is **confined** if some finite `F` inside `G\{1}`
meets every conjugate of `H`.  Otherwise it is **unconfined**.

1. **The compression subgroup is unconfined.**  `Q=Stab_E(e_n)`, the
   stabiliser of the last standard column, is unconfined in `E`.  Hence
   so are its subgroups, including `L`, and their conjugates, including
   `M`.  The input on `R` is that `cR` is infinite for every nonzero `c`.
   It follows from `t_0s_0=t_1s_1=1` and `t_1s_0=0`.
2. **Weak containment of the regular representation.**  For a countable
   group `G` and an unconfined `H`, `lambda_G` is weakly contained in
   `lambda_(G/H)`.  So there is a surjection `Phi:C*_(lambda_(G/H))(G)->C*_lambda(G)`
   with `Phi(lambda_(G/H)(g))=lambda_G(g)`.  In particular,
   `lambda_(G/H)` is injective on `C[G]`, and `tau_q=tau o Phi` is a
   tracial state that is faithful on every `M_k(lambda_(G/H)(C[G]))`.
3. **No algebraic or trace-visible infiniteness (for any `rho` with
   `lambda_G` weakly contained in `rho`).**  Let `A=C*_rho(G)` and `J=ker Phi`.
   - (a) Every isometry `s` in `M_k(A)` is unitary modulo `M_k(J)`.  Its
     defect `1-ss*` lies in `M_k(J)`, and `tau_q` kills it.
   - (b) `M_k(rho(C[G]))` contains no proper isometry.  More strongly,
     no nonzero projection of `M_k(rho(C[G]))` is Murray-von Neumann
     equivalent to a subprojection of a defect `1-ss*`.
   - (c) `A` is stably finite unless the following holds.
     **GQE(rho):** there are `k` and `b=b*` in `M_k(C[G])` with
     `||lambda(b)||<=1/4`, `sp(rho(b))` contained in `[-1/4,1/4] u [3/4,5/4]`,
     and `sp(rho(b))` meeting `[3/4,5/4]`.  GQE is equivalent to
     `M_k(J)` containing a nonzero projection for some `k`.
4. **Sandwich for the Leavitt sub-prerequisite.**  For
   `(E,L,u,M,pi)` as above:
   ```text
   MSG_L(pi)  ==>  A_q(E,L,u) is not finite  ==>  A_q is not stably finite  ==>  GQE(pi).
   ```
   `MSG_L(pi)` means that `1` is isolated in `sp(pi(h_S))`.  The first
   implication is item 3 of `stably-finite-msg-rung-is-one-universal-algebra`,
   applied to the single representation `pi`: `delta_M` is `M`-fixed but
   not `L`-fixed.  Both ends are statements about the one representation
   `lambda_(E/M)`.  `MSG_L(pi)` is equivalent to a uniform Kesten gap for
   the family of Schreier graphs of `L` on
   `L/(L cap yMy^-1)`, for `y` in `L\E/M`.  The gap is taken on the
   complement of the constants for finite orbits and on all of `l^2` for
   infinite ones.
5. **Sharpness: the unconfinement hypothesis cannot be dropped.**  Let `V`
   act on the orbit `X` of any point of the Cantor set.  An involution
   `g`, its conjugate `g'=hgh^-1` equal to `g` on the `g`-invariant clopen
   `A' u gA'` and trivial elsewhere, `P=(1-pi_X(g))/2` and
   `P'=(1-pi_X(g'))/2` satisfy `P'<P`.  So `w=pi_X(h)P+(1-P)` is a proper
   isometry with entries in `pi_X(C[V])`.  By items 2 and 3, point
   stabilisers of `V` are confined, as they are: `g'` and `gg'` have
   disjoint supports.  So item 3(b) fails without the unconfinement
   hypothesis.

## The class it kills, and the invariant

**Invariant:** unconfinement of `M` (equivalently of `L`) in `E`.  This
means that `{1}` lies in the Chabauty closure of the conjugacy class.  It
gives `lambda_E` weakly contained in `lambda_(E/M)`.

**Killed.**  Every argument that makes `A_q(E,L,u)`, or any matrix algebra
over it, infinite by one of the following means:
- a finite-subgroup projection such as `(1-pi(g))/2`, for instance for
  the involutions `e_ij(r)` (every one is an involution in characteristic
  `2`), or a V-style compressible involution;
- a partial translation with group-ring coefficients;
- any other identity in `M_k(C[E])`;
- any defect projection detected by the regular trace, or equivalent to
  a projection with nonzero image in `C*_lambda(E)`.

**Failing step.**  The defect `1-ss*` must lie in `M_k(J_q)`.  But
`M_k(pi(C[E]))` meets `M_k(J_q)` only in `0`, and `tau_q` vanishes on
`J_q`.  The same holds verbatim for `C*_max(E)`, with `J=ker lambda`, and
for every completion of `C[E]` above `lambda`.

**Survives.**  Only a *gapped spectral piece* survives: a self-adjoint
group-ring matrix whose quasi-regular spectrum has an isolated part that
the regular spectrum lacks (GQE).  The Kazhdan projection is the special
case `b=f(h_S)`.  The Property-`(T)`-free question is therefore exactly
spectral, in one representation.

## Consequence for the Leavitt goal

`property-t-free-leavitt-full-mf-radical` reaches `SF(E,L)` through
`stably-finite-msg-rung-is-one-universal-algebra`.  That route now has the
following checkable, independently failing prerequisites:
- (P1) `GQE(lambda_(E/M))`, which is necessary;
- (P2) the sharper `MSG_L(lambda_(E/M))`, a uniform Kesten gap for the
  double-coset family of Schreier graphs `L/(L cap yMy^-1)`, which is
  sufficient for the infiniteness;
- (P3) the parallel `GQE` for `C*_max(E)`, which is necessary for
  `C*_max(E)` not stably finite.

Each is weaker than `(T)` and concerns a single representation.  None
can be discharged by algebra in `C[E]`.

Proof route: `unconfined-quasi-regular-infiniteness-proof`.
