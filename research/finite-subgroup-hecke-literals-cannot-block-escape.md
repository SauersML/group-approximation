---
rg: 2
id: finite-subgroup-hecke-literals-cannot-block-escape
kind: claim
title: A finite-subgroup Hecke literal is either zero or remains in the finite packet
distinct_from:
  involution-hecke-corner-has-no-proper-literal-projections: that treats the bare rank-one C2 plus corner and gets only zero or the corner unit; this handles every projection in every finite subgroup algebra and identifies the first nonminimal proper example.
  finite-support-central-corners-are-finite-normal-twisted-sectors: that classifies central finite-support corners through finite normal subgroups; this needs no centrality or normality and instead classifies single literal compressions qgq when q lies in an arbitrary finite subgroup algebra.
  root-block-piecewise-transport-cannot-host-nonce-bcs: that rules out a whole compatible atlas kept in one finite root matrix block; this proves that every nonzero single-literal projection is automatically trapped in the finite root packet.
---

Let `H <= Gamma` be finite and let `q=q^*=q^2 in C[H]`.  Write

```text
q=sum_(s in H) a_s s.
```

If `g in Gamma` and `p=qgq` is a projection in `qL(Gamma)q`, then

```text
p!=0  implies  g in H,                                  (FHL1)
```

and hence every nonzero such projection belongs to the finite-dimensional
corner `qC[H]q`.  The proof is the canonical coefficient calculation

```text
tau(p)=tau(gq)=a_(g^-1)  if g^-1 in H,
tau(p)=0                 if g notin H.                  (FHL2)
```

A nonzero projection has positive faithful trace, proving `(FHL1)`.
Therefore no amalgam or HNN letter outside `H` can provide a nonzero
single-literal projection through the same finite-support corner.

Two useful extremal cases are completely classified.

1. For the subgroup average

   ```text
   q_H=|H|^(-1) sum_(h in H) h,
   ```

   the double-coset sum `q_H g q_H` is nonzero for every `g` (all its group-
   basis coefficients are nonnegative and at least one occurs).  If it is a
   projection, `(FHL1)` gives `g in H`, and then
   `q_H g q_H=q_H`.  Thus a subgroup-average Hecke literal is a projection
   exactly for `g in H`, and it is never a proper projection.
2. If `q` is a minimal projection of the finite-dimensional C-star algebra
   `C[H]`, then `qC[H]q=Cq`.  By `(FHL1)`, every projection `qgq` is therefore
   `0` or `q`.  This includes arbitrary rank-one matrix-coefficient
   projections in an irreducible Fourier block, not only the C2 corner.

The first possible proper example is consequently **nonminimal**, and corner
dimension two already suffices.  Take

```text
H=C_2 times S_3,
rho_1=chi times 1,       rho_2=chi times sigma,
```

where `chi` is the nontrivial character of `C_2` and `sigma` is the standard
two-dimensional representation of `S_3`.  Let `t` be a transposition, choose
unit eigenvectors `v_+,v_-` of `sigma(t)` with eigenvalues `+1,-1`, and put
`xi=(v_++v_-)/sqrt(2)`.  Under the Fourier decomposition of `C[H]`, define
`q` to be rank one in the `rho_1` block, the rank-one projection onto `xi` in
the `rho_2` block, and zero in every other block.  Then `epsilon(q)=0`,

```text
q C[H] q = C directSum C,
g=(1,t),
q g q = (1,0),                                         (FHL3)
```

because `rho_1(g)=1` and
`<xi,sigma(t)xi>=0`.  Thus `(FHL3)` is a nonzero proper canonical projection
and proves that nonminimal finite-type corners are the sharp local escape
from the minimal/average obstruction.

It is still a finite-packet escape only.  If all variable projections of the
Paddock--Slofstra BCS have the form `qg_xq` for one `q in C[H]`, `(FHL1)`
puts every nonzero one in `qC[H]q`; the zero ones are there as well.  The
tuple would give a finite-dimensional tracial BCS model, contradicting its
non-`R^U` property.  Finite groups, amalgams and HNN extensions therefore
cannot compile the BCS through **single** double-coset literals sharing a
finite-subgroup corner, even though proper local literals such as `(FHL3)`
exist.

Noncentrality matters for the structural endpoint.  Put the example above
inside `Gamma=H*Z`.  This free product has no nontrivial finite normal
subgroup, while the same noncentral `q` and proper literal `(FHL3)` persist.
Hence an arbitrary noncentral finite-subgroup corner need not lie in one of
the finite-normal twisted sectors classified by
`finite-support-central-corners-are-finite-normal-twisted-sectors`; the
single-literal trap `(FHL1)` is strictly different and does not require such
a reduction.

For a completely arbitrary noncentral finite-support projection
`q=sum_(s in S)a_s s in C[Gamma]`, the same calculation gives only

```text
qgq is a nonzero projection  implies
g^(-1) in S and a_(g^-1)=tau(qgq)>0.                    (FHL4)
```

Thus a shared finite-support corner permits only finitely many nonzero
literal group elements, all already visible in its own support.  Nothing in
`(FHL4)` forces `S` to generate a finite or finite-normal subgroup.  Such a
claim would be a general support theorem for algebraic group-ring
projections, far beyond the finite-Hecke calculation and unavailable in this
generality.  Central `q` is exactly the case where the existing finite-normal
twisted-sector theorem supplies that stronger conclusion.

