# Audit of the finite-presentation MF compiler

**Audited 2026-08-24--25 and resolved 2026-08-26.**  This note records the
obstructions found before the tensor-synchronization and Mikhailova
fiber-product repairs.  The historical failed shortcuts remain useful, but
the missing compiler described below is now supplied by a regular-MF benign
witness inside a direct product of free groups.

## 1. What is already complete

For finite presentation codes, MF has the arithmetical upper bound
`Pi^0_2`, and non-MF has the complementary `Sigma^0_2` upper bound.  For
recursive presentations, the free-factor switch is exact:

```text
W_e infinite  =>  H_e is MF,
W_e finite    =>  the fixed finitely presented non-MF group E embeds in H_e.
```

Consequently the only missing implication is an effective map from this
recursive family to finite presentations which preserves the MF branch and
the embedded `E` branch.

## 2. The positive specialization of the bridge

The Higman--Neumann--Neumann three-generator bridge starts from a countable
group `A`, forms `P=A*F(x,y)`, and adjoins `t` identifying

```text
a_i=x^-i y x^i,                 b_i=g_i a_i.
```

When `A=1`, the two families coincide.  Hence the positive specialization is

```text
Ext(1)=<x,y,t | [t,x^-i y x^i]=1, i>=0>,              (B1)
```

a central HNN of `F_2`.  By Shulman's central-HNN theorem its full group
C*-algebra is MF.  Thus the countable-to-finitely-generated bridge itself is
MF-safe on the collapsed branch; it is not the obstruction.

The older Lempp two-generator bridge gives a different fixed MF scaffold.
When the countable input is trivial, its relations reduce to the automorphism
HNN in which the stable letter swaps the two free generators.  This group is
virtually `F_2 times Z`, and hence is MF by the established commensurability
and free/maximal-tensor controls.  Again, finite generation is not the failing
step.

## 3. Exact form of the remaining rope edge

Let `F` be the finite-rank free group carrying the recursive presentation,
`N normal F` its relator subgroup, and `K` a finitely presented benign witness.
The rope construction first makes the central HNN

```text
Gamma=<K,v | [v,L]=1>,
```

where `L intersect F=N`.  Inside `Gamma`, put

```text
S=<F,F^v> = F *_N F.
```

There is a homomorphism

```text
tau:S -> Q=F/N
```

equal to the quotient map on the first copy of `F` and trivial on the second.
The final group is the graph HNN

```text
R=<Gamma times Q,u |
   u(s,1)u^-1=(s,tau(s)), s in S>.                    (R1)
```

Britton's lemma supplies the embedded `Q`, so the negative branch is correct.
The missing positive assertion is:

```text
Gamma and Q MF, with the rope data above  =>  R MF.    (R2)
```

Only `(R2)` is needed.  An arbitrary asymmetric HNN permanence theorem would
be much stronger.

## 4. Why the 2026 amalgam theorem does not prove (R2)

Shulman, *The MF property for amalgamated free products*,
arXiv:2603.13564v2, states:

- Theorem 10: `A *_C A` is MF for an MF `A`, with the same inclusion of `C`
  in both copies;
- Theorem 20: a general `A *_C B` is MF exactly when `A` and `B` admit
  matrix-corona embeddings agreeing on `C`;
- Theorem 24: maximal tensoring with `C*(F_N)` preserves MF;
- Theorem 25: central HNN extensions preserve MF.

For `(R1)`, the two copies of `S` are

```text
s |-> (s,1),             s |-> (s,tau(s)).             (R3)
```

They are not identical.  They become identical only when `Q=1`.  Equal traces,
large direct-sum multiplicities, or a common retraction do not produce the
exact equality in a matrix corona required by Theorem 20: a single unmatched
unitary block retains its operator norm no matter how small its normalized
rank is.

## 5. Why the positive quotient cannot simply be made trivial

Suppose a finitely generated recursive presentation has generators
`x_1,...,x_d` and an increasing stream of relator normal closures `N_s`.  If
the limit quotient is trivial, then every `x_i` belongs to `union_s N_s`.
There are finitely many `x_i`, so one stage contains all of them.  The quotient
is already trivial at that finite stage.

Therefore a monotone stream whose collapse is delayed exactly while a c.e.
set keeps enumerating cannot, after finite generation, use literal triviality
as its `INF` endpoint.  A nontrivial MF scaffold such as `(B1)` is forced.  This
is why Theorem 25 closes only a specialization that the reduction cannot
reach.

## 6. Other routes checked

### Graph and permutational lamps

A perfect non-MF lamp has a useful difference phenomenon: on two distinct
commuting sites, lamp differences normally generate both site factors, while
on a loop they collapse.  A full permutational wreath product, however, is
finitely presented only with finitely many diagonal orbits.  A graph-wreath
product relaxes this to finitely many edge orbits, but finite vertex orbits
conjugate the corresponding normal closures.  Killing one obligation then
kills its whole orbit, so it does not implement the required finite-prefix /
infinite-tail switch.

### A one-relator quotient of a fixed radical carrier

This cannot encode `INF`.  For fixed finite presentations and computable words
`q_e`, the predicate

```text
r belongs to normalClosure(q_e)
```

is recursively enumerable.  Its preimage cannot be the `Pi^0_2`-complete set
`INF`.  The fixed MF-radical computer correctly realizes halting in individual
radical words, but it does not turn a universal conjunction of those words
into one finite relator.

### Boone's modular-machine group

The final Boone stable letter is central over the lifted halting subgroup, so
Shulman's Theorem 25 controls that last step if its base is MF.  The machine
tower below it is a finite list of asymmetric HNN extensions between scaled
copies of the base `Z * Z^2`.  Totality changes subgroup membership detected by
the final letter; it does not remove the preceding HNN layers.  Thus the Boone
presentation is a finite packing device, not an MF-safe compiler by itself.

### Neumann diagonal products

A diagonal construction would solve the problem if one finitely presented
group contained independently killable, pairwise distinguishable non-MF
simple factors.  The repository's Neumann families use finite alternating
factors and are finitely generated rather than finitely presented.  Replacing
the factors by non-MF groups loses both the known finite-presentation mechanism
and the coordinate-isolation argument.

## 7. Status

### Two subsequent refinements

The positive half-row benign witness is MF-safe.  In the standard tower the
endomorphisms satisfy `xi_1=Ad(c^-1) o xi_0`.  If `t_0,t_1` are the two stable
letters, then `z=t_0^-1 c t_1` centralizes the base free group.  The first
tower is a residually finite free-group mapping torus, and the second is
therefore a central HNN extension of a regularly MF-realized group.  This is
recorded in `higman-half-row-has-regular-mf-benign-witness`.

The most direct symmetrization of `(R3)` does not work.  Two opposite quotient
coordinates make the graph embeddings conjugate by a coordinate swap, but in
the finite pre-quotient presentation the HNN letter then only swaps `(n,1)`
and `(1,n)` for `n in N`.  It never forces `n=1`.  See
`coordinate-swap-rope-does-not-compress-kernel`.

The audit correctly isolated two missing inputs.  They are now supplied as
follows.  The claim
`mikhailova-fiber-product-gives-regular-mf-benign-compiler` constructs the
ordinary benign witness in a finite direct product of free groups, so its
ambient group is regularly MF without tracking Higman's internal HNN tower.
The claim `regular-mf-tensor-sync-proves-twisted-rope-mf` tensors that faithful
regular realization with finite graph maps and proves MF permanence of `(R1)`
for the rope data.  Thus the graph edge `(R3)` and the pre-rope uniformity gap
are both accounted for in the final completeness proof.
