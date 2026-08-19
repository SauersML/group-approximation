# Two empty quantifiers in the wall problem: trace energy and commutant density

Date: 2026-08-14

## 1. Outcome

Two numerical parameters appear throughout the Kun--Thom Clifford lane: the
*energy* of a relative wall (how far the compressed lamp moves in normalized
Hilbert--Schmidt norm) and the *density* of the relative commutant (the
normalized dimension count that kills every exact finite-dimensional model).
Neither is a real parameter.

```text
(E)  Any relative wall in a Connes-embeddable model amplifies,
     by diagonal tensor powers, to a wall of energy at least
     sqrt(2) - epsilon.  Demanding the maximal-energy wall of
     (CHI8)/(WFI4) costs nothing over demanding a bare one.

(D)  The normalized commutant density of a tracial model is a
     function of its character alone.  It is therefore exactly
     equal for Gamma and for t Gamma t^(-1), and it vanishes
     identically in every model whose character is supported at
     the identity.  No dimension count can obstruct the wall.
```

`(E)` strengthens the hypotheses of
`TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md` and of
Corollary 8 of `TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md`: their
conclusions now follow from the mere *existence* of a wall.

`(D)` answers, negatively and with a proof, the natural attempt to transport
the Kun--Thom obstruction to the tracial ultraproduct by counting.  Kun--Thom
Theorem 4.1 is proved by controlling isotropy orders and orbit cardinalities
in a permutation model, and the exact-representation form of the same
mechanism is the repo's `commutant-no-growth`: a genuine finite-dimensional
representation has `dim rho(Gamma)'=dim rho(t Gamma t^(-1))'`, so the
one-sided inclusion collapses.  `(D)` shows that the only normalized shadow
of that count is identically null.  The correct II_1 replacement is not a
density but the Pimsner--Popa index of Corollary 5 of the wall note, which is
not a normalized quantity at all.

Neither statement decides Connes embeddability.

## 2. Energy is free

Throughout, `Gamma<G`, `t Gamma t^(-1)<=Gamma`, and a *wall* in a finite
tracial `(M,tau)` for a homomorphism `pi:G->U(M)` is a unitary

```text
v in N=M intersect pi(Gamma)'   with   [v,pi(h)]!=1    (WE1)
```

for some `h=t^(-1) gamma t notin Gamma`, `gamma in Gamma`.  Its *energy* is

```text
e(v)=||v-pi(h) v pi(h)^*||_2.                          (WE2)
```

**Theorem 1.**  Let `(M,pi,v)` be a wall with `M` Connes embeddable.  For
`k>=1` put

```text
M_k=M^(tensorBar k),  pi_k=pi^(tensor k),  v_k=v^(tensor k). (WE3)
```

Then each `(M_k,pi_k,v_k)` is a wall in a Connes-embeddable algebra, `v_k` is
self-adjoint whenever `v` is, and

```text
sup_k e(v_k)^2>=2.                                     (WE4)
```

More precisely, with `c=tau(v^* pi(h) v pi(h)^*)`: if `|c|<1` then
`e(v_k)->sqrt2`, and if `|c|=1` then `e(v_k)^2>=3` for suitable `k`.

**Proof.**  Write `w=pi(h) v pi(h)^*`.  Since `v` commutes with every
`pi(gamma)`, `v_k` commutes with every `pi_k(gamma)=pi(gamma)^(tensor k)`, so
`v_k in M_k intersect pi_k(Gamma)'`.  Also
`pi_k(h) v_k pi_k(h)^*=w^(tensor k)`, so

```text
e(v_k)^2=2-2 Re tau(v^* w)^k=2-2 Re c^k.               (WE5)
```

Connes embeddability is preserved by finite tensor products: tensoring
microstates of the factors gives microstates of the product.

The element `v^*w` is a unitary in a tracial von Neumann algebra with
faithful trace, so `|c|<=1`, and `c=1` would force `v^*w=1`, i.e. `w=v`,
contradicting `(WE1)`.  If `|c|<1` then `c^k->0` and `(WE5)` gives
`e(v_k)->sqrt2`, and each `v_k` is still a wall because `w^(tensor k)!=v^(tensor k)`.
If `|c|=1` then `c=exp(i theta)` with `theta` not a multiple of `2 pi`;
the closure of `{c^k}` is either the full circle or the group of `m`-th roots
of unity with `m>=2`, and in both cases `inf_k Re c^k<=-1/2`, so
`e(v_k)^2>=3` for a suitable `k`.  End proof.

**Corollary 2.**  If a wall exists in any Connes-embeddable finite tracial
algebra, then there exists one satisfying the maximal-energy hypotheses
`(CHI8)` of `TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md`
and `(WFI4)` of `FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md`, up
to an arbitrarily small loss in the constant.  Consequently the flexible
Hilbert--Schmidt instability conclusions of those notes hold as soon as a
wall exists at all.

**Scope.**  Tensor amplification does **not** produce the *Clifford* wall of
Theorem 3 of the wall note.  There `v` and its conjugate must anticommute,
and `v_k w_k=(vw)^(tensor k)` while `w_k v_k=(wv)^(tensor k)`, so
anticommutation of the amplified pair requires `vw=zeta wv` with a scalar
`zeta` in the base model.  Anticommutation is a genuinely stronger demand
than energy; energy is not.

## 3. The commutant density is a character invariant

Let `Gamma` be a finitely generated infinite group with property `(T)` and
let `(mu_j)` be a Kazhdan sequence as constructed in Section 5 of
`TRUE_CLIFFORD_COMPRESSOR_SITE_GROWTH.md`: finitely supported probability
measures on `Gamma` with `||sigma(mu_j)-P_sigma||->0` uniformly over all
unitary representations `sigma`.

For a map `rho:Gamma->U(d)` (not assumed multiplicative) put

```text
D_j(rho)=sum_gamma mu_j(gamma) |tr_d(rho(gamma))|^2,   (WE6)
```

with `tr_d` the normalized trace.

**Proposition 3 (character formula for the commutant dimension).**  If
`rho` is a homomorphism, then

```text
lim_j D_j(rho)=dim_C(rho(Gamma)')/d^2.                 (WE7)
```

**Proof.**  Equip `M_d(C)` with the Hilbert--Schmidt inner product.  Then
`Ad rho` is a unitary representation of `Gamma` on this `d^2`-dimensional
space, and its fixed-point space is `rho(Gamma)'`.  Uniform convergence gives
`Ad rho(mu_j)->P` in norm, `P` the orthogonal projection onto
`rho(Gamma)'`, hence `Tr(Ad rho(mu_j))->Tr(P)=dim rho(Gamma)'`.  Finally
`Ad rho(gamma)` is `rho(gamma) tensor conj(rho(gamma))` under
`M_d=C^d tensor (C^d)^*`, so `Tr(Ad rho(gamma))=|Tr rho(gamma)|^2`.  Divide
by `d^2`.  End proof.

**Proposition 4 (exact conjugation invariance).**  Let `rho_n:G->U(d_n)` be
normalized-Hilbert--Schmidt asymptotic representations and `t in G`.  Then
for every fixed `j`

```text
|D_j(rho_n|_(t Gamma t^(-1)) o Ad t)-D_j(rho_n|_Gamma)|
 <= 2 max_(gamma in supp mu_j)
    ||rho_n(t gamma t^(-1))-rho_n(t)rho_n(gamma)rho_n(t)^*||_2 -> 0. (WE8)
```

Here the left density is the one attached to the compressed subgroup
`t Gamma t^(-1)` through the transported Kazhdan sequence
`(mu_j)^t(t gamma t^(-1))=mu_j(gamma)`.  That transport is legitimate, and
the transported sequence has the *same* constants: conjugation
`c_t:Gamma->t Gamma t^(-1)` is a group isomorphism, so for every unitary
representation `tau` of `t Gamma t^(-1)` the composite `tau o c_t` is a
unitary representation of `Gamma` with the same space of invariant vectors,
whence

```text
||tau((mu_j)^t)-P_tau||=||(tau o c_t)(mu_j)-P_(tau o c_t)||->0     (WE8a)
```

uniformly.  In particular `t Gamma t^(-1)` inherits the Kazhdan set `c_t(K)`
with the same constant `kappa`, so nothing in `(WE6)` is being compared
across different normalizations.

**Proof.**  `|tr(A)-tr(B)|<=||A-B||_2` by Cauchy--Schwarz, and
`| |a|^2-|b|^2 |<=2|a-b|` for `|a|,|b|<=1`.  The displayed defect tends to
zero because

```text
||rho(t gamma t^(-1))-rho(t)rho(gamma)rho(t)^*||_2
 =||rho(t gamma t^(-1))rho(t)-rho(t)rho(gamma)||_2
 <=||rho(t gamma t^(-1))rho(t)-rho(t gamma)||_2
  +||rho(t gamma)-rho(t)rho(gamma)||_2,
```

two multiplicative defects on a fixed finite window.  End proof.

**Proposition 5 (degeneracy).**  Suppose `tr(rho_n(g))->chi(g)` for every
`g in G`.  Then `lim_n D_j(rho_n|_Gamma)=sum_gamma mu_j(gamma)|chi(gamma)|^2`.
If moreover `chi(gamma)=0` for every `gamma!=1` — as for the canonical trace
of any crossed product `Cl(X) crossed_product G`, of `L(W)`, or of any
free-lamp model built on the regular character of `G` — then

```text
lim_j lim_n D_j(rho_n|_Gamma)=lim_j mu_j(1)=0.         (WE9)
```

**Proof.**  The first statement is immediate since `mu_j` is finitely
supported.  Under the second hypothesis the inner limit is `mu_j(1)`.  Apply
`||lambda(mu_j)-P_lambda||->0` in the regular representation of `Gamma`:
`Gamma` is infinite, so `P_lambda=0` and
`mu_j(1)=<lambda(mu_j)delta_1,delta_1> -> 0`.  End proof.

**Which limit is being computed.**  Proposition 4 fixes `j` and lets
`n->infinity`; Proposition 5 then lets `j->infinity`.  What is computed is
therefore the **iterated** limit `lim_j lim_n D_j(rho_n)`, and no uniformity
in `j` is claimed or used.  For the negative conclusion below that is
enough — an iterated limit of `0` already leaves the counting method with
nothing to compare — but anyone who later wants to *use* the density as an
invariant, rather than to bury it, will need a joint limit and will have to
supply the uniformity.

**Conclusion (D).**  Combining: the normalized commutant density of a
microstate model is determined by its character; it takes the same value on
`Gamma` and on any conjugate `t Gamma t^(-1)`, because a trace is
conjugation invariant; and in every model relevant to this program — those
whose character is supported at the identity — it is `0`.  The
conjugation-invariance half is unconditional; the vanishing half is not, and
depends on that hypothesis on the character.  The exact-representation identity
`dim rho(Gamma)'=dim rho(t Gamma t^(-1))'`, which is the entire content of
`commutant-no-growth` and the exact-representation shadow of the isotropy and
orbit counting in Kun--Thom Theorem 4.1, therefore degenerates in the tracial
ultraproduct to the identity `0=0`.

This is a strictly negative statement about a method, not evidence for
embeddability.  It says only that the load-bearing invariant of the
finite-dimensional and permutation obstructions has no informative normalized
version, so a tracial refutation of the wall must come from somewhere else —
in practice from flexible Hilbert--Schmidt stability, which restores an exact
representation and with it the exact dimension count.

The abstract form of this failure is already recorded as the established
claim `invariant-size-collapse`: a conjugation-invariant size that
distinguishes proper inclusions forces every compression to be an equality,
and the II_1 trace fails the second hypothesis.  What Propositions 3--5 add
is the identification of the *specific* candidate size in the tracial
setting, its closed form in terms of the character, and the fact that it is
not merely refinement-blind but identically zero for every model in this
program — so it cannot be repaired by sharpening the comparison, only
replaced by the index.

## 4. Relation to the index

Corollary 5 of `TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md` gives the correct
II_1 substitute for the dimension count: a wall forces
`lambda(t)=[Ad pi(t)(N):N]>1` and `[M:N]=infinity`.  The index is not a
normalized quantity and does not degenerate; `TRUE_CLIFFORD_COMPRESSOR_SITE_
GROWTH.md` computes it to be infinite at every strict positive compressor of
the monomial-cone pair.  Section 3 above explains why nothing weaker than the
index — in particular no normalized dimension density — can see the
compression at all.

## References

* `notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md`, Theorem 2, Corollaries 5
  and 8.
* `notes/TRUE_CLIFFORD_HYPERLINEARITY_FORCES_AMBIENT_HS_INSTABILITY.md`,
  `(CHI8)`.
* `notes/FALSE_RELATIVE_WALL_FORCES_FLEXIBLE_HS_INSTABILITY.md`,
  `(WFI2)`--`(WFI4)`.
* Kun--Thom, arXiv:2608.06222v1, Theorem 4.1 (statement verified from source;
  the proof there controls isotropy orders and orbit cardinalities in a
  permutation model).
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, for the
  representation-independent Kazhdan projection.
