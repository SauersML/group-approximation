# Finite-packet self-copy collapse

## Proof architecture, failed route, and repair

## Status

This note gives a paper-level closure of a **modified finite-memory self-copy route**.
It does not assert the previously falsified bare implication

> exact finite-dimensional self-copy sterility => MF sterility.

The calibration group

\[
\langle a,t,p\mid tat^{-1}=a^2,\ [p,a^2]=1\rangle
\]

shows that implication is false.  The added hypothesis here is a fixed finite
**noncommutative packet** normalized by the Kazhdan source.  That packet gives
an integer rank/multiplicity scale which cannot dissolve continuously.

The analytic input from Cairn is only the already proved theorem
`ScaledKazhdanTransport.scaled_transport_both`.

---

## Executive summary

The original finite-memory program starts from an exact finite-dimensional
fact: a finite-dimensional algebra cannot contain a proper conjugate copy of
itself with the same dimension.  In an ascending self-copy this forces every
honest finite-dimensional representation to forget certain parent-versus-child
commutators.  Cairn proves that statement in
`GroupApproximation/Criterion/FiniteDimensionalKill.lean`.

That exact result does **not** pass automatically to norm-matrix coronas.  The
calibration

\[
G=\langle a,t,p\mid tat^{-1}=a^2,\ [p,a^2]=1\rangle,
\qquad w=[p,a],
\]

is torsion-free, finitely presented, and operator-MF.  Its word `w` is
nontrivial and is killed by every honest finite-dimensional representation,
but survives in a norm-matrix corona.  The escape persists even when the
parent and child generated C-star algebras are literally equal at every matrix
stage.  Thus neither exact finite-dimensional sterility nor bare
Kadison--Kastler transport supplies the missing uniform coercivity.

The repair is to store memory in the integer multiplicity of a fixed finite
noncommutative packet.  For the arithmetic compressor

\[
P=\Gamma(3)\ltimes\mathbb Z^3,
\qquad \alpha(g,v)=(g,2v),
\]

the compressed subgroup has index eight.  On its eight cosets plus one new
point, take `K = S_9` and mark the star transposition.  A representation of
this fixed packet in a matrix corona can be exactified on a tail.  Packet
covariance can then be corrected exactly by finite averaging and polar
decomposition.  Every surviving marked displacement has an integer rank, and
for two distinct star transpositions every nonzero singular value of their
difference is `sqrt 3`.

That rank is used as the normalization weight in Cairn's already formalized
scaled Kazhdan transport theorem.  Property (T) and one-sided compression say
the marked displacement is negligible relative to its own rank; the fixed
spectral floor says it costs at least three times that rank.  Hence its rank is
zero.  The mechanism is

\[
\boxed{
\text{finite noncommutative packet exactification}
+\text{integer rank self-normalization}
+\text{scaled Kazhdan transport}.}
\]

The endpoint below remains a paper-level breakthrough candidate until the new
finite-packet chain is independently checked and translated into Lean.

---

## The exact finite-dimensional detector already in Cairn

Let `Gamma <= H` and let `t in H` satisfy

\[
t\Gamma t^{-1}\le\Gamma.
\]

For a genuine finite-dimensional representation `pi : H -> GL(V)`, put

\[
C=\pi(\Gamma)'.
\]

Conjugation by `pi(t)` maps the parent commutant injectively into the
compressed commutant.  In the one-sided situation the transported copy lies
inside the parent commutant.  Conjugation preserves dimension, so
finite-dimensional inclusion with equal dimension is equality.  Therefore,
if `p` commutes with the compressed child, then `pi(p)` commutes with the
whole parent, and

\[
\pi([p,q])=1\qquad(q\in\Gamma).
\]

The relevant declarations in `FiniteDimensionalKill.lean` are

* `repCommutant_eq_map_sandwich_of_compression`;
* `mem_repCommutant_of_commutes_compressed`;
* `map_commutator_eq_one_of_commutes_compressed`;
* `map_commutator_eq_one_of_commutes_compressed_units`.

The Cairn graph records the machine-checked general statement at
`compression-defect-dies-in-finite-dimensions`; this note does not duplicate
that theorem.

---

## The bare route is false

Consider

\[
G=\langle a,t,p\mid tat^{-1}=a^2,\ [p,a^2]=1\rangle,
\qquad w=[p,a].
\]

The exact detector applies to `Gamma=<a>` and its child `<a^2>`, so every
honest finite-dimensional representation kills `w`.  On the other hand,

\[
G\cong BS(1,2)*_{\langle a^2\rangle}\mathbb Z^2.
\]

The word `p a p^{-1} a^{-1}` is reduced in the amalgam normal form, hence
`w != 1`.  Both factors are torsion-free, and torsion-freeness of their amalgam
is the existing Cairn theorem
`amalgam-torsion-permanence-needs-no-cyclic-reduction`.  Both factors are also
amenable.  Shulman's theorem that full group C-star algebras of amalgamated
free products of amenable groups are MF therefore makes `C*(G)` MF.

Consequently

\[
\boxed{
\text{nontrivial and killed by every finite-dimensional representation}
\not\Rightarrow\text{MF-radical}.}
\]

This calibration is wired once in the Cairn graph as
`bare-self-copy-mf-calibration`; its literature input is isolated as
`amenable-amalgams-have-mf-full-cstar`.

### The explicit matrix escape

For `m >= 2`, let `zeta_m=exp(pi i/m)` and use the basis
`e_0,...,e_(2m-1)` of `C^(2m)`.  Define

\[
A_me_j=\zeta_m^j e_j,
\]

and let the permutation unitary `T_m` satisfy

\[
T_me_{2r}=e_r,
\qquad T_me_{2r+1}=e_{m+r}
\quad(0\le r<m).
\]

Put `B_m=T_m A_m T_m^*`, and let `P_m` swap the two `m`-point fibers:

\[
P_me_r=e_{m+r},
\qquad P_me_{m+r}=e_r.
\]

Direct evaluation gives

\[
\|B_m-A_m^2\|=2\sin\frac{\pi}{2m}\longrightarrow0,
\qquad [P_m,A_m^2]=1,
\]

and

\[
\|[P_m,B_m]-1\|=2\sin\frac{\pi}{2m}\longrightarrow0.
\]

But `zeta_m^m=-1`, so

\[
P_mA_mP_m^*=-A_m,
\qquad [P_m,A_m]=-1.
\]

Thus the defining relations hold in the norm corona while the marked
commutator stays maximally nontrivial.  This is a concrete corona witness; the
MF property of the whole group comes from the amenable-amalgam theorem above.

### Exact algebra equality still does not repair it

Both `A_m` and `B_m` are diagonal with simple spectrum consisting of all
`2m`-th roots of unity.  Therefore

\[
C^*(A_m)=C^*(B_m)=D_{2m}
\]

literally, while

\[
\operatorname{dist}(P_m,D_{2m})=1.
\]

Hence exact equality of the generated parent and child algebras does not turn
approximate commutation with a checked child generator into proximity to the
full child commutant.  The discarded self-copy strategy had conflated two
independent tasks:

1. transporting the child algebra to the parent; and
2. obtaining dimension-independent commutant coercivity from finitely checked
   commutators.

The second fails in the calibration even when the first has zero error.  The
open graph node `self-copy-kadison-kastler-checksum` now records only the
stronger direct coercivity statement that survives this counterexample.

---

## The repair: multiplicity memory

The fiber-swap model hides disagreement in a phase whose amplitude tends to
zero.  Once a representation of one fixed finite group is exact, the possible
irreducible blocks are fixed and finite.  A nonzero displacement cannot create
new sectors with arbitrarily small singular values; it can only change the
integer multiplicity of sectors on which the two packet elements disagree.

This changes the memory variable from a continuous error amplitude to

\[
0,1,2,3,\ldots.
\]

The remainder of the note proves that this integer rank is exactly the scale
which one-sided Kazhdan transport can consume.

---

## 1. Finite-packet collapse theorem

Let `W` be a countable group and `L <= W` a subgroup.  Let `s in W` satisfy

\[
sLs^{-1}\le L.
\]

Assume:

1. `L` is finitely generated and has property (T);
2. `K <= W` is a finite subgroup normalized by `L`;
3. `k in K` is fixed by the compressed subgroup:
   \[
   hkh^{-1}=k\qquad(h\in sLs^{-1}).
   \]

Then for every homomorphism

\[
\rho:W\longrightarrow U\!\left(\prod_nM_{d_n}(\mathbb C)/\bigoplus_nM_{d_n}(\mathbb C)\right)
\]

and every `g in L`,

\[
\rho(gkg^{-1})=\rho(k).
\]

Equivalently,

\[
\rho([g,k])=1.
\]

Thus every `[g,k]` lies in the operator-MF radical of `W`.

The point is that the `L`-orbit of `k` need **not commute**.  The finite packet
may be an arbitrary finite group.

---

## 2. Exactify the finite packet

Write

\[
\mathcal Q=\prod_nM_{d_n}(\mathbb C)/\bigoplus_nM_{d_n}(\mathbb C),
\qquad q:\prod_nM_{d_n}\to\mathcal Q.
\]

The restriction `rho|_K` extends to a unital star-homomorphism

\[
\Phi:C^*(K)\to\mathcal Q.
\]

Since `K` is finite, `C^*(K)` is finite-dimensional.  Finite-dimensional
C-star algebras are semiprojective.  Applying semiprojectivity to

\[
0\to\bigoplus_nM_{d_n}\to\prod_nM_{d_n}\to\mathcal Q\to0
\]

shows, after deleting finitely many coordinates, that there are exact unital
star-homomorphisms

\[
\Phi_n:C^*(K)\to M_{d_n}
\]

whose sequence lifts `Phi`.

Put

\[
V_n(x)=\Phi_n(x),\qquad x\in K.
\]

Then at every retained coordinate

\[
V_n(xy)=V_n(x)V_n(y),\qquad V_n(x)^*=V_n(x^{-1}).
\]

So the packet is no longer approximate at all.

### Elementary alternative

One does not need the full machinery of semiprojectivity here.  Choose lifts
of the finitely many matrix units in the decomposition

\[
C^*(K)\cong\bigoplus_{j=1}^r M_{m_j}(\mathbb C).
\]

Their matrix-unit defects converge to zero in operator norm.  Spectral
rounding of the diagonal projections followed by polar correction of the
partial isometries produces exact matrix units at every sufficiently late
coordinate.  Because only finitely many relations are present, the
correction converges to zero.  This gives the same `Phi_n`.

---

## 3. Exactify covariance by a near-identity unitary

Let `a in L`.  Choose a unitary lift `U_{a,n}` of `rho(a)`.  Since `L`
normalizes `K`, conjugation by `a` induces an automorphism

\[
\beta_a:K\to K.
\]

At coordinate `n` consider the two exact representations of the finite group
`K`

\[
\phi_{a,n}(x)=U_{a,n}V_n(x)U_{a,n}^*,
\qquad
\psi_{a,n}(x)=V_n(\beta_a(x)).
\]

They have the same image in the corona, so, because `K` is finite,

\[
\epsilon_{a,n}:=
\max_{x\in K}\|\phi_{a,n}(x)-\psi_{a,n}(x)\|\longrightarrow0.
\]

There is an explicit exact intertwiner.  Define

\[
T_{a,n}=\frac1{|K|}\sum_{x\in K}
\psi_{a,n}(x)\phi_{a,n}(x)^*.
\]

Haar invariance of the finite sum gives

\[
T_{a,n}\phi_{a,n}(x)=\psi_{a,n}(x)T_{a,n}\qquad(x\in K).
\]

Also

\[
\|T_{a,n}-1\|\le\epsilon_{a,n}.
\]

For late `n`, `epsilon_{a,n}<1`, hence `T_{a,n}` is invertible.  Let

\[
z_{a,n}=T_{a,n}(T_{a,n}^*T_{a,n})^{-1/2}.
\]

Because `T_{a,n}^*T_{a,n}` commutes with `phi_{a,n}(K)`, the polar unitary
still intertwines:

\[
z_{a,n}\phi_{a,n}(x)z_{a,n}^*=\psi_{a,n}(x).
\]

Moreover

\[
\|z_{a,n}-1\|
\le \frac{2\epsilon_{a,n}}{1-\epsilon_{a,n}}
\longrightarrow0.
\]

Set

\[
\widehat U_{a,n}=z_{a,n}U_{a,n}.
\]

Then

\[
\widehat U_{a,n}V_n(x)\widehat U_{a,n}^*=V_n(\beta_a(x))
\tag{3.1}
\]

**exactly**, while

\[
\|\widehat U_{a,n}-U_{a,n}\|\to0.
\tag{3.2}
\]

This is the key finite-memory correction: covariance on the entire packet is
made exact with no dimension-dependent constant.

---

## 4. The integer self-normalizing scale

Choose the assumed finite symmetric generating set `S` of `L`.

For `lambda in L` write

\[
k_\lambda=\lambda k\lambda^{-1}\in K,
\qquad
b_n(\lambda)=V_n(k_\lambda)-V_n(k).
\]

For `a in S` put

\[
r_{a,n}=\operatorname{rank} b_n(a),
\qquad
w_n=\sum_{a\in S}r_{a,n}.
\tag{4.1}
\]

Assume for contradiction that `rho(k)` is not fixed by `L`.  Then it is not
fixed by some `a_0 in S`.  The sequence `b_n(a_0)` is therefore not
operator-norm-null.  Since every `b_n(a)` comes from a representation of the
**fixed finite group** `K`, there is a constant

\[
\eta>0
\tag{4.2}
\]

depending only on `(K,k,S)` such that every nonzero singular value of every
`b_n(a)` is at least `eta`.

Indeed decompose `C^*(K)` into its finitely many irreducible matrix blocks and
take the minimum positive singular value of

\[
\pi(k_a)-\pi(k)
\]

over the finitely many pairs `(a,pi)` for which this matrix is nonzero.

After passing to an increasing subsequence we may therefore suppose

\[
w_n\ge1\qquad\text{for all }n.
\tag{4.3}
\]

The unnormalized Hilbert--Schmidt mass of the generator displacement has a
uniform lower anchor:

\[
\sum_{a\in S}\|b_n(a)\|_2^2
\ge \eta^2 w_n.
\tag{4.4}
\]

There is also the trivial upper estimate

\[
\|b_n(a)\|_2^2\le4r_{a,n}\le4w_n.
\tag{4.5}
\]

Thus `w_n` is exactly the missing self-normalizing scale: it is an integer,
it is positive whenever the mark survives, and the marked energy is bounded
below by a fixed positive multiple of it.

---

## 5. Rank word bound without commutativity

Equation (3.1) gives, for a generator `a in S`,

\[
\begin{aligned}
b_n(a\lambda)
 &=V_n(k_{a\lambda})-V_n(k)\\
 &=\widehat U_{a,n}
     (V_n(k_\lambda)-V_n(k))
   \widehat U_{a,n}^*
   +b_n(a).
\end{aligned}
\tag{5.1}
\]

Rank is invariant under unitary conjugation and subadditive, so

\[
\operatorname{rank}b_n(a\lambda)
\le \operatorname{rank}b_n(\lambda)+r_{a,n}.
\tag{5.2}
\]

Induction on word length gives, for every fixed `lambda`,

\[
\operatorname{rank}b_n(\lambda)
\le |\lambda|_S w_n.
\tag{5.3}
\]

Since `b_n(lambda)` is a difference of unitaries,

\[
\|b_n(\lambda)\|\le2,
\]

and hence

\[
\|b_n(\lambda)\|_2^2
\le4|\lambda|_S w_n.
\tag{5.4}
\]

No pairwise commutativity of the packet was used.

---

## 6. Weighted Hilbert ultraproduct and the displacement cocycle

Give `M_{d_n}(C)` the real Hilbert norm

\[
\|X\|_{(n)}=w_n^{-1/2}\|X\|_2.
\]

Take a nonprincipal ultrafilter and form the Hilbert ultraproduct `H_omega`.
The chosen lifts `U_{g,n}` of the corona representation define an orthogonal
representation

\[
\Sigma:W\to O(H_\omega),
\qquad
\Sigma(g)[X_n]=[U_{g,n}X_nU_{g,n}^*].
\tag{6.1}
\]

This is a genuine representation because the lift is multiplicative in
operator norm modulo `c_0`: for a scaled-mass-bounded vector,

\[
\|\operatorname{Ad}U_{gh,n}X_n-
  \operatorname{Ad}(U_{g,n}U_{h,n})X_n\|_{(n)}
\le2\|U_{gh,n}-U_{g,n}U_{h,n}\|\,\|X_n\|_{(n)}
\to0.
\]

By (5.4), for every fixed `lambda` the sequence `b_n(lambda)` has bounded
scaled Hilbert norm.  Define

\[
b(\lambda)=[b_n(\lambda)]\in H_\omega.
\]

Equation (5.1) and (3.2) imply

\[
b(a\lambda)=\Sigma(a)b(\lambda)+b(a)
\qquad(a\in S),
\]

because replacing `widehat U_{a,n}` by `U_{a,n}` changes the scaled Hilbert
norm by at most

\[
2\|z_{a,n}-1\|\,\|b_n(\lambda)\|_{(n)}\to0.
\]

Since `S` generates `L`, `b|_L` is a genuine 1-cocycle for `Sigma|_L`.

The anchor (4.4) gives

\[
\sum_{a\in S}\|b(a)\|^2\ge\eta^2,
\tag{6.2}
\]

so the cocycle is nonzero.

---

## 7. Property (T) produces a primitive

By the Delorme--Guichardet fixed-point theorem (formalized in Cairn as
`Kazhdan.Delorme.exists_fixed_point_of_hasKazhdanPropertyT`), property (T) of
`L` gives `xi in H_omega` such that

\[
b(\lambda)=\xi-\Sigma(\lambda)\xi
\qquad(\lambda\in L).
\tag{7.1}
\]

Let

\[
H=sLs^{-1}.
\]

By hypothesis, `hkh^{-1}=k` for every `h in H`; therefore

\[
b(h)=0\qquad(h\in H).
\]

Equation (7.1) shows that `xi` is `H`-fixed.

Put

\[
\zeta=\Sigma(s)^{-1}\xi.
\]

For `lambda in L`,

\[
\Sigma(\lambda)\zeta
=\Sigma(s)^{-1}\Sigma(s\lambda s^{-1})\xi
=\zeta,
\]

because `s lambda s^{-1} in H`.  Hence `zeta` is `L`-fixed.

So far this is ordinary property-(T) Hilbert-space geometry.  The one-sided
nature of the compressor appears in the next step.

---

## 8. Use Cairn's scaled Kazhdan transport

Choose a matrix representative `Z_n` of `zeta` in the weighted Hilbert
ultraproduct.  It has bounded `w_n`-scaled Frobenius mass.

`L`-invariance of `zeta` says that for each fixed `lambda in L`,

\[
\frac{\|Z_n-U_{\lambda,n}Z_nU_{\lambda,n}^*\|_2^2}{w_n}
\longrightarrow_\omega0.
\tag{8.1}
\]

Because `L` is countable, choose an increasing subsequence lying in the
ultrafilter on which (8.1) holds **cofinally for every fixed lambda**, while
preserving the mass bound and (6.2).  On that subsequence `Z_n` is precisely
an `IsScaledAsymptoticCommutant` at weight `w_n` in the sense of
`ScaledKazhdanTransport.lean`.

Apply

`ScaledKazhdanTransport.scaled_transport_both`

to the compression core with root `c=1`.  Its forward half gives

\[
U_{s,n}Z_nU_{s,n}^*
\]

as another `w_n`-scaled asymptotic commutant of the **whole** `L`.

But this transported sequence represents

\[
\Sigma(s)\zeta=\xi.
\]

Thus `xi` is `L`-fixed at the scaled coordinate level.  Combining this with
(7.1) yields

\[
\frac{\|b_n(a)\|_2^2}{w_n}\to0
\qquad(a\in S).
\]

Summing over the finite set `S` gives

\[
\frac{\sum_{a\in S}\|b_n(a)\|_2^2}{w_n}\to0,
\]

contradicting the uniform lower bound (4.4).

Therefore the assumption that `rho(k)` is moved by `L` was false.  Hence

\[
\rho(gkg^{-1})=\rho(k)\qquad(g\in L).
\]

This proves the finite-packet collapse theorem.

---

# 9. A concrete arithmetic carrier

The theorem above can be fed by Cairn's already formalized affine compressor.
Use the certified dilation-by-2 instance

\[
P=\Gamma(3)\ltimes\mathbb Z^3,
\qquad
\alpha(g,v)=(g,2v).
\]

Cairn proves:

* `P` is countable, finitely presented, torsion-free and Kazhdan;
* `alpha` is injective and proper;
* `H=alpha(P)` has index `8` in `P`;
* there is an explicit `p_0 notin H`.

Let

\[
E=\langle P,t\mid tpt^{-1}=\alpha(p)\ (p\in P)\rangle.
\]

Then

\[
tPt^{-1}=H\le P.
\]

Let

\[
X=P/H,
\qquad |X|=8,
\]

and adjoin a new point `star`.  Put

\[
F=\operatorname{Sym}(X\sqcup\{\star\})\cong S_9.
\]

`P` acts on `X` by left translation and fixes `star`; hence it acts by
automorphisms on `F`.  Form

\[
A=F\rtimes P.
\]

Let

\[
k=(H\ \star)\in F
\]

be the star transposition at the base coset.  Every `h in H` fixes `H in X`,
so

\[
hkh^{-1}=k.
\tag{9.1}
\]

On the other hand `p_0H != H`, so

\[
p_0kp_0^{-1}=(p_0H\ \star)\ne(H\ \star)=k.
\tag{9.2}
\]

Finally amalgamate the packet host with the ascending HNN extension along the
common copy of `P`:

\[
W=A *_P E.
\tag{9.3}
\]

Both factor embeddings into an amalgamated free product are injective.
Therefore (9.2) remains true in `W`, and

\[
w=[p_0,k]\ne1.
\tag{9.4}
\]

Inside `W`, the finite subgroup `F` is normalized by `P`, while (9.1) says
the compressed subgroup `tPt^{-1}=H` fixes `k`.  The finite-packet collapse
theorem therefore gives, for every norm-matrix-corona representation `rho`,

\[
\rho(w)=1.
\tag{9.5}
\]

Since `w != 1`, `W` cannot embed faithfully in a norm matrix corona:

\[
\boxed{W\text{ is not operator-MF}.}
\]

---


## 9.5. The concrete packet has an explicit spectral floor

For the arithmetic carrier the abstract constant `eta` can be made explicit.
If `xH != H`, the two packet elements

\[
k=(H\ \star),\qquad k_x=(xH\ \star)
\]

are distinct transpositions sharing the point `star`, so `k_x k` is a
3-cycle.  In any unitary representation `pi` of `S_9`,

\[
\pi(k_x)-\pi(k)=\pi(k_x)\bigl(1-\pi(k_xk)\bigr).
\]

The spectrum of a 3-cycle is contained in `{1, omega, omega^2}`, hence every
nonzero singular value of `1-pi(k_xk)` is exactly

\[
|1-\omega|=\sqrt 3.
\]

Thus in the concrete carrier one may take

\[
\boxed{\eta=\sqrt3}.
\]

This removes any hidden compactness dependence from the marked packet: the
rank weight is anchored by an explicit dimension-independent constant.

## 10. Finite presentation

The construction is finitely presented.

* `P` is finitely presented in Cairn.
* The ascending HNN extension `E` is finitely presented: choose a finite
  presentation `<S|R>` for `P`; add `t` and the finitely many relations
  `t s t^{-1}=alpha(s)` for `s in S`.
* `A=F semidirect P` is finitely presented because `F` is finite and `P` is
  finitely presented; one may write a finite multiplication table for `F`
  and finitely many action relations for generators of `P`.
* An amalgam of two finitely presented groups over a finitely generated
  subgroup is finitely presented: take the two finite presentations and add
  one identification relation for each generator of the amalgamated subgroup.

Hence

\[
\boxed{W\text{ is finitely presented and non-MF}.}
\]

The carrier is not torsion-free because it deliberately uses the finite packet
`F=S_9`.

---

## 11. Why this is not one of Cairn's three previous detectors

### Not the central-sign / Clifford detector

`F=S_9` has trivial center.  The marked element `k` is not central and no
central `-1` phase is used.

### Not the commuting finite-torsion detector

The `P`-orbit of `k` consists of star transpositions.  Distinct star
transpositions do **not** commute:

\[
(H\ \star)(x\ \star)\ne(x\ \star)(H\ \star).
\]

Therefore `TorsionSpectralCollapse.actualCoronaMFInvisible_of_torsionWitness`
does not apply: its pairwise-commuting-orbit hypothesis fails on purpose.

### Not the normal-Kazhdan-defect detector

The proof does not place a normal Kazhdan subgroup inside the compression
defect.  It kills the single commutator by a finite-packet multiplicity/rank
cocycle.

Thus the analytic mechanism is genuinely different:

\[
\boxed{
\text{finite noncommutative packet exactification}
+\text{integer rank self-normalization}
+\text{scaled Kazhdan transport}.
}
\]

It is best regarded as the successful **finite-memory** replacement for the
failed bare commutant/Kadison--Kastler route.

---

## 12. Why the previous counterexample does not apply

In the calibration group

\[
\langle a,t,p\mid tat^{-1}=a^2,[p,a^2]=1\rangle,
\]

the sibling unitary can hide in a continuously varying phase/fiber swap.
There is no fixed finite packet whose nonzero displacement has an integer rank
scale with a uniform spectral floor.

Here, after exactifying `F`, every generator displacement

\[
V_n(k_a)-V_n(k)
\]

belongs to the finite representation theory of one fixed finite group.
Nonzero singular values therefore have the fixed lower bound `eta`; the defect
cannot fade by shrinking its amplitude.  Its only escape is to shrink its
**multiplicity**, and that integer multiplicity is exactly the weight `w_n`
transported by Cairn's arbitrary-weight theorem.

That is the missing rigidity.

---

## 13. A useful negative control: property (T) is essential here

Replace `P` by `Z`, `alpha(n)=2n`, and take the analogous finite coset packet.
Then the HNN factor is `BS(1,2)` and the packet semidirect factor is amenable.
The resulting amalgam is an amalgamated free product of amenable groups, a
class known to be MF.  Thus finite packet discreteness by itself is not the
obstruction.

The rigidity step is precisely the Kazhdan/scaled-transport step in Section 8.

---

## 14. Formalization boundary

The following pieces already exist in Cairn/Lean:

* the affine Kazhdan compressor (`affine-congruence-source-is-kazhdan`);
* the standard cofinite norm-matrix-corona MF definition;
* Delorme fixed points for property (T);
* arbitrary-weight transport
  `ScaledKazhdanTransport.scaled_transport_both`.

The new Lean work required for a kernel-checked endpoint is finite and local:

1. exact lifting of a representation of a fixed finite group from the matrix
   corona to coordinate representations (or a finite-dimensional C-star
   exactification wrapper);
2. the averaging/polar covariance-correction lemma of Section 3;
3. rank word bounds for a noncommuting exact finite packet;
4. the weighted diagonal/ultraproduct assembly, parallel to the existing
   involution-collapse files;
5. the finite packet/amalgam carrier.

No Kadison--Kastler estimate, moving-address checksum, high-chromatic challenge,
or dimension-dependent commutant coercivity theorem remains.

---


## 15. Verification status and external sanity check

The dependency graph wires the general analytic theorem through
`finite-group-corona-tail-exactification`,
`finite-packet-covariance-polar-correction`, and
`scaled-kazhdan-transport`.  The arithmetic endpoint
`arithmetic-star-packet-non-mf` then consumes the affine Kazhdan source and the
general packet theorem.  The separate calibration route consumes the existing
exact finite-dimensional detector, torsion permanence, and Shulman's
amenable-amalgam theorem.  Repository validation should require all three
endpoints to resolve and `cairn check --changed` to add no graph error.

This is nevertheless **not yet a Lean-kernel-checked new endpoint**.  The new
finite-group tail-exactification, covariance correction, weighted cocycle
assembly, and concrete packet carrier are proved here at paper level and still
need translation into Lean.  The load-bearing transport theorem they consume,
`ScaledKazhdanTransport.scaled_transport_both`, is already present in Lean.

That distinction matters because public literature available in August 2026
still describes existence of a non-MF group (for the standard pointwise
operator-norm definition) as open.  Consequently this note should be treated
as a **breakthrough candidate requiring independent verification and Lean
formalization**, not as an externally established theorem merely because the
Cairn research graph closes.

## References for the standard finite-dimensional perturbation input

* B. Blackadar, *The homotopy lifting theorem for semiprojective C*-algebras*,
  Math. Scand. 118 (2016), arXiv:1207.1909.
* P. McKenney and A. Vignati, *Ulam stability for some classes of C*-algebras*,
  Proc. Roy. Soc. Edinburgh A 149 (2019), 45--59,
  DOI 10.1017/S0308210517000397.
* T. Shulman, *The MF property for amalgamated free products*,
  arXiv:2603.13564 (2026), Theorem 19.
* F. Fournier-Facio and B. Rangarajan, *Ulam stability of lamplighters and
  Thompson groups*, Math. Ann. 389 (2024), 2487--2531, Example 7.3.

The covariance correction in Section 3 is proved directly above by finite
averaging and polar decomposition, so only the finite-dimensional tail lift is
being imported from standard C-star perturbation theory.

---

## Breakthrough chronology

1. Cairn formalized exact finite-dimensional self-copy sterility.
2. The group `bare-self-copy-mf-calibration` falsified the passage from that
   exact theorem to MF-radical membership.
3. Its fiber-swap matrices showed that even literal equality of parent and
   child generated algebras does not give dimension-free commutant coercivity.
4. The Thompson lamp analysis separately exposed moving-address covariance as
   a quantifier leak for infinite packets.
5. A fixed finite noncommutative packet removes both leaks: all packet
   relations can be exactified at once, and nonzero displacement is measured
   by integer multiplicity with a fixed spectral floor.

The conceptual slogan is:

> Self-compression can make a continuously small error disappear, but it
> cannot make a positive integer number of rigid packet sectors disappear
> continuously.

## Repository anchors

The exact detector is in
`GroupApproximation/Criterion/FiniteDimensionalKill.lean`; the load-bearing
transport theorem is in
`GroupApproximation/Sofic/ScaledKazhdanTransport.lean`.  The graph nodes
`bare-self-copy-mf-calibration`,
`finite-noncommutative-packet-compression-collapse`, and
`arithmetic-star-packet-non-mf` are the canonical entry points for the failed
route, repaired analytic theorem, and concrete carrier respectively.
