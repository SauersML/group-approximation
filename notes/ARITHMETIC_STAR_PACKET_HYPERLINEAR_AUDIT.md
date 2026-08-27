# Arithmetic star packet: normalized-HS route audit

## Status

This route is now closed in the negative.  The arithmetic `S_9` packet carrier
embeds in a sofic graph-wreath product, hence is itself sofic and hyperlinear.
The former wall-placement target is therefore false for this carrier.

The operator-norm theorem `ScaledKazhdanTransport.scaled_transport_both`
cannot be applied to a hyperlinear microstate sequence: its ambient object is
`OpAlmostRepresentation`, whose multiplication defects vanish in operator
norm, whereas hyperlinearity supplies only normalized Hilbert--Schmidt
defect.  At dimension weight this theorem transports normalized-HS
commutants only for that narrower operator-norm input class.

Cairn already has the correct normalized-HS replacement at positive adjoint
density:

`property-t-hs-positive-density-commutant-no-growth`.

The audit below retains the normalized-HS anchor and multiplicity-gauge
calculation because they explain exactly how the sofic escape works.  The
internal packet gap cannot be placed in the compressed-versus-parent wall.

---

## 1. The finite action quotient

Let

\[
P=\Gamma(3)\ltimes\mathbb Z^3,
\qquad H=\alpha(P)=\Gamma(3)\ltimes2\mathbb Z^3.
\]

The action of `P` on `P/H` is the affine action on `F_2^3`.  Indeed, the
translation subgroup reduces onto `F_2^3`, while the elementary matrices
`e_ij(3)` lie in `Gamma(3)` and reduce modulo two to `e_ij(1)`.  These
generate `SL_3(F_2)=GL_3(F_2)`.  Hence the images of `P` and `H` in the
permutation group of the eight cosets are

\[
Q=AGL(3,2),\qquad Q_0=GL(3,2),
\]

where `Q_0` is the stabilizer of the base coset.  Their orders are

\[
|Q|=8\cdot168=1344,
\qquad |Q_0|=168.
\]

Both embed in `K=S_9` by fixing the extra point `star`.  The marked
transposition `k=(0 star)` is fixed by `Q_0` and moved by every affine
translation taking `0` to a nonzero point.

---

## 2. Canonical microstates force the regular packet type

Suppose a normalized-HS microstate sequence for the final group converges to
the canonical group trace.  Its restriction to the fixed finite subgroup
`K` has character converging to the regular character:

\[
\operatorname{tr}(U_x)\longrightarrow 1_{x=1}
\qquad(x\in K).
\]

Apply finite-group normalized-HS stability to exactify this fixed packet,
allowing a dimension change `d_n <= m_n=(1+o(1))d_n`.  Fixed character
polynomials show that the exact representation `V_n` has asymptotically the
regular Plancherel multiplicity vector.  Equivalently, up to `o(m_n)`
dimensions it is a multiple of the regular representation of `K`.

For two distinct star transpositions, their quotient is a three-cycle.  In
the regular representation, `1-g` for an order-three element has rank
`2|K|/3`, and all of its nonzero singular values are `sqrt 3`.  Therefore

\[
\frac{\operatorname{rank}(V_n(p_0kp_0^{-1})-V_n(k))}{m_n}
\longrightarrow\frac23,
\]

and

\[
\|V_n(p_0kp_0^{-1})-V_n(k)\|_{2,m_n}^2\longrightarrow2.
\]

This is the normalized-HS marked anchor.  Unlike the norm-corona proof, no
self-generated rank weight is needed: canonical trace already forces the
packet discrepancy onto positive ambient density.

---

## 3. The packet supplies an explicit adjoint-density gap

For a finite subgroup `G<=K`, let

\[
R_G(X)=\frac1{|G|}\sum_{g\in G}V_n(g)XV_n(g)^*
\]

be the Reynolds projection on the `m_n^2`-dimensional adjoint Hilbert space.
If `V_n` is `r` copies of the regular representation of `K`, then its
restriction to `G` is `r[K:G]` copies of the regular representation of `G`.
Consequently

\[
\frac{\operatorname{rank}R_G}{m_n^2}=\frac1{|G|}.
\]

The `o(m_n)` nonregular remainder changes normalized adjoint rank by `o(1)`.
Since `Q_0<=Q`, one has `R_Q<=R_{Q_0}` and hence

\[
\frac{\operatorname{rank}(R_{Q_0}-R_Q)}{m_n^2}
\longrightarrow
\frac1{168}-\frac1{1344}
=\boxed{\frac1{192}}.
\]

Thus the `S_9` packet really does manufacture the `Omega(d_n^2)` family of
adjoint directions which a normalized-HS argument needs.  This avoids the
`macroscopic-projection-is-one-adjoint-direction` dilution: the witness is a
whole commutant-difference space, not the span of one full-rank matrix.

---

## 4. The multiplicity gauge

The action of `P` on `K=S_9` is inner.  Write

\[
\theta:P\longrightarrow Q\le K
\]

for the affine permutation action.  Then

\[
A=K\rtimes_{\operatorname{Ad}\theta}P
\]

is abstractly a direct product.  The map

\[
\Phi:A\longrightarrow K\times P,
\qquad \Phi(x,p)=(x\theta(p),p)
\]

is an isomorphism.  Under it, the originally embedded source element is

\[
p\longmapsto(\theta(p),p).
\]

Equivalently, inside `A` the elements

\[
c_p=\theta(p)^{-1}p
\]

form a copy of `P` centralizing the entire packet.  In a matrix model,
`U_p` therefore factors, after packet exactification, into the internal
finite permutation `V(\theta(p))` and an essentially arbitrary unitary from
the packet multiplicity commutant.

This is the exact residual gauge.  The internal Reynolds gap
`R_(Q_0)-R_Q` need not automatically be a gap between the low-energy spaces
of the **external** `H` and `P` actions, because the commuting factors
representing `c_p` act on the multiplicity coordinates.  Local packet
exactification cannot remove them.

---

## 5. Why the placement theorem is false

Let `P_n` and `Q_n` be the parent and compressed low-spectrum projections in
`property-t-hs-positive-density-commutant-no-growth`, formed from the
external source matrices and the fixed words for `alpha(S)`.

The proposed theorem asked packet covariance and the HNN relations

\[
tpt^{-1}=\alpha(p)
\]

force a subspace `W_n` with

\[
W_n\le Q_n,
\qquad W_n\perp P_n,
\qquad
\operatorname{tr}_{ad}(W_n)\ge\frac1{192}-o(1).
\]

Together with Cairn's positive-density no-growth theorem this would give

\[
\frac1{192}-o(1)\le C\delta_n,
\]

contradicting a hyperlinear microstate sequence with `delta_n->0`.

But such microstates exist: the full carrier is sofic.  Let
`L=ker(theta)` and make every finite fiber of `E/L -> E/P` a clique.  The
amalgam kernel is the twisted free product `*_(E/P) K`; the map

\[
k\longmapsto (q^{-1}kq)_{q\in P/L}\in K^{P/L}
\]

embeds each twisted packet copy into its clique fiber and converts the inner
`P`-action into coordinate permutation.  This embeds the carrier into the
corresponding graph wreath product.  Cairn's exact finite telescope-orbit
models, followed by its cyclic-stack construction, prove the actor's action
on this fiber-clique graph sofic.  Graph-wreath permanence makes the envelope
sofic.

The point of the formulation is that the missing theorem cannot be replaced
by either of the following already-insufficient statements:

1. the marked matrix has rank `2d_n/3` -- one matrix is still one adjoint
   direction;
2. the internal packet Reynolds gap has density `1/192` -- the multiplicity
   gauge can rotate that gap away from the external Kazhdan low spaces.

The HNN relation therefore does not pay the gauge.  The gauge is precisely the
coordinate freedom used by the graph-wreath embedding.  The arithmetic
star-packet route is not a live route to non-hyperlinearity.

---

## 6. Surviving positive-density power-return route

The Culf--Mastel lane attacks the same normalized-HS visibility problem with
a stronger semantic payload.  Its finite packet authenticates a projection
`q` with canonical trace `alpha>0`; a finite-game gap forces an acceptance
compression to have matrix norm at most `rho<1`; and a group-word return is
asked to expose only the scalar overlaps

\[
\|q u^{kL}q\|_2^2
\le (\alpha+o(1))\rho^{2kL}+o(1),
\qquad 1\le k\le N.
\]

Cairn's established theorem
`positive-density-hs-power-overlaps-force-finite-depth` then gives

\[
(N+1)\alpha
\le1+\frac{2\rho^{2L}}{1-\rho^{2L}},
\]

which is contradicted by first fixing large `L` and then fixed
`N>1/alpha`.  Scalar overlap norms are insensitive to a common multiplicity
gauge, so this route avoids the precise placement problem left by the bare
`S_9` Reynolds gap.

The remaining compiler is recorded at
`canonical-positive-density-hs-power-overlap-return`.  It is strictly weaker
than the older no-return tail: it asks for finitely many scalar overlap
bounds on one positive-density head, not identities `q u^n q=T^n`.

There is an even weaker static sibling.  Replace the powers of one word by
finitely many unrelated words `v_i`.  For

\[
Q_i=v_iqv_i^*,
\qquad
\tau(Q_iQ_j)=\|qv_i^*v_jq\|_2^2,
\]

Cairn's existing `marked-copy-collision-forces-overlap-mass` theorem gives

\[
\sum_{i<j}\tau(Q_iQ_j)
\ge \frac{(M\alpha)^2-M\alpha}{2}.
\]

Thus pairwise bounds

\[
\|qv_i^*v_jq\|_2^2
\le(\alpha+o(1))\rho^{2L}+o(1)
\]

contradict capacity as soon as
`M alpha>1+(M-1)rho^(2L)`.  This route is recorded at
`canonical-positive-density-pairwise-game-overlap-packing`.  It removes the
single-word power orbit completely.  Cairn further reduces it through
`pairwise-game-packing-from-corner-actuator`: attach the same selected-corner
actuator directly to each actual ratio `v_i^*v_j`, so all cycle identities
hold automatically.  The remaining theorem is
`canonical-positive-density-amplified-acceptance-corner-actuator`: amplify
one game return on a fixed-density corner without using fresh-control trace
dilution or a global block-encoder equality.  No new matrix inequality is
needed.
