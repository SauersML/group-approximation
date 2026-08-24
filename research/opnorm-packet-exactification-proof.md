---
rg: 2
id: opnorm-packet-exactification-proof
kind: route
title: Round the corner projection, polar-correct the columns, orthogonalize, and rotate carriers together
target: opnorm-packet-exactification-is-dimension-free
requires: []
---

All constants below are absolute multiples of `r` (resp. `r+s`) times
`delta`; none depends on `d`.  Write `~` for equality up to such a quantity.

**1. Symmetrize.**  Replace `E_ij` by `(E_ij+E_ji^*)/2`.  By the first line
of `(EXA1)` this moves each entry by at most `delta/2` and makes
`E_ij^*=E_ji` exact.  The second line of `(EXA1)` survives with `2delta`.

**2. Round the corner.**  `E_11` is now self-adjoint with
`||E_11^2-E_11||<=2delta`, so its spectrum lies within `O(delta)` of
`{0,1}`.  Let `p=chi_([1/2,infinity))(E_11)`, a projection with
`||p-E_11||=O(delta)`.  If `||E_11||>1/2` then `p!=0`.

**3. Polar-correct the first column.**  Put `v_i=E_i1 p`.  Then

```text
v_i^*v_i = p E_1i E_i1 p ~ p E_11 p ~ p,
```

so `v_i^*v_i` is invertible in `pM_d(C)p` with inverse of norm `1+O(delta)`.
Set `w_i=v_i (v_i^*v_i)^(-1/2)`, computed in `pM_d(C)p`.  Each `w_i` is a
partial isometry with `w_i^*w_i=p` exactly, and `||w_i-E_i1||=O(delta)` --
using `||E_i1-E_i1p||<=||E_i1(E_11-p)||+||E_i1-E_i1E_11||=O(delta)`.  Take
`w_1=p`.

**4. Orthogonalize the ranges.**  For `i!=j`,
`w_i^*w_j ~ E_1i E_j1 ~ 0`, so the projections `q_i=w_iw_i^*` satisfy
`||q_iq_j||=O(delta)`.  A family of `r` projections that is pairwise
`O(delta)`-almost orthogonal is `O(r delta)`-close to a pairwise orthogonal
family: process `i=2,...,r` in order, replacing `q_i` by the projection onto
`(1-q_1-...-q_(i-1))q_i H`, which is well defined and `O(r delta)`-close to
`q_i` because the accumulated sum has norm `1+O(r delta)`.  Transport `w_i`
along the corresponding `O(r delta)`-small unitary to get `w~_i` with
`w~_i^*w~_i=p` and mutually orthogonal ranges.

**5. Assemble.**  Put `e_ij=w~_i w~_j^*`.  Then

```text
e_ij e_kl = w~_i (w~_j^* w~_k) w~_l^* = [j=k] e_il,
e_ij^*=e_ji,
```

exactly, so `(e_ij)` is an exact system of matrix units, and
`||e_ij-E_ij||<=||e_ij-E_i1E_1j||+||E_i1E_1j-E_ij||=O(r delta)` by steps 3-4
and `(EXA1)`.  Its identity is `P=sum_i e_ii=sum_i w~_iw~_i^*`, a sum of `r`
mutually orthogonal projections each equivalent to `p`, so `rank(P)=r rank(p)`
and `P!=0` exactly when `p!=0`.  Set `eps_r(delta)=O(r delta)`.

**6. Common carrier.**  Exactify `(F_ab)` likewise, with identity `Q` and
`rank(Q)=s rank(q)`.  By step 5 applied twice and `(EXA3)`,

```text
||P-Q||<=||P-sum_i E_ii||+||sum_i E_ii-sum_a F_aa||+||sum_a F_aa-Q||
      =O((r+s)delta)<1
```

for `delta` small.  Two projections at distance `<1` are unitarily
equivalent by a nearby unitary: `z=PQ+(1-P)(1-Q)` satisfies
`||z-1||=O((r+s)delta)`, hence `z` is invertible, `zQ=Pz`, and the polar part
`u=z|z|^(-1)` is unitary with `uQu^*=P` and `||u-1||=O((r+s)delta)`.
Replace `f_ab` by `u f_ab u^*`.  Both exact systems now have identity `P`,
and `rank(P)` is divisible by `r` and by `s`.

This is the finite-dimensional case of the semiprojectivity of
`M_r(C)`; the argument above uses only finite-dimensional spectral theory and
polar decomposition, so it is independent of the cited sources.
