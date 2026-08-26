---
rg: 2
id: intertwiner-retention-criterion-proof
kind: route
title: Compress, polar-decompose, descend to the quotient, use simplicity and the abstract-embedding upgrade
target: intertwiner-retention-makes-leavitt-quotient-hyperlinear
requires:
  - abstract-unitary-embedding-upgrades-to-hyperlinear
  - leavitt-presentation-double-forces-restriction-instability
  - binary-leavitt-elementary-group-is-simple
---

Write `x_n(f) = P_n Pi_n(f) P_n` on `W_n`.  Since `Pi_n(f)` is unitary,
`x_n(f)^* x_n(f) = P_n - P_n Pi_n(f)^* (1 - P_n) Pi_n(f) P_n`, so by (IR1)
`||x_n(f)^* x_n(f) - 1||_(2,r_n) -> 0`, and the unitary `sigma_n(f)` in the
polar decomposition satisfies `||x_n(f) - sigma_n(f)||_(2,r_n) -> 0`
(`||x - u|x| ... ||`: for `x = u|x|`, `||x - u||_2 = || |x| - 1||_2 <= || |x|^2 - 1||_2`).
Multiplicativity: `x_n(fg) - x_n(f) x_n(g) = P_n Pi_n(f) (1 - P_n) Pi_n(g) P_n`,
of `||.||_(2,r_n)`-norm at most `||(1 - P_n) Pi_n(g) P_n||_(2,r_n) -> 0` by
unitary invariance; hence `||sigma_n(fg) - sigma_n(f) sigma_n(g)||_(2,r_n) -> 0`
for all `f, g`.  By (IR2), `||sigma_n(fk) - sigma_n(f)||_(2,r_n) -> 0` for
`k in K`, so along a free ultrafilter the maps `sigma_n` define a homomorphism
`Theta : Q = F/K -> U(prod_omega M_(r_n))` into the tracial matrix
ultraproduct (choose any representatives; the limit is independent of the
choice).  By (IR3), `Theta(f_0 K) != 1`.  The kernel of `Theta` is a normal
subgroup of the simple group `Q` (`binary-leavitt-elementary-group-is-simple`)
and is proper, hence trivial: `Theta` is injective.  By
`abstract-unitary-embedding-upgrades-to-hyperlinear` (3) => (1), `Q` is
hyperlinear.  (The unstable pairs themselves come from
`leavitt-presentation-double-forces-restriction-instability`; the criterion
is stated for any exact pairs.)
