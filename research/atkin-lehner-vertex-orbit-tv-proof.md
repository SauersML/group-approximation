---
rg: 2
id: atkin-lehner-vertex-orbit-tv-proof
kind: route
title: The two action kernels generate the unipotent part, so shared constituents are unit characters; count their orbits
target: atkin-lehner-twist-of-vertex-orbit-representation-is-disjoint
requires: []
---

**Setup.**  `h^-i C h^i = Stab_A(h^-i o)`, so `C^((k))` is the pointwise
stabilizer in `C` of the geodesic from `v_(-k) = h^-k o = [(1,0)]` (the
lattice `Z_p(1,0) + p^(2k) Z_p^2`) to `o`; a matrix in `SL_2(Z)` fixes this
class iff its lower-left entry is `0 mod p^(2k)`, i.e. `C^((k)) = Gamma_0(p^(2k))`.
`J v_(-k) = [(0,1)] = h^k o = v_k`, and `g_k = J^-1 h^k` maps `v_(-k) |-> o`,
`o |-> v_(-k)`; the displayed formula for `Ad(g_k)` is a direct matrix
computation, and `g_k^2 = -1`.  Vertices at distance `2k` from `o` are the
classes `[v]` of `Z_p v + p^(2k) Z_p^2` for primitive `v mod p^(2k)`, i.e.
`P^1(Z/p^(2k))`, with `SL_2(Z)` acting through `SL_2(Z/p^(2k))`; the
geodesic from `o` to `[v]` passes through `[v mod p^j]`, so `[v]` lies on
the far side of `o` (away from `v_(-k) = [1:0]`) iff `v mod p` is not
`[1:0]`, i.e. `[v] = [x:1]`.  The twisted action of `M in Gamma_0(p^(2k))` on
the sphere is the Moebius action of `Ad(g_k)(M) mod p^(2k) = [[d, -c/p^(2k)],[0, a]]`,
which on `[x:1]` is `x |-> (d x - c/p^(2k))/a`; it is well defined because
`c = 0 mod p^(2k)` and depends on `c mod p^(4k)`.

**Kernels.**  Both actions factor through
`G' = Gamma_0(p^(2k)) / {a = d = 1 (p^(2k)), b = 0 (p^(2k)), c = 0 (p^(4k))}`,
a group of order `p^(6k-1)(p-1)`.  The kernel of the untwisted action on
`P^1(Z/p^(2k))` (equivalently on its far part, which is already faithful
for the unipotent part) is `N_1 = {M = +-1 mod p^(2k)}`, i.e.
`a = d = +-1, b = 0 (p^(2k))`, `c` arbitrary in `p^(2k) Z/p^(4k)`.  The kernel
of the twisted action is `N_2 = Ad(g_k)^-1(N_1) = {a = d = +-1 (p^(2k)), c = 0 (p^(4k))}`,
`b` arbitrary.  Hence `N := N_1 N_2 = {a = d = +-1 mod p^(2k)}`, and
`G'/N` is the abelian group `(Z/p^(2k))^x / {+-1}` through `M |-> a`.

**Shared constituents.**  A constituent of `sigma` is trivial on `N_1`, one
of `sigma^g` is trivial on `N_2`; a common constituent is trivial on `N`.
The `N`-trivial part of a permutation representation on a set `Y` is the
permutation representation of `G'/N` on the orbit set `Y/N`, of total weight
`|Y/N|/|Y|`.  On the far sphere, `N_2` contains all `e_12(b)`, acting as
translations `x |-> x + b`, so `N` is transitive on `X`; on the twisted far
sphere, `N_1` contains all `e_21(c)`, `c in p^(2k) Z/p^(4k)`, acting as
translations `x |-> x - c/p^(2k)`, so `N` is transitive on `X^g`.  Thus the
only common constituent is the trivial representation, with weight
`1/|X| = p^(-2k)` on each side, and `(AL1)` follows:
`TV = (1 - p^(-2k)) + (1 - p^(-2k))`.

**Near sphere.**  On `S = P^1(Z/p^(2k))`, the far part is one `N`-orbit and
the near points `[1 : p y]`, `y in Z/p^(2k-1)`, are moved by `e_12(b)` to
`[1 : p y (1 + b p y)^(-1)]`; the lower unipotents of level `p^(2k)` and
`+-1` act trivially.  For `v_p(y) = t <= k-1` the orbit of `y` is
`y (1 + p^(t+1) Z)`, of size `p^(2k-2-2t)`, so the `(p-1)p^(2k-2-t)` such `y`
form `(p-1)p^t` orbits; for `t >= k` every `y` is fixed, giving
`(p-1)p^(2k-2-t)` orbits, and `y = 0` is one more.  Summing,
`nu = (p^k - 1) + (p^(k-1) - 1) + 1 = p^k + p^(k-1) - 1`, so `|S/N| = 1 + nu = p^(k-1)(p+1)`
and the shared weight is `p^(k-1)(p+1) / ((p+1) p^(2k-1)) = p^(-k)` on the
untwisted side.  The twisted side has the same orbit count (apply
`Ad(g_k)`, which normalizes `N`), and the two permutation representations of
the abelian group `G'/N` on `S/N` and `S^g/N` are isomorphic because the
twist acts on `a mod p^(2k)` by inversion, which preserves every orbit type
of a cyclic group action.  Hence the shared weights agree pointwise and
`TV = 2 - 2 p^(-k)`, which is `(AL2)`.

**Numerical check.**  Computing the isotypic decomposition of
`l^2(S) (+) l^2(S^g)` from the orbital algebra of the generators
`e_12(1)`, `e_21(p^(2k))`, `diag(u, u^-1)` (`u` generating the units) gives,
the following values (isotypic components found as connected classes of
eigenspaces of a generic element of the orbital algebra under the orbital
maps; run on MSI, 2026-08-25):

```text
(p,k)    far TV     2-2p^(-2k)   sphere TV   2-2p^(-k)
(2,1)    1.500000   1.500000     1.000000    1.000000
(2,2)    1.875000   1.875000     1.500000    1.500000
(2,3)    1.968750   1.968750     1.750000    1.750000
(3,1)    1.777778   1.777778     1.333333    1.333333
(3,2)    1.975309   1.975309     1.777778    1.777778
(5,1)    1.920000   1.920000     1.600000    1.600000
(7,1)    1.959184   1.959184     1.714286    1.714286
(11,1)   1.983471   1.983471     1.818182    1.818182
```

All fourteen values agree with `(AL1)`--`(AL2)` to the printed precision.
