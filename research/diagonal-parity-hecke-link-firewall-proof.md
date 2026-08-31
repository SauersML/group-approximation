---
rg: 2
id: diagonal-parity-hecke-link-firewall-proof
kind: route
title: Compute the Hecke normal blocks and a collapsing additive link character
target: diagonal-parity-is-hecke-but-tau-misses-local-links
requires:
  - proper-torus-diagonal-code-is-incomplete-cover-curl
  - diagonal-exact-inversion-is-two-cubic-parity-code
  - sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair
---

Give every coset function the normalized counting norm inherited by its
constant lift to `G_m`. For `f` fixed by `N`, the first syndrome lift is

`f+L_a f+L_(a^2)f=3e_A f`.

It is fixed by `A`, and the second row is similarly `3e_B f`. This proves
(DHT3). Orthogonal projection back to the input is `e_N`, so taking the
adjoint gives

`D_m^*D_m=9e_N(e_A+e_B)e_N`.

All left translations commute with the right regular action. The finite
Peter-Weyl decomposition is

`C[G_m]=direct_sum_pi V_pi tensor V_pi^*`,

with the left action on `V_pi` and the right action on `V_pi^*`. Taking
`N`-fixed vectors in the first tensor factor and applying the displayed
normal operator proves (DHT5). Reducing the integral matrices
`1+L_a+L_(a^2)` and `1+L_b+L_(b^2)` modulo two gives exactly the two
parity rows in the diagonal-code claim.

For completeness, consider the cyclic label before imposing edge
reversal. The left action of `T_s/H` on `H-left-cosets in G_m` is free on
each fiber over `T_s-left-cosets in G_m`. If its order `i` is odd, its
group algebra over a characteristic-two splitting field is semisimple.
Thus the oriented module is the direct sum of its `chi`-isotypic spaces.
The Weyl element satisfies

`x t x=t^(-1)` modulo `H`,

so it exchanges the `chi` and `chi^(-1)` spaces. Since odd `i` has no
nontrivial self-inverse character, the unoriented fixed space consists of
the trivial fixed block and one fixed graph for every pair
`{chi,chi^(-1)}`.

If `i=2^s j` with `j` odd, the two-primary factor instead has

`k[C_(2^s)]=k[z]/((z-1)^(2^s))`.

Its powers of the augmentation ideal give a nilpotent filtration, not a
character direct sum. This proves the odd/even label statement. It does
not diagonalize the curl: the oriented label action is a left action,
whereas (DHT3) is equivariant for the right `G_m` action. Geometrically,
left label translation moves a selected boundary to a generally omitted
triangle lift. Algebraically, `e_A` and `e_B` need not commute with left
translation by `T_s`. Hence (DHT5) is the valid automatic block
decomposition.

It remains to compute one vertex link. Write

`d=ord_m(4)` and `H={h^k:0<=k<d}`, where `h=h(2)`.

Every element of `P=UH=HU` has a unique form `h^k u(z)`, and the incident
edge represented by it has link coordinate `z`. The conjugation rule is

`h^k u(z) h^(-k)=u(4^k z)`.

For the `a=xt` face through the vertex `P`, the two incident edges are
represented by `g` and `tg`. If `g=h^k u(z)`, then

`t g=h^k u(z+4^(-k))`.

As `k` varies, these differences are precisely `K_m=<4>`. An undirected
link edge contributes both signs of every difference.

For the `b=x t^2 r` face, put `y=t^2r`. The same triangle calculation
uses `g` and `yg`. Since

`y h^k u(z)=t^2h^(k+1)u(z)
            =h^(k+1)u(z+(1/2)4^(-k))`,

the second connection multiset is `(1/2)K_m`. The two face orbits each
give degree `2d`, proving the normalized adjacency formula (DHT6).

Now take `m_n=4^n-1`. Certainly `4^n=1 mod m_n`; if `0<j<n`, then
`0<4^j-1<m_n`, so `4^j` is not one modulo `m_n`. Hence
`ord_(m_n)(4)=n`.

For the additive character

`phi_n(z)=exp(4 pi i z/m_n)`,

translation by `q` has eigenvalue `exp(4 pi i q/m_n)`. Translation by
`q/2` has eigenvalue `exp(2 pi i q/m_n)`, because twice the modular
inverse-half representative is congruent to `q`. Adding inverse
translations takes real parts. Substitution in (DHT6) proves (DHT7).

Finally use `1-cos(theta)<=theta^2/2` and the geometric series:

`sum_(j=0)^(n-1) 16^j=(16^n-1)/15`.

It follows that

`1-lambda_n
 <=(1/(4n)) sum_j [(4 pi 4^j/m_n)^2
                  +(2 pi 4^j/m_n)^2]
 =(pi^2/(3n)) (16^n-1)/(4^n-1)^2
 =(pi^2/(3n)) (4^n+1)/(4^n-1)
 <4/n`

for `n>=2`. The character is nonconstant, so this is an upper bound on
the link spectral gap.

Selberg/property tau controls a fixed global Cayley averaging operator on
the congruence quotients; the established tau-pair claim supplies that
uniform global gap. The operators (DHT6) are different, growing additive
link averages, and the displayed nonconstant eigenfunctions prove their
gaps vanish. Therefore a theorem requiring uniform link expansion cannot
be invoked from property tau alone. No step turns the link eigenfunction
into a binary one-cochain far from all cocycles, so the final statement is
a firewall rather than a claimed failure of Hamming soundness.
