---
rg: 2
id: fournier-facio-simple-wreath-shift-proof
kind: route
title: Iterate the compression letter on the commuting simple group and use centerless normal-subgroup rigidity
target: fournier-facio-group-contains-simple-wreath-shift
requires:
  - fournier-facio-torsion-free-skeleton
---

The skeleton supplies: `Gamma<=G`; `t Gamma t^-1<=Gamma`; a finitely
presented infinite simple group `S` with `pi|_S` injective; and
`J=t^-1 pi(S) t` with `[Gamma,J]=1`, `Gamma cap J=1`, `t J t^-1=pi(S)<=Gamma`.
Each `J_k` is conjugate to `pi(S)`, so it is isomorphic to `S`.  It is
nonabelian (an abelian simple group is finite) and hence centerless.

**(W1).**  `J_1=pi(S)<=Gamma`.  If `J_k<=Gamma` then
`J_(k+1)=t J_k t^-1<=t Gamma t^-1<=Gamma`.

**(W3).**  For `k>=0`, `t^k Gamma t^-k<=Gamma` by iterating the compression.
Then `[J_-k,Gamma]=t^-k [J_0, t^k Gamma t^-k] t^k<=t^-k [J_0,Gamma] t^k=1`.

**(W2).**  For `k>=1`, `J_k<=Gamma` by (W1) and `J_0` centralizes `Gamma`, so
`[J_0,J_k]=1`.  Conjugating by `t^a` gives `[J_a,J_(a+k)]=1`.

**(W4).**  By (W2) the multiplication map
`mu:(+)_(k in Z) J_k -> G` is a homomorphism.  Its kernel `N` is normal in the
direct sum and meets every summand trivially, because each `J_k` embeds in
`G`.  Suppose `1!=n in N` and choose `k` with component `n_k!=1`.  As `J_k` is
centerless there is `a in J_k` with `[n_k,a]!=1`.  The other components of
`n` commute with `a`, so `[n,a]=[n_k,a]`.  This is a nontrivial element of
`N cap J_k`, a contradiction.  So `N=1`.

**(W5).**  Define `nu:S wr Z -> G` on the base `(+)_Z S` through the
isomorphisms `S -> J_k`, `s |-> t^k (t^-1 pi(s) t) t^-k`, and send the
generator of `Z` to `t`.  The relation `t J_k t^-1=J_(k+1)` matches the shift
action, so `nu` is a homomorphism, and (W4) makes it injective on the base.
Let `x=a tau^m` lie in `ker nu`, with `a` in the base and `m!=0`.  Then
`t^m=mu(a)^-1`.  For `j in J_0`, the element `t^m j t^-m` lies in `J_m`,
while `mu(a)^-1 j mu(a)` lies in `J_0`, because `mu(a)` normalizes every
summand.  These two elements are equal, and `J_m cap J_0=1` by (W4).  So
`j=1` for every `j in J_0`, which is absurd.  Hence `m=0`, and then `a=1`.

**(W6).**  `C=mu((+)_(k<=0) J_k)` centralizes `Gamma` by (W3), so
`Gamma cap C` is central in `C`.  `C` is a direct sum of centerless groups,
so `Gamma cap C=1`.

**(W7).**  `J_1<=Gamma` and `t Gamma t^-1<=Gamma`.  They commute, since
`[J_1,t Gamma t^-1]=t[J_0,Gamma]t^-1=1`, and
`J_1 cap t Gamma t^-1=t(J_0 cap Gamma)t^-1=1`.  So
`J_1 x t Gamma t^-1<=Gamma`.  Conjugating by `t^n` gives
`t^n Gamma t^-n>=J_(n+1) x t^(n+1) Gamma t^-(n+1)`.  Moreover `J_1,...,J_n`
centralize `t^n Gamma t^-n`: for `1<=i<=n`,
`t^n Gamma t^-n<=t^i Gamma t^-i`, which `J_i=t^i J_0 t^-i` centralizes.  The
intersection of `J_1 x ... x J_n` with `t^n Gamma t^-n` is therefore central
in the centerless group `J_1 x ... x J_n`, hence trivial, and induction gives
(W7).

**Properness remark.**  If `J_1 x t Gamma t^-1=Gamma`, then `S=J_1` would be
a quotient of `Gamma`, and so Kazhdan.
