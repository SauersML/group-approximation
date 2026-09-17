---
rg: 2
id: fpbs-kazhdan-cofinal-mod-p-growth-vanishes
kind: claim
title: In a Kazhdan group mod-p homology growth tends to zero along the profinite topology
distinct_from:
  fpbs-kazhdan-no-rapid-descent: that concerns abelian p-series and pro-p-cofinal families; this concerns families cofinal in the full profinite topology, whose members have arbitrary finite quotients, and needs the cocycle-support iteration rather than Theorem 1.15 as a black box.
  fpbs-kazhdan-positive-rank-gradient: that asks for d(Gamma_n) linear along some Farber chain; this proves d_p(Gamma_n) sublinear, for each fixed p, along every profinitely cofinal chain, which leaves d(Gamma_n) itself and non-cofinal chains open.
artifacts:
  - research/artifacts/fpbs/docs/kazhdan-mod-p-growth-2026-09-17.md
---

**ESTABLISHED (written deduction).** Let `Gamma` be a group with property (T),
`p` a prime and `c > 0`. Then there is a finite index subgroup `M` of
`Gamma` such that every finite index normal subgroup `N` contained in `M`
has `d_p(N) < c[Gamma:N]`.

Equivalently, no family of finite index normal subgroups with
`d_p(N) >= c[Gamma:N]` is cofinal in the profinite topology. In particular,
`d_p(Gamma_n)/[Gamma:Gamma_n] -> 0` along every nested normal chain whose
boundary action is the profinite completion.

**General form.** The same holds for every *`p`-Frattini closed* family `F` of
finite index normal subgroups, meaning each `N` in `F` contains a member inside
`[N,N]N^p`. No such family has `d_p(N) >= c[Gamma:N]` for all members.
Profinitely cofinal families and normal chains with
`Gamma_(n+1) <= [Gamma_n,Gamma_n]Gamma_n^p` are special cases.

**All primes at once.** Also, for every `c > 0` there is a finite index `M` with
`d(N^ab) < c[Gamma:N]` for every finite index normal `N` contained in `M`.
Here `d(N^ab) = max_p d_p(N)` is the rank of the finite abelianization. The
proof uses a Hadamard bound: on a finitely presented Kazhdan cover with
relators of length at most `L`, `d_p(N) <= |R|[Gamma:N] log L/log p`. So only
primes `p <= L^(|R|/c)` can carry linear growth, and the fixed-prime statement
handles those finitely many.

Consequence for `fpbs-fixed-price-counterexample-exists`: a proof that the
profinite completion action of a Kazhdan group has cost above one cannot be an
abelianization count at any prime or combination of primes. The generators
must be forced by non-central chief factors of finite quotients of `Gamma_n`:
twisted `H^1(Gamma_n;M)` for nontrivial modules `M`, or non-abelian crowns.
Otherwise they come from `d(Gamma_n)` exceeding the profinite rank. A chain-based homological certificate must use a
Farber chain that is not `p`-Frattini closed and is not an abelian `p`-series
with rapid descent.
