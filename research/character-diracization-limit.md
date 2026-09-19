---
rg: 2
id: character-diracization-limit
kind: claim
title: Conjugate tensor powers drive every character to the regular character of its scalar-kernel quotient
distinct_from:
  balanced-replica-hs-amplification: that bounds the multiplicative defect of the balanced power of one finite unitary *table* and needs the defect bookkeeping; this identifies the pointwise *limit* of the powers of an arbitrary character as a normal-subgroup indicator, with no finite table and no defect in the statement
  ce-characters-closed-multiplicative-semigroup: that is the closure property of the microstate locus; this is the limit computation for the powers themselves, which holds for characters that are nowhere near that locus
artifacts:
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
---

ESTABLISHED, elementary.  Let `tau` be a character of a group `Gamma` (a
normalized central positive-definite function).  Write `(M, tau)` for its
tracial GNS algebra and `u_g` for the image of `g`.  Put

```text
Phi_k(g) = |tau(g)|^{2k},
K_tau    = { g in Gamma : |tau(g)| = 1 }.
```

**Lemma.**  Each `Phi_k` is again a character of `Gamma`; `K_tau` is a normal
subgroup of `Gamma`; and

```text
Phi_k(g)  ->  1_{K_tau}(g)   pointwise as k -> infinity,
```

i.e. the powers converge to the regular character of `Gamma/K_tau` pulled
back to `Gamma`.

**Proof.**  `|tau|^2 = tau · conj(tau)` is the character of `pi ⊗ conj(pi)`,
so `Phi_k` is a character.  In the GNS representation,

```text
|| u_g - tau(g)1 ||_2^2 = 1 - conj(tau(g))tau(g) - tau(g)conj(tau(g)) + |tau(g)|^2
                        = 1 - |tau(g)|^2,
```

so `|tau(g)| = 1` holds exactly when `u_g` is the scalar `tau(g)1`.  If
`u_g = tau(g)1` then `u_{hgh^{-1}} = u_h u_g u_h^{-1} = tau(g)1`, and the
scalars form a subgroup, so `K_tau` is normal.  Finally `t^k -> 1` for
`t = 1` and `t^k -> 0` for `t = |tau(g)|^2 < 1`.  QED

## What the limit is, and is not

The limit is always the regular character of a quotient of `Gamma`.  So the
construction is a canonical **Diracization map**

```text
{ characters of Gamma }  ->  { regular characters of quotients of Gamma },
       tau               |->  1_{K_tau},
```

turning arbitrary trace information into exactly the kind of object
hyperlinearity is about.  Two facts fix its scope.

- `tau` is multiplicative across `K_tau`: for `k in K_tau`,
  `tau(gk) = tau(g)tau(k)`, so `|tau|` descends to `Gamma/K_tau`, where it is
  `< 1` off the identity.  The map keeps only the locus where the GNS
  representation is projectively trivial and discards everything else about
  `tau`.
- The domain is not a group-theoretic invariant of `tau` up to small
  perturbation: `K_tau` is a closed condition on an open set of characters, so
  arbitrarily small perturbations of `tau` can collapse `K_tau` to `{e}`.

## The IRS instance

For an invariant random subgroup `mu` on `Gamma`, the function
`tau_mu(g) = Pr_{H ~ mu}[g in H]` is a character, and intersecting `k` iid
samples gives the character of the intersection IRS:

```text
tau_{mu^{∩ k}}(g) = tau_mu(g)^k  ->  1_{core(mu)}(g),
core(mu) = { g : Pr[g in H] = 1 }.
```

So iid intersection is the Diracization map on the IRS side, and `K_{tau_mu}`
is the normal core of `mu` (the values are real and in `[0,1]`, so the modulus
is invisible here).  This is the same operation `notes/FALSE_RECENT_LITERATURE_AUDIT.md`
§3 refers to when it records that **taking normal cores destroys the
information in the currently available examples**; see
`diracization-gap-equals-nonhyperlinear-group` for the general form of that
verdict.
