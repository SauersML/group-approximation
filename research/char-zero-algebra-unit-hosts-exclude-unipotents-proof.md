---
rg: 2
id: char-zero-algebra-unit-hosts-exclude-unipotents-proof
kind: route
title: Reduce modulo infinitely many primes, then use logarithms of unipotents
target: char-zero-algebra-unit-hosts-exclude-unipotents
requires: []
---

Notation as in the claim. `G~ <= B^x`, because `B` contains the lifts and their
inverses. Let `k` be the nilpotency index of `nu`, so `nu^k = 0`.

1. **Logarithms.** In a `Q`-algebra, a nilpotent `x` has
   `log(1 + x) = sum_(j>=1) (-1)^(j+1) x^j / j` and `exp(x) = sum_(j>=0) x^j / j!`.
   Both sums are finite, and `exp` and `log` are mutually inverse between
   nilpotents and unipotents, by the formal power-series identities. So a
   unipotent `w` determines `log w`, which is a polynomial in `w - 1`. If `w` is
   central, then `log w` is central.
2. **Powers of `1 + nu` stay non-central.** Let `q >= 1` and suppose
   `(1 + nu)^q` is central. Put `l = log(1 + nu)`. Then `(1 + nu)^q = exp(q l)`,
   so `q l = log((1 + nu)^q)` is central by step 1. So `l` is central, and then
   `nu = exp(l) - 1` is central, which contradicts (U). As a consequence, for every
   `q >= 1`, `u^q = c^q (1 + nu)^q` does not lie in `C`, because `C` is central.
3. **Congruence quotients.** For a prime `p`, let `pi_p : B -> B/pB` be the
   quotient. Central units of `A` that lie in `B` map to central units of `B/pB`.
   So `phi_p : G~ -> (B/pB)^x / Z(B/pB)^x` is a homomorphism that kills
   `G~ ∩ C`. It descends to `G`; let `N_p` be its kernel, a normal subgroup of `G`.
4. **`N_p` is non-trivial for every prime `p >= k`.** Such a `p` divides
   `binom(p, j)` for `0 < j < p`, and `nu^j = 0` for `j >= k`. So
   `(1 + nu)^p = 1 + sum_(j=1)^(k-1) binom(p, j) nu^j` lies in `1 + pB`, and
   `pi_p(u^p) = pi_p(c)^p` is a central unit. So `u^p` is in the kernel of
   `phi_p`, while its class in `G` is non-trivial by step 2.
5. **If `G` were simple.** Then `N_p = G` for every prime `p >= k`. So each
   `pi_p(g_i)` is central in `B/pB`, that is, `g_i b - b g_i` lies in `pB` for
   every `b in B`. For fixed `b` this holds for infinitely many primes, so
   `g_i b = b g_i` by (D). The `g_i` lie in `B`, so `G~` is abelian, and so `G`
   is abelian. An abelian simple group is cyclic of prime order `q`. Then
   `u^q in C`, which contradicts step 2. So `G` is not simple.
6. **(D) for subgroups of free `Z[1/m]`-modules.** If `b` lies in `pB` for
   infinitely many `p`, then each coordinate of `b` in `Z[1/m]` is divisible by
   infinitely many primes, so it is `0`. A finitely generated subring of
   `A_Z ⊗ Q` has bounded denominators, so it lies in `A_Z[1/m]` for some `m`.
   That is a free `Z[1/m]`-module when `A_Z` is a free abelian group.
7. **(D) for `M_n(B_0)`.** It suffices to treat one entry `b != 0` of `B_0`.
   - **A map to a number field.** `B_0 ⊗ Q` is a finitely generated `Q`-algebra
     and a domain. So `(B_0 ⊗ Q)[1/b]` is non-zero and has a maximal ideal. Its
     residue field is a number field `L`, by the Nullstellensatz.
   - **Bounded denominators.** This gives a ring map `f : B_0 -> L` with
     `f(b) != 0`. `f(B_0)` is finitely generated, so it lies in `O_L[1/M]` for
     some `M`.
   - **Norms.** If `b = p b'` with `b' in B_0`, then
     `N_(L/Q)(f(b)) = p^([L:Q]) N_(L/Q)(f(b'))`, and `N_(L/Q)(f(b')) in Z[1/M]`.
     So for `p` not dividing `M`, `p` divides the numerator of the non-zero
     rational `N_(L/Q)(f(b))`. Only finitely many primes do.
