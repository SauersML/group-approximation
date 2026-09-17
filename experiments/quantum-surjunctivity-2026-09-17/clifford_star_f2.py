#!/usr/bin/env python3
"""Exhaustive Clifford search on F_2 = <a,b>, one qudit of prime dimension p per site,
propagation N = {1, a, b}.

A Clifford *-endomorphism Phi of the tensor product of M_p over F_2 is fixed by
Phi(X_e) = P and Phi(Z_e) = Q, where P and Q are Pauli strings on the slots
N = {1, a, b}. A Pauli string is a vector (x_1, x_a, x_b, z_1, z_a, z_b) in F_p^6.
Up to phases, Phi is a unital *-homomorphism iff
  (H) beta(P, Q) = beta(X, Z) = 1, the full symplectic product over the three slots, and
  (L) every translate Phi(A_h), h != e, commutes with Phi(A_e).
For h in N N^{-1} \\ {e} = {a, b, a^-1, b^-1, a b^-1, b a^-1}, the sets hN and N meet in exactly
one site:
  h = a      : translate slot 1 = base slot a
  h = b      : translate slot 1 = base slot b
  h = a b^-1 : translate slot b = base slot a
together with their inverses (the same pairs, with the orientation swapped).
So (L) says that for all R, S in {P, Q} and each ordered slot pair (s, t) in
{(1,a), (a,1), (1,b), (b,1), (a,b), (b,a)}, the one-site symplectic product of R_s and S_t is 0.

The script lists every solution and checks whether it is a wiring: P and Q supported on one
common slot. Then Phi is a shift composed with an on-site Clifford, so it is bijective.
The theorem `sofic-groups-are-quantum-surjunctive` predicts that no strict solution exists.
"""
import itertools
import json
import sys

SLOTS = ["1", "a", "b"]
PAIRS = [(0, 1), (1, 0), (0, 2), (2, 0), (1, 2), (2, 1)]


def site_form(p, R, s, S, t):
    # one-site symplectic product of R at slot s and S at slot t
    return (R[s] * S[3 + t] - R[3 + s] * S[t]) % p


def full_form(p, R, S):
    return sum(R[i] * S[3 + i] - R[3 + i] * S[i] for i in range(3)) % p


def support(R):
    return {i for i in range(3) if R[i] or R[3 + i]}


def search(p):
    strings = [v for v in itertools.product(range(p), repeat=6) if any(v)]
    # (L) with R = S constrains each string by itself; prefilter
    self_ok = [v for v in strings if all(site_form(p, v, s, v, t) == 0 for s, t in PAIRS)]
    solutions = []
    for P in self_ok:
        for Q in self_ok:
            if full_form(p, P, Q) != 1:
                continue
            if all(site_form(p, P, s, Q, t) == 0 and site_form(p, Q, s, P, t) == 0 for s, t in PAIRS):
                solutions.append((P, Q))
    wiring = [(P, Q) for P, Q in solutions if len(support(P) | support(Q)) == 1]
    strict_candidates = [(P, Q) for P, Q in solutions if len(support(P) | support(Q)) != 1]
    return {
        "p": p,
        "pauli_strings": len(strings),
        "strings_passing_self_locality": len(self_ok),
        "solutions": len(solutions),
        "wiring_solutions": len(wiring),
        "non_wiring_solutions": len(strict_candidates),
        "solutions_per_slot": {SLOTS[i]: sum(1 for P, Q in wiring if support(P) | support(Q) == {i})
                                for i in range(3)},
        "on_site_cliffords_Sp2_Fp_order": p * (p * p - 1),
    }


def main():
    primes = [int(x) for x in sys.argv[1:]] or [2, 3]
    out = [search(p) for p in primes]
    print(json.dumps(out, indent=2))
    ok = all(r["non_wiring_solutions"] == 0 and r["solutions"] == 3 * r["on_site_cliffords_Sp2_Fp_order"]
             for r in out)
    print("VERDICT:", "every Clifford endomorphism with propagation {1,a,b} is a wiring (bijective)" if ok
          else "non-wiring solution found; inspect output")


if __name__ == "__main__":
    main()
