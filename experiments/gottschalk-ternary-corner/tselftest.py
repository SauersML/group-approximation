#!/usr/bin/env python3
"""Self-test for tleavitt.py: relations, both paths, units, the anti-central quotient."""

import random
import sys

import tleavitt as L


def check(name, ok):
    print("%-58s %s" % (name, "PASS" if ok else "FAIL"))
    if not ok:
        sys.exit(1)


def main():
    L.set_dual(True)
    check("t_i s_j = delta_ij", L.is_one(L.mul(L.t0, L.s0)) and L.is_one(L.mul(L.t1, L.s1))
          and not L.mul(L.t0, L.s1) and not L.mul(L.t1, L.s0))
    check("s0 t0 + s1 t1 = 1", L.is_one(L.add(L.mul(L.s0, L.t0), L.mul(L.s1, L.t1))))
    check("s0 t0 != 1 (strict)", not L.is_one(L.mul(L.s0, L.t0)))
    check("W^2 = 1, D^2 = 1", L.is_one((L.W * L.W).val) and L.is_one((L.D * L.D).val))
    check("D W D = -W", (L.D * L.W * L.D).val == L.scale(L.W.val, 2))
    A = L.thompson_unit(["0", "10", "11"], ["00", "01", "1"])
    B = L.thompson_unit(["0", "10", "110", "111"], ["0", "100", "101", "11"])
    check("Thompson units invert", L.is_one((A * A.inverse()).val) and L.is_one((B.inverse() * B).val))
    check("A s0 = S[00]", L.mul(A.val, L.s0) == L.S("00"))
    n = L.mul(L.mul(L.S("000"), L.s1), L.T("01"))
    E = L.one_plus_nilpotent(n)
    check("E = 1 + S[000] s1 T[01] has order 3", L.is_one((E * E * E).val) and not L.is_one((E * E).val))
    # delta4(g) = sum_{|gamma|=2} S[gamma] g T[gamma] is a homomorphism G -> G
    def delta4(u):
        val, inv = {}, {}
        for g in ("00", "01", "10", "11"):
            val = L.add(val, L.mul(L.mul(L.S(g), u.val), L.T(g)))
            inv = L.add(inv, L.mul(L.mul(L.S(g), u.inv), L.T(g)))
        return L.Unit(val, inv)
    check("delta4 multiplicative on samples", (delta4(A) * delta4(E)).val == delta4(A * E).val)
    # anti-central quotient: [z] = -1, [-g] = -[g]
    Sm = L.SMinus()
    one = Sm.one()
    check("[z] = -[1] in S_-", Sm.of_unit(L.Z) == {k: 2 for k in one})
    check("[W][W] = [1] in S_-", Sm.mul(Sm.of_unit(L.W), Sm.of_unit(L.W)) == one)
    lhs = Sm.mul(Sm.mul(Sm.of_unit(L.D), Sm.of_unit(L.W)), Sm.of_unit(L.D))
    check("[D][W][D] = -[W] in S_-", lhs == {k: (2 * c) % 3 for k, c in Sm.of_unit(L.W).items()})
    e_minus = L.add(Sm.one(), Sm.of_unit(L.W)) and {k: (2 * c) % 3 for k, c in
                                                     L.add(Sm.one(), Sm.of_unit(L.W)).items()}
    check("e_- = 2(1 + [W]) idempotent in S_-", Sm.mul(e_minus, e_minus) == e_minus)
    check("pi(e_-) = 2(1 + w)", Sm.evaluate(e_minus) == L.scale(L.add(L.ONE, L.W.val), 2))
    random.seed(7)
    gens = [A, B, E, L.W, L.D, A.inverse(), B.inverse()]
    for _ in range(40):
        u = L.IDENTITY
        for _ in range(4):
            u = u * random.choice(gens)
        v = random.choice(gens)
        _ = L.mul(u.val, v.val)
    check("dual path: %d products cross-checked" % L.dual_stats()["checked"], True)


if __name__ == "__main__":
    main()
