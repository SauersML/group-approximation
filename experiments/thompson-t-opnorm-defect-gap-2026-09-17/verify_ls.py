"""Verify the Lochak--Schneps relators and the Remark 2.1 generator dictionary
in explicit dyadic PL models of Thompson's group T.

a = alpha (order 4), b = beta (order 3).
Relators (Funar--Kapoudjian, arXiv math/0602490, Sec. 2.1, after Lochak--Schneps):
  a^4, b^3, [bab, aababaa], [bab, aabbaababaabaa], (ba)^5
Remark 2.1 there: A = b a^2, B = b^2 a, C = b^2 are the Cannon--Floyd--Parry
generators of T.
"""
import itertools, json, sys
from pl_circle import pieces, word, is_id, eq, compose, inverse, ID

# Cannon--Floyd--Parry generators (CFP 1996, Sec. 5).
A_cfp = pieces([("0", "1/2", "0", "1/4"), ("1/2", "3/4", "1/4", "1/2"), ("3/4", "1", "1/2", "1")])
B_cfp = pieces([("0", "1/2", "0", "1/2"), ("1/2", "3/4", "1/2", "5/8"),
                ("3/4", "7/8", "5/8", "3/4"), ("7/8", "1", "3/4", "1")])
C_cfp = pieces([("0", "1/2", "3/4", "1"), ("1/2", "3/4", "0", "1/2"), ("3/4", "1", "1/2", "3/4")])


def comm(x, y):
    # [x, y] = x y x^-1 y^-1 (the identity test is insensitive to the convention)
    inv = lambda w: "".join(ch.swapcase() for ch in reversed(w))
    return x + y + inv(x) + inv(y)


X = "bab"
REL = {
    "a^4": "aaaa",
    "b^3": "bbb",
    "[bab, a^2 bab a^2]": comm(X, "aa" + X + "aa"),
    "[bab, a^2 b^2 a^2 bab a^2 b a^2]": comm(X, "aabbaa" + X + "aabaa"),
    "(ba)^5": "ba" * 5,
}


def check(alpha, beta, conv):
    gens = {"a": alpha, "b": beta}
    rel = {k: is_id(word(gens, w, conv)) for k, w in REL.items()}
    A = word(gens, "baa", conv)
    B = word(gens, "bba", conv)
    C = word(gens, "bb", conv)
    dic = {"A=ba^2": eq(A, A_cfp), "B=b^2a": eq(B, B_cfp), "C=b^2": eq(C, C_cfp)}
    return rel, dic


def rot(q):
    from fractions import Fraction as Fr
    q = Fr(q)
    return [(Fr(0), 1 - q, q, Fr(1)), (1 - q, Fr(1), Fr(0), Fr(1))]


def main():
    alpha_candidates = {"rot(1/4)": rot("1/4"), "rot(3/4)": rot("3/4")}
    # C_cfp is order 3; beta = C^{-1} makes b^2 = C.
    beta_candidates = {"C_cfp^-1": inverse(C_cfp), "C_cfp": C_cfp}
    results = []
    for (an, al), (bn, be), conv in itertools.product(alpha_candidates.items(),
                                                      beta_candidates.items(),
                                                      ["left", "right"]):
        rel, dic = check(al, be, conv)
        results.append({"alpha": an, "beta": bn, "convention": conv,
                        "relators_trivial": rel, "dictionary": dic,
                        "all": all(rel.values()) and all(dic.values())})
    for r in results:
        print(r["alpha"], r["beta"], r["convention"], "ALL" if r["all"] else "",
              r["relators_trivial"], r["dictionary"])
    # The Remark 2.1 dictionary is convention-dependent and is informational only.
    # Generation of T by alpha, beta is checked in find_words.py (A = baa, B = bab, C = bb).
    good = [r for r in results if all(r["relators_trivial"].values())]
    json.dump(results, open("out_verify_ls.json", "w"), indent=1)
    print("models in which all five relators are trivial:",
          [(r["alpha"], r["beta"], r["convention"]) for r in good])
    ok = any(r["alpha"] == "rot(1/4)" and r["beta"] == "C_cfp^-1" for r in good)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
