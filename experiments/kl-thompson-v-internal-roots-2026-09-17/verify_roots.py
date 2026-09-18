"""Independent re-verification of ROOT lines produced by rootsearch.c.

For each line "<id> <word> ROOT endo=<name> t0=<d>:<r>,<d>:<r>,...":
  1. t0's domain and range are complete prefix codes (prefix-free, Kraft sum exactly 1),
     and the pairs define a bijection between them;
  2. phi(g) for g in {a, b, B, c} is rebuilt from the endomorphism table below
     (a complete prefix code P and a mask; phi(g) acts as g inside each masked cone,
     as the identity on the unmasked cones), at least one cone is masked, so phi is an
     injective endomorphism of the simple group V;
  3. the product phi(g_0) t0^(e_0) phi(g_1) t0^(e_1) ... in V (right action, tree-pair
     arithmetic of experiments/kl-thompson-v-census/vgroup.py) equals the identity.
Exits nonzero on the first failure.  Usage: verify_roots.py FILE [FILE ...]
"""
import os
import sys
from fractions import Fraction

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "kl-thompson-v-census"))
import vgroup as V  # noqa: E402

ENDOS = {
    "delta1": ([""], [1]),
    "delta2": (["0", "1"], [1, 1]),
    "delta3": (["0", "10", "11"], [1, 1, 1]),
    "delta4": (["00", "01", "10", "11"], [1, 1, 1, 1]),
    "g+1": (["0", "1"], [1, 0]),
    "g+g+1": (["0", "10", "11"], [1, 1, 0]),
    "g+1+1": (["0", "10", "11"], [1, 0, 0]),
    "1+g+g": (["0", "10", "11"], [0, 1, 1]),
    "delta5": (["0", "100", "101", "110", "111"], [1, 1, 1, 1, 1]),
    "g+g+g+1": (["0", "10", "110", "111"], [1, 1, 1, 0]),
    "g+1q": (["00", "01", "1"], [1, 0, 0]),
}
GEN = {"a": V.GENS["a"], "b": V.GENS["b"], "B": V.GENS["B"], "c": V.GENS["c"]}


def complete_prefix_code(words):
    ws = list(words)
    if len(set(ws)) != len(ws):
        return False
    for i, u in enumerate(ws):
        for j, v in enumerate(ws):
            if i != j and v.startswith(u):
                return False
    return sum(Fraction(1, 2 ** len(u)) for u in ws) == 1


def phi(name):
    code, mask = ENDOS[name]
    assert complete_prefix_code(code) and any(mask)
    out = {}
    for s, g in GEN.items():
        pairs = {}
        for p, m in zip(code, mask):
            if m:
                for d, r in g.pairs.items():
                    pairs[p + d] = p + r
            else:
                pairs[p] = p
        out[s] = V.V(pairs)
    return out


def main():
    ok = 0
    by_endo = {}
    for path in sys.argv[1:]:
        for line in open(path):
            parts = line.split()
            if len(parts) < 5 or parts[2] != "ROOT":
                continue
            word = parts[1]
            name = parts[3].split("=", 1)[1]
            body = parts[4].split("=", 1)[1]
            pairs = [tuple(x.split(":")) for x in body.split(",")]
            dom, ran = [d for d, _ in pairs], [r for _, r in pairs]
            assert complete_prefix_code(dom) and complete_prefix_code(ran), line
            t0 = V.V(dict(pairs))
            T0 = t0.inverse()
            ph = phi(name)
            w = V.identity()
            cur = None
            for ch in word:
                if ch in "tT":
                    if cur is not None:
                        w = w * ph[cur]
                    w = w * (t0 if ch == "t" else T0)
                    cur = None
                else:
                    assert cur is None and ch in GEN, line
                    cur = ch
            assert cur is None, line
            if w != V.identity():
                print("FAILED", line.strip())
                sys.exit(1)
            ok += 1
            by_endo[name] = by_endo.get(name, 0) + 1
    print("verified", ok, "ROOT certificates", dict(sorted(by_endo.items())))


if __name__ == "__main__":
    main()
