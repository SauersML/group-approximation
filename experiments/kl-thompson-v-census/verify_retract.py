"""Independent re-verification of RETRACT certificates from certify.py output.

For each line "<id> <word> RETRACT k=<k> t0=<pairs>":
  1. t0's domain and range are complete prefix codes (prefix-free, Kraft sum exactly 1);
  2. delta_k(g) is built over the fixed complete prefix code P_k;
  3. the product g_0 * t^(e_0) * g_1 * ... in V (right action, tree-pair arithmetic of vgroup.py)
     equals the identity.
Exits nonzero on the first failure.  Usage: verify_retract.py FILE [FILE ...]
"""
import ast
import sys
from fractions import Fraction
import vgroup as V

PCODES = {1: [""], 2: ["0", "1"], 3: ["0", "10", "11"], 4: ["00", "01", "10", "11"]}
E = {"a": V.GENS["a"], "b": V.GENS["b"], "B": V.GENS["B"], "c": V.GENS["c"]}


def complete_prefix_code(words):
    ws = list(words)
    if len(set(ws)) != len(ws):
        return False
    for i, u in enumerate(ws):
        for j, v in enumerate(ws):
            if i != j and v.startswith(u):
                return False
    return sum(Fraction(1, 2 ** len(u)) for u in ws) == 1


def main():
    ok = 0
    for path in sys.argv[1:]:
        for line in open(path):
            parts = line.split()
            if len(parts) < 5 or parts[2] != "RETRACT":
                continue
            word, k = parts[1], int(parts[3].split("=")[1])
            pairs = ast.literal_eval(parts[4].split("=", 1)[1])
            dom, ran = [d for d, _ in pairs], [r for _, r in pairs]
            assert complete_prefix_code(dom) and complete_prefix_code(ran), line
            t0 = V.V(dict(pairs))
            code = PCODES[k]
            assert complete_prefix_code(code)
            delta = {s: V.V({p + d: p + r for p in code for d, r in E[s].pairs.items()}) for s in E}
            w = V.identity()
            cur = None
            for ch in word:
                if ch in "tT":
                    if cur is not None:
                        w = w * delta[cur]
                    w = w * (t0 if ch == "t" else t0.inverse())
                    cur = None
                else:
                    assert cur is None, line
                    cur = ch
            assert cur is None, line
            if w != V.identity():
                print("FAILED", line.strip())
                sys.exit(1)
            ok += 1
    print("verified", ok, "RETRACT certificates")


if __name__ == "__main__":
    main()
