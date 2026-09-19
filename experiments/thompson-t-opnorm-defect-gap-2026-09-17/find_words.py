"""Find short words in alpha = rot(1/4), beta = C_cfp^-1 equal to the CFP generators.

Convention 'right': the leftmost letter is applied first (w = w1...wk acts as wk o ... o w1).
Letters: a = alpha, b = beta (a^-1 = aaa, b^-1 = bb, so positive words suffice).
"""
import json
from pl_circle import word, eq, inverse
from verify_ls import A_cfp, B_cfp, C_cfp, rot

alpha, beta = rot("1/4"), inverse(C_cfp)
gens = {"a": alpha, "b": beta}
targets = {"A": A_cfp, "B": B_cfp, "C": C_cfp}
found = {}
frontier = [""]
for L in range(1, 15):
    new = []
    for w in frontier:
        for ch in "ab":
            v = w + ch
            if v.endswith("aaaa") or v.endswith("bbb"):
                continue
            new.append(v)
    frontier = new
    for v in frontier:
        f = word(gens, v, "right")
        for k, t in targets.items():
            if k not in found and eq(f, t):
                found[k] = v
    if len(found) == 3:
        break
print(found)
for k, v in found.items():
    assert eq(word(gens, v, "right"), targets[k])
json.dump({"convention": "right (leftmost letter applied first)", "alpha": "rotation by 1/4",
           "beta": "C_cfp^-1: [0,1/2)->[1/2,3/4), [1/2,3/4)->[3/4,1), [3/4,1)->[0,1/2)",
           "words": found}, open("out_find_words.json", "w"), indent=1)
