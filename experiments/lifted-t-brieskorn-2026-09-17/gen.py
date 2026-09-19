"""Breadth-first search for words in alpha, beta equal (in T) to the CFP generators
A, B, C.  Elements are compared by their canonical mod-1 lift; for each hit we also
record the exact lift of the word, i.e. the power of z by which it differs from the
canonical lift of the target."""
from pl import Lift, ID
from run import alpha, beta, A, B, C

gens = {"a": alpha, "A_": alpha.inverse(), "b": beta, "B_": beta.inverse()}
inv = {"a": "A_", "A_": "a", "b": "B_", "B_": "b"}
targets = {"A": A.mod1(), "B": B.mod1(), "C": C.mod1()}
found = {}
seen = {ID.mod1(): ()}
frontier = [((), ID)]
for depth in range(1, 15):
    new = []
    for word, g in frontier:
        for s, h in gens.items():
            if word and inv[word[-1]] == s:
                continue
            gh = g * h
            key = gh.mod1()
            if key in seen:
                continue
            seen[key] = word + (s,)
            new.append((word + (s,), gh))
            for t, tk in targets.items():
                if t not in found and key == tk:
                    found[t] = (word + (s,), gh)
    frontier = new
    print("depth", depth, "ball", len(seen), "found", sorted(found))
    if len(found) == 3:
        break
for t, (word, g) in found.items():
    print(t, "=", " ".join(word))
