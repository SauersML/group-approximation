"""Check that Cay(F_2, {a^+-1, b^+-1, (ab)^+-1}) is the tree of triangles with
three triangles per vertex: sphere sizes 1, 6, 24, 96, ... and, inside a ball,
cyclomatic number equal to the number of triangles {g, ga, gab} in the ball.

Run: python3 tree_of_triangles_check.py
"""


def red(w):
    out = []
    for c in w:
        if out and out[-1] == c.swapcase():
            out.pop()
        else:
            out.append(c)
    return "".join(out)


GENS = ["a", "A", "b", "B", "ab", "BA"]
R = 5
seen = {"": 0}
front = [""]
sizes = [1]
for n in range(1, R + 1):
    nf = []
    for g in front:
        for s in GENS:
            h = red(g + s)
            if h not in seen:
                seen[h] = n
                nf.append(h)
    front = nf
    sizes.append(len(nf))
print("sphere sizes:", sizes, "expected:", [1] + [6 * 4 ** k for k in range(R)])

ball = set(seen)
edges = set()
for g in ball:
    for s in GENS:
        h = red(g + s)
        if h in ball:
            edges.add(frozenset((g, h)))
triangles = sum(1 for g in ball if red(g + "a") in ball and red(g + "ab") in ball)
print("V =", len(ball), "E =", len(edges),
      "cyclomatic =", len(edges) - len(ball) + 1, "triangles in ball =", triangles)
