"""Enumerate every relative root position for one completeness-fold attachment.

Run through MSI.  The audit is purely combinatorial and uses the A_4 root
system only to leave three spare indices visible.
"""


N = 5
alpha = (0, 1)


def classify(beta):
    a, b = alpha
    c, d = beta
    if beta == (b, a):
        return "opposite"
    if c == b and d != a:
        return "right-composable"
    if d == a and c != b:
        return "left-composable"
    if c == a:
        return "same-source"
    if d == b:
        return "same-target"
    if {a, b}.isdisjoint({c, d}):
        return "distant"
    raise AssertionError((alpha, beta))


roots = [(i, j) for i in range(N) for j in range(N) if i != j]
counts = {}
for beta in roots:
    if beta == alpha:
        continue
    kind = classify(beta)
    counts[kind] = counts.get(kind, 0) + 1

assert sum(counts.values()) == len(roots) - 1 == 19
assert counts == {
    "opposite": 1,
    "right-composable": 3,
    "left-composable": 3,
    "same-source": 3,
    "same-target": 3,
    "distant": 6,
}

for kind in sorted(counts):
    print(f"{kind}: {counts[kind]}")
print("all 19 nonidentical root positions classified")
