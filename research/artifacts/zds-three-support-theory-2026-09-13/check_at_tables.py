#!/usr/bin/env python3
"""Cross-check Abdollahi--Taheri Table tab-C4 starred relators and their
trefoil substitutions (arXiv:1612.00934, Thm C4) in the free group F(h2,h3)."""
from cycle_relators import cred, inv, canon, relator, tuples, tuple_class, classify

H2, H3 = 1, 2
def w(*letters):
    return cred(list(letters))
def p(word, k):
    return cred(word * k) if k > 0 else cred(inv(word) * (-k))
def cat(*ws):
    out = []
    for x in ws:
        out.extend(x)
    return cred(out)

h2, h3 = [H2], [H3]
ih2, ih3 = [-H2], [-H3]
# starred relators of Table tab-C4 and the substitutions (x, y) of Thm C4
rel = {
 5:  (cat(h2, h2, h3, ih2, h3), (cat(ih2, h3), ih2)),
 7:  (cat(h2, h2, ih3, ih3, h2), (h3, h2)),
 14: (cat(h2, h3, ih2, ih2, h3), (cat(h2, h3), h2)),
 17: (cat(h2, h3, ih2, h3, ih2, h3), (ih2, cat(h3, ih2))),
 26: (cat(h2, ih3, h2, h3, ih2, h3), (cat(h2, ih3, h2), cat(ih3, h2))),
}
swap = lambda u: [(2 if abs(c) == 1 else 1) * (1 if c > 0 else -1) for c in u]
rel[21] = (swap(rel[7][0]), (swap(rel[7][1][0]), swap(rel[7][1][1])))
rel[22] = (swap(rel[14][0]), (swap(rel[14][1][0]), swap(rel[14][1][1])))
rel[25] = (swap(rel[5][0]), (swap(rel[5][1][0]), swap(rel[5][1][1])))
rel[29] = (swap(rel[17][0]), (swap(rel[17][1][0]), swap(rel[17][1][1])))

def cyclic_forms(u):
    u = cred(u)
    forms = set()
    for v in (u, inv(u)):
        for s in range(len(v)):
            forms.add(tuple(v[s:] + v[:s]))
    return forms

ok = True
for n in sorted(rel):
    r, (x, y) = rel[n]
    t = cat(x, x, inv(y), inv(y), inv(y))   # x^2 y^-3
    same = bool(cyclic_forms(r) & cyclic_forms(t))
    print("relation %d: r=%s x^2y^-3=%s conjugate_or_inverse=%s type=%s" % (n, r, t, same, classify(r)[0]))
    ok &= same
# every starred C4 class of the census is one of these nine, and conversely
census = {}
for T in tuples(4):
    c = tuple_class(T)
    census[c] = relator(list(c))
starred = {c: r for c, r in census.items() if classify(r)[0] == "C"}
matched = set()
for c, r in starred.items():
    hits = [n for n in rel if cyclic_forms(r) & cyclic_forms(rel[n][0])]
    print("census class", list(c), "relator", r, "matches A-T", hits)
    ok &= len(hits) == 1
    matched.update(hits)
print("all nine matched:", matched == set(rel), "ALLOK", ok and matched == set(rel))
