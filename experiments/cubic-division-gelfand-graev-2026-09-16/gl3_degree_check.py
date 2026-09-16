# Consistency check of the imported GL_3(F_q) degree list (Steinberg 1951; import, not re-read).
# Families: (count, degree, generic?).  Checks: class number q^3 - q, sum of squares |GL_3|,
# generic count q^3 - q^2, generic degree sum |GL_3|/|U| = (q-1)(q^2-1)(q^3-1).
def fams(q):
    return [(q-1, 1, False), (q-1, q*q+q, False), ((q-1)*(q-2), q*q+q+1, False),
            (q-1, q**3, True), ((q-1)*(q-2), q*(q*q+q+1), True),
            ((q-1)*(q-2)*(q-3)//6, (q+1)*(q*q+q+1), True),
            (q*(q-1)**2//2, (q-1)*(q*q+q+1), True), ((q**3-q)//3, (q-1)**2*(q+1), True)]
ok = True
for q in [2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 37, 41, 43, 47]:
    F = fams(q); order = (q**3-1)*(q**3-q)*(q**3-q*q)
    c = sum(n for n, d, g in F); s2 = sum(n*d*d for n, d, g in F)
    gc = sum(n for n, d, g in F if g); gd = sum(n*d for n, d, g in F if g)
    good = (c == q**3-q and s2 == order and gc == q**3-q*q and gd == (q-1)*(q*q-1)*(q**3-1)
            and sum(n for n, d, g in F if not g) == q*(q-1))
    ok &= good
    print(q, c, s2 == order, gc, gd == (q-1)*(q*q-1)*(q**3-1), "ok" if good else "FAIL")
print("ALL OK" if ok else "SOME FAIL")
