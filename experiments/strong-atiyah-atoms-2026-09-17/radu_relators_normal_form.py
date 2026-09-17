# Normal forms in Radu's BMW lattice Gamma_R = <a,b,c,x,y,z | squares, axax, ayay, azbz, bxbx, bycy, cxcz>.
# Every element is uniquely (reduced V-word)(reduced A-word); the square relations give h*v = v'*h'.
# Check that F1 = b a and F2 = y x satisfy the two relators of pi_1(S_R) found by GAP (radu_index4_kernel.g).
swap = {}  # (h, v) -> (v', h')  meaning h v = v' h'
for sq in ["axax", "ayay", "azbz", "bxbx", "bycy", "cxcz"]:
    h1, v1, h2, v2 = sq   # h1 v1 h2 v2 = 1  =>  h1 v1 = v2 h2 (all involutions)
    swap[(h1, v1)] = (v2, h2)
    swap[(h2, v2)] = (v1, h1)
    # inverse relator v2 h2 v1 h1 = 1 gives h2 v1 = v2 h1 and h1 v2 = v1 h2
    swap[(h2, v1)] = (v2, h1)
    swap[(h1, v2)] = (v1, h2)
assert len(swap) == 9, sorted(swap)
def push(word):
    V, A = [], []
    for s in word:
        if s in "abc":
            if A and A[-1] == s: A.pop()
            else: A.append(s)
        else:
            v = s; newA = []
            for h in reversed(A):
                v, h2 = swap[(h, v)]
                newA.append(h2)
            A = list(reversed(newA))
            if V and V[-1] == v: V.pop()
            else: V.append(v)
    return "".join(V), "".join(A)
inv = lambda w: w[::-1]            # all letters are involutions
F1, F2 = "ba", "yx"
I1, I2 = inv(F1), inv(F2)
def W(*parts): return "".join(parts)
r1 = W(F2, I1, I2, I2, F1, F1, F2, F2, I1, I2, F1)
r2 = W(F1, I2, I2, I1, F2, F1, I2, I1, F2, F2, F1)
print("relator checks", push(r1), push(r2), "(empty pairs mean identity)")
print("F1 normal form", push(F1), " F2 normal form", push(F2))
# consistency: the defining relators themselves reduce to the identity
for rel in ["aa", "axax", "ayay", "azbz", "bxbx", "bycy", "cxcz"]:
    assert push(rel) == ("", ""), rel
print("defining relators reduce to identity")
