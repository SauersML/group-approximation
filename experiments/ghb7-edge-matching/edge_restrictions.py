#!/usr/bin/env python3
"""Edge restrictions of every irreducible representation of the GHB_2(7) vertex groups.

Vertex groups via the CCKW quotient psi into SL_4(F_7) (injective on vertex groups):
  a -> I + E_03 + E_12,  b -> I + E_10 - E_23,  c -> I + E_31.
For a vertex group X = <x,y> (x, y the edge generators) we:
  1. find an abelian normal subgroup A of index 7 (A = <x, [x,y], [x,y,y]> closed up; checked);
  2. fix a basis of A = (Z/7)^r and the conjugation action of y on A as an r x r matrix over F_7;
  3. list characters psi of A (vectors in F_7^r), orbits under y;
  4. orbit of size 7  -> one irreducible Ind_A^X psi of degree 7;
     orbit of size 1  -> 7 linear characters extending psi (eigenvalue of y free);
  5. eigenvalue multiset of x in Ind psi: {psi^{y^t}(x) : t = 0..6}; y acts by a 7-cycle on cosets,
     so y is regular in every degree-7 irreducible.
Cross-checks: number of irreducibles = number of conjugacy classes; sum of squares = |X|;
column orthogonality sum_chi |chi(x^j)|^2 = |C_X(x^j)| for j = 1..6.
"""
import itertools, json, cmath
P, N = 7, 4
def E(i, j, s=1):
    return tuple(tuple((s % P if (r, cc) == (i, j) else 0) for cc in range(N)) for r in range(N))
def add(A, B):
    return tuple(tuple((A[r][cc] + B[r][cc]) % P for cc in range(N)) for r in range(N))
def mul(A, B):
    return tuple(tuple(sum(A[r][k] * B[k][cc] for k in range(N)) % P for cc in range(N)) for r in range(N))
I4 = tuple(tuple(1 if i == j else 0 for j in range(N)) for i in range(N))
gen = {"a": add(add(I4, E(0, 3)), E(1, 2)), "b": add(add(I4, E(1, 0)), E(2, 3, -1)), "c": add(I4, E(3, 1))}
def closure(gs):
    seen = {I4}; fr = [I4]
    while fr:
        nw = []
        for g in fr:
            for s in gs:
                h = mul(g, s)
                if h not in seen:
                    seen.add(h); nw.append(h)
        fr = nw
    return seen
def power(g, n):
    r = I4
    for _ in range(n % P):
        r = mul(r, g)
    return r
def inv(g):
    return power(g, P - 1)  # all elements here have exponent 7
def comm(x, y):
    return mul(mul(inv(x), inv(y)), mul(x, y))

def analyze(name, xn, yn):
    x, y = gen[xn], gen[yn]
    X = closure([x, y])
    assert all(power(g, P) == I4 for g in X), "exponent 7 check failed"
    # A := centralizer of x, required abelian of index 7 (normal since index p in a p-group)
    A = {g for g in X if mul(g, x) == mul(x, g)}
    assert len(X) == 7 * len(A), (name, "centralizer index", len(X) // len(A))
    assert all(mul(g, h) == mul(h, g) for g in A for h in A), (name, "centralizer not abelian")
    assert all(mul(mul(y, g), inv(y)) in A for g in A), (name, "centralizer not normal")
    assert y not in A
    basis = [x]
    while len(closure(basis)) < len(A):
        cur = closure(basis)
        basis.append(next(g for g in sorted(A) if g not in cur))
    r = len(basis)
    assert len(A) == P ** r, (name, len(A), r)
    coord = {}
    for v in itertools.product(range(P), repeat=r):
        g = I4
        for k in range(r):
            g = mul(g, power(basis[k], v[k]))
        coord[g] = v
    assert len(coord) == len(A)
    # conjugation g -> y^{-1} g y on A as matrix M with coord(y^-1 e_k y) = column k
    M = [coord[mul(mul(inv(y), basis[k]), y)] for k in range(r)]
    def act(psi):  # psi^y(g) := psi(y^{-1} g y); psi as vector, psi(g)=zeta^{<psi,coord g>}
        return tuple(sum(psi[j] * M[k][j] for j in range(r)) % P for k in range(r))
    seen = set(); irreps = []; linear = 0
    for psi in itertools.product(range(P), repeat=r):
        if psi in seen:
            continue
        orb = [psi]
        while True:
            nxt = act(orb[-1])
            if nxt == psi:
                break
            orb.append(nxt)
        seen.update(orb)
        if len(orb) == 1:
            linear += P
        else:
            assert len(orb) == P
            # eigenvalue exponents of x = e1 (coord (1,0,..)) : psi^{y^t}(e1) = zeta^{psi_t[0]}
            exps = [o[0] for o in orb]
            mult = [exps.count(k) for k in range(P)]
            # central character data: exponent of psi on e_r (e3 or e2)
            irreps.append({"x_multiplicities": mult, "orbit_rep": list(psi)})
    nclasses = 0; rem = set(X)
    while rem:
        g = rem.pop(); rem -= {mul(mul(h, g), inv(h)) for h in X}; nclasses += 1
    patterns = {}
    for ir in irreps:
        key = tuple(sorted(ir["x_multiplicities"], reverse=True))
        patterns[str(key)] = patterns.get(str(key), 0) + 1
    zeta = cmath.exp(2j * cmath.pi / P)
    colsum = []
    for j in range(1, P):
        s = linear * 1.0
        for ir in irreps:
            chi = sum(m * zeta ** (k * j) for k, m in enumerate(ir["x_multiplicities"]))
            s += abs(chi) ** 2
        cent = sum(1 for h in X if mul(h, power(x, j)) == mul(power(x, j), h))
        colsum.append([round(s, 6), cent])
    return {"vertex": name, "x": xn, "y": yn, "order": len(X), "abelian_normal_rank": r,
            "linear_characters": linear, "degree7_irreducibles": len(irreps),
            "classes": nclasses, "irreducible_count_ok": linear + len(irreps) == nclasses,
            "sum_of_squares_ok": linear + 49 * len(irreps) == len(X),
            "x_multiplicity_patterns_in_degree7": patterns,
            "column_orthogonality_x_powers": colsum,
            "y_regular_in_degree7": True}

out = [analyze("X_0=<a,b>", "a", "b"), analyze("X_0=<a,b>", "b", "a"),
       analyze("X_1=<c,b>", "c", "b"), analyze("X_2=<c,a>", "c", "a")]
print(json.dumps(out, indent=1))
print("DONE")
