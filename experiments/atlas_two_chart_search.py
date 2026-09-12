"""Two-chart A8 search for necessary Leavitt-atlas centrality constraints.

This is a signal experiment, not a proof endpoint.  The two copies of A8 are
represented on the 15 nonzero vectors of F_2^4.  Their relative position is a
unitary U in U(15 k).  We translate a finite family of Steinberg/Leavitt
relations through the explicit K1*K2 atlas from EXPLICIT_LEAVITT_ATLAS.md.
For every relation word r and a generating transvection p of either chart,
[p,r] belongs to [P,R], so a hyperlinear atlas model must make all the tested
commutators small in normalized Hilbert--Schmidt norm.

The optimizer maximizes their mean real normalized trace on U(15 k) using the
exact cyclic gradient and Cayley retractions.  It deliberately uses only
NumPy so it runs in the existing MSI environment without installing anything.
"""

import argparse
import itertools
import json
import time

import numpy as np


COEFFS = ("1", "e", "f", "E", "F")
GAMMA = {1: "00", 2: "01", 3: "1"}
CHART_LEAVES = {
    1: ("01", "1", "000", "001"),
    2: ("00", "1", "010", "011"),
}
I4 = np.eye(4, dtype=np.uint8)


def gf2_mul(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    return (a @ b) & 1


def gf2_inv(a: np.ndarray) -> np.ndarray:
    aug = np.concatenate((a.copy(), I4.copy()), axis=1)
    for col in range(4):
        pivots = np.flatnonzero(aug[col:, col])
        if len(pivots) == 0:
            raise ValueError("singular F2 matrix")
        pivot = col + int(pivots[0])
        if pivot != col:
            aug[[col, pivot]] = aug[[pivot, col]]
        for row in range(4):
            if row != col and aug[row, col]:
                aug[row] ^= aug[col]
    return aug[:, 4:]


def transvection(row: int, col: int) -> np.ndarray:
    g = I4.copy()
    g[row, col] ^= 1
    return g


# A word is a list of (free-factor, element of GL_4(F_2)).
def reduce_word(word):
    out = []
    for factor, g in word:
        if np.array_equal(g, I4):
            continue
        if out and out[-1][0] == factor:
            h = gf2_mul(out[-1][1], g)
            out.pop()
            if not np.array_equal(h, I4):
                out.append((factor, h))
        else:
            out.append((factor, g))
    return out


def product(*words):
    joined = []
    for word in words:
        joined.extend(word)
    return reduce_word(joined)


def inverse(word):
    return [(factor, gf2_inv(g)) for factor, g in reversed(word)]


def commutator(x, y):
    return product(x, y, inverse(x), inverse(y))


def direct_q(i: int, j: int, a: str):
    if a == "1":
        chart = 6 - i - j
        alpha, beta = GAMMA[i], GAMMA[j]
    elif a in ("e", "f"):
        chart = i
        alpha = GAMMA[i] + ("0" if a == "e" else "1")
        beta = GAMMA[j]
    else:
        chart = j
        alpha = GAMMA[i]
        beta = GAMMA[j] + ("0" if a == "E" else "1")
    if chart not in (1, 2):
        return None
    leaves = CHART_LEAVES[chart]
    return [(chart, transvection(leaves.index(alpha), leaves.index(beta)))]


def q(i: int, j: int, a: str):
    direct = direct_q(i, j, a)
    if direct is not None:
        return direct
    # The six identities (7) express precisely the ten K3 generators.
    if i == 3 and j == 1 and a in ("e", "f"):
        return commutator(q(3, 2, "1"), q(2, 1, a))
    if i == 3 and j == 2 and a in ("e", "f"):
        return commutator(q(3, 1, "1"), q(1, 2, a))
    if i == 1 and j == 3 and a in ("E", "F"):
        return commutator(q(1, 2, a), q(2, 3, "1"))
    if i == 2 and j == 3 and a in ("E", "F"):
        return commutator(q(2, 1, a), q(1, 3, "1"))
    if (i, j, a) == (1, 2, "1"):
        return commutator(q(1, 3, "1"), q(3, 2, "1"))
    if (i, j, a) == (2, 1, "1"):
        return commutator(q(2, 3, "1"), q(3, 1, "1"))
    raise ValueError("unhandled K3 generator: %s" % ((i, j, a),))


def relation_family():
    rels = []
    names = []

    def add(name, word):
        word = reduce_word(word)
        if word:
            names.append(name)
            rels.append(word)

    # Steinberg multiplication with one scalar coefficient.
    for i, j, k in itertools.permutations((1, 2, 3)):
        for a in COEFFS:
            add("stL_%d%d%d_%s" % (i, j, k, a),
                product(commutator(q(i, j, a), q(j, k, "1")),
                        inverse(q(i, k, a))))
            add("stR_%d%d%d_%s" % (i, j, k, a),
                product(commutator(q(i, j, "1"), q(j, k, a)),
                        inverse(q(i, k, a))))

        # e*e=f*f=1 and the two zero cross-products.
        for left, right, out in (("E", "e", "1"), ("F", "f", "1")):
            add("cuntz_%d%d%d_%s%s" % (i, j, k, left, right),
                product(commutator(q(i, j, left), q(j, k, right)),
                        inverse(q(i, k, out))))
        for left, right in (("E", "f"), ("F", "e")):
            add("zero_%d%d%d_%s%s" % (i, j, k, left, right),
                commutator(q(i, j, left), q(j, k, right)))

        # ee* + ff* = 1 in characteristic two.
        add("partition_%d%d%d" % (i, j, k),
            product(commutator(q(i, j, "e"), q(j, k, "E")),
                    commutator(q(i, j, "f"), q(j, k, "F")),
                    inverse(q(i, k, "1"))))

    # Root commutation for a compact but representative coefficient set.
    roots = [(i, j) for i in (1, 2, 3) for j in (1, 2, 3) if i != j]
    for (i, j), (k, ell) in itertools.combinations(roots, 2):
        if i != ell and j != k:
            for a, b in (("1", "1"), ("e", "f"), ("E", "F")):
                add("orth_%d%d_%d%d_%s%s" % (i, j, k, ell, a, b),
                    commutator(q(i, j, a), q(k, ell, b)))

    # Deduplicate exact free-product words.
    unique = {}
    for name, word in zip(names, rels):
        key = tuple((f, bytes(g.reshape(-1))) for f, g in word)
        unique.setdefault(key, (name, word))
    pairs = list(unique.values())
    return [p[0] for p in pairs], [p[1] for p in pairs]


def factor_generators():
    out = []
    for factor in (1, 2):
        for row, col in ((0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2)):
            out.append(("p%d_%d%d" % (factor, row, col),
                        [(factor, transvection(row, col))]))
    return out


def permutation_rep(g: np.ndarray) -> np.ndarray:
    vectors = [np.array(bits, dtype=np.uint8)
               for bits in itertools.product((0, 1), repeat=4)
               if any(bits)]
    index = {tuple(v.tolist()): i for i, v in enumerate(vectors)}
    p = np.zeros((15, 15), dtype=np.complex128)
    for col, v in enumerate(vectors):
        image = (g @ v) & 1
        p[index[tuple(image.tolist())], col] = 1.0
    return p


def matrix_key(g):
    return bytes(g.reshape(-1))


def leavitt_add(x, y):
    out = dict(x)
    for monomial in y:
        if monomial in out:
            del out[monomial]
        else:
            out[monomial] = 1
    return out


def leavitt_mul(x, y):
    out = {}
    for a, b in x:
        for c, d in y:
            if len(b) <= len(c) and c[:len(b)] == b:
                monomial = (a + c[len(b):], d)
            elif len(c) < len(b) and b[:len(c)] == c:
                monomial = (a, d + b[len(c):])
            else:
                continue
            if monomial in out:
                del out[monomial]
            else:
                out[monomial] = 1
    return out


def leavitt_chart_element(factor, g):
    leaves = CHART_LEAVES[factor]
    out = {}
    for row in range(4):
        for col in range(4):
            if g[row, col]:
                out[(tuple(map(int, leaves[row])),
                     tuple(map(int, leaves[col])))] = 1
    return out


def leavitt_is_one(x):
    # Expand every homogeneous degree to a common right-word depth.  The
    # identity expansion is inserted in degree zero, so exact equality to one
    # is equivalent to cancellation of every expanded monomial.
    delta = leavitt_add(x, {((), ()): 1})
    by_degree = {}
    for a, b in delta:
        by_degree.setdefault(len(a) - len(b), []).append((a, b))
    for terms in by_degree.values():
        depth = max(len(b) for _, b in terms)
        expanded = set()
        for a, b in terms:
            extra = depth - len(b)
            for suffix in itertools.product((0, 1), repeat=extra):
                monomial = (a + suffix, b + suffix)
                if monomial in expanded:
                    expanded.remove(monomial)
                else:
                    expanded.add(monomial)
        if expanded:
            return False
    return True


def validate_relation_words(names, words):
    one = {((), ()): 1}
    for name, word in zip(names, words):
        value = one
        for factor, g in word:
            value = leavitt_mul(value, leavitt_chart_element(factor, g))
        if not leavitt_is_one(value):
            raise AssertionError("word is not a Leavitt relation: %s" % name)


class Problem:
    def __init__(self, k: int):
        self.k = k
        self.n = 15 * k
        rel_names, rels = relation_family()
        validate_relation_words(rel_names, rels)
        constraints = []
        constraint_names = []
        for rname, rel in zip(rel_names, rels):
            for pname, p in factor_generators():
                word = commutator(p, rel)
                if word:
                    constraints.append(word)
                    constraint_names.append("[%s,%s]" % (pname, rname))
        self.words = constraints
        self.names = constraint_names
        distinct = {}
        for word in self.words:
            for _, g in word:
                distinct.setdefault(matrix_key(g), g)
        eye_k = np.eye(k, dtype=np.complex128)
        self.reps = {key: np.kron(permutation_rep(g), eye_k)
                     for key, g in distinct.items()}

    def factors(self, word, u):
        ans = []
        uh = u.conj().T
        for factor, g in word:
            a = self.reps[matrix_key(g)]
            ans.append(a if factor == 1 else u @ a @ uh)
        return ans

    def word_trace_and_gradient(self, word, u, need_gradient):
        fs = self.factors(word, u)
        length = len(fs)
        prefix = [np.eye(self.n, dtype=np.complex128)]
        for f in fs:
            prefix.append(prefix[-1] @ f)
        trace = float(np.trace(prefix[-1]).real / self.n)
        if not need_gradient:
            return trace, None
        suffix = [None] * (length + 1)
        suffix[length] = np.eye(self.n, dtype=np.complex128)
        for pos in range(length - 1, -1, -1):
            suffix[pos] = fs[pos] @ suffix[pos + 1]
        grad = np.zeros((self.n, self.n), dtype=np.complex128)
        for pos, (factor, _) in enumerate(word):
            if factor == 2:
                c = fs[pos]
                cyclic_rest = suffix[pos + 1] @ prefix[pos]
                grad += c @ cyclic_rest - cyclic_rest @ c
        return trace, grad

    def score(self, u, indices=None, need_gradient=False):
        if indices is None:
            indices = range(len(self.words))
        total = 0.0
        grad = np.zeros((self.n, self.n), dtype=np.complex128) if need_gradient else None
        count = 0
        for idx in indices:
            value, g = self.word_trace_and_gradient(self.words[idx], u, need_gradient)
            total += value
            if need_gradient:
                grad += g
            count += 1
        return total / count, (grad / (count * self.n) if need_gradient else None)

    def diagnostics(self, u):
        vals = self.traces(u)
        defects = np.sqrt(np.maximum(0.0, 2.0 - 2.0 * vals))
        worst = np.argsort(defects)[-5:][::-1]
        return {
            "mean_trace": float(vals.mean()),
            "rms_defect": float(np.sqrt(np.mean(defects ** 2))),
            "max_defect": float(defects.max()),
            "worst": [(self.names[int(i)], float(defects[int(i)])) for i in worst],
        }

    def traces(self, u):
        return np.array([self.word_trace_and_gradient(w, u, False)[0]
                         for w in self.words])


def haar_unitary(n, rng):
    z = rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))
    qmat, rmat = np.linalg.qr(z)
    phases = np.diag(rmat).copy()
    phases /= np.where(np.abs(phases) == 0, 1.0, np.abs(phases))
    return qmat @ np.diag(phases.conj())


def cayley_left(u, x, step):
    eye = np.eye(u.shape[0], dtype=np.complex128)
    half = 0.5 * step * x
    return np.linalg.solve(eye - half, (eye + half) @ u)


def optimize(problem, seed, iterations, batch_size, report_every, initial=None,
             focus_every=0):
    rng = np.random.default_rng(seed)
    if initial is None:
        # The atlas representation is rho(g) tensor I_k.  Starting from an
        # amplified 15-dimensional unitary respects the direct-sum inequality
        # and makes scores at different k honestly comparable.
        u = np.kron(haar_unitary(15, rng),
                    np.eye(problem.k, dtype=np.complex128))
    else:
        initial_k = initial.shape[0] // 15
        if (initial.shape[0] == initial.shape[1] and
                initial.shape[0] % 15 == 0 and
                problem.k % initial_k == 0):
            u = np.kron(initial, np.eye(problem.k // initial_k,
                                       dtype=np.complex128))
        elif initial.shape == (problem.n, problem.n):
            u = initial.copy()
        else:
            raise ValueError("initial unitary has incompatible shape %r" %
                             (initial.shape,))
        if seed != 1729:
            z = rng.standard_normal((problem.n, problem.n))
            z = z + 1j * rng.standard_normal((problem.n, problem.n))
            kick = 0.5 * (z - z.conj().T) / np.sqrt(problem.n)
            u = cayley_left(u, kick, 1e-2)
    best_u = u.copy()
    best_score, _ = problem.score(u)
    best_diag = problem.diagnostics(u)
    started = time.time()
    print(json.dumps({"event": "start", "seed": seed, "k": problem.k,
                      "dimension": problem.n, "constraints": len(problem.words),
                      **best_diag}), flush=True)
    active = None
    for iteration in range(1, iterations + 1):
        size = min(batch_size, len(problem.words))
        if focus_every and (active is None or (iteration - 1) % focus_every == 0):
            # Small trace means large squared HS defect.  Recompute the active
            # worst tail periodically, then optimize its smooth mean until the
            # next refresh.  This is a deterministic soft-max surrogate.
            active = np.argsort(problem.traces(u))[:size]
        batch = (active if active is not None else
                 rng.choice(len(problem.words), size=size, replace=False))
        old, g = problem.score(u, batch, True)
        skew = 0.5 * (g - g.conj().T)
        direction = -skew
        accepted = False
        for step in (3.0, 1.0, 0.3, 0.1, 0.03, 0.01):
            candidate = cayley_left(u, direction, step)
            new, _ = problem.score(candidate, batch, False)
            if new > old + 1e-12:
                u = candidate
                accepted = True
                break
        if not accepted:
            # A tiny random tangent kick helps leave symmetric stationary loci.
            z = rng.standard_normal((problem.n, problem.n))
            z = z + 1j * rng.standard_normal((problem.n, problem.n))
            kick = 0.5 * (z - z.conj().T) / np.sqrt(problem.n)
            u = cayley_left(u, kick, 1e-3)
        if iteration % report_every == 0 or iteration == iterations:
            full, _ = problem.score(u)
            diag = problem.diagnostics(u)
            improved = (diag["max_defect"] < best_diag["max_defect"]
                        if focus_every else full > best_score)
            if improved:
                best_score, best_u, best_diag = full, u.copy(), diag
            print(json.dumps({"event": "progress", "seed": seed,
                              "iteration": iteration,
                              "elapsed_s": round(time.time() - started, 3),
                              **diag}), flush=True)
    return best_u, best_diag


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=1)
    parser.add_argument("--iters", type=int, default=100)
    parser.add_argument("--seeds", type=int, default=2)
    parser.add_argument("--batch", type=int, default=24)
    parser.add_argument("--report-every", type=int, default=20)
    parser.add_argument("--init", type=str)
    parser.add_argument("--save", type=str)
    parser.add_argument("--focus-every", type=int, default=0)
    args = parser.parse_args()
    problem = Problem(args.k)
    initial = np.load(args.init) if args.init else None
    results = []
    for seed in range(args.seeds):
        unitary, diag = optimize(problem, 1729 + seed, args.iters,
                                 args.batch, args.report_every, initial,
                                 args.focus_every)
        results.append((unitary, diag))
    metric = "max_defect" if args.focus_every else "rms_defect"
    best_u, best = min(results, key=lambda item: item[1][metric])
    if args.save:
        np.save(args.save, best_u)
    print(json.dumps({"event": "final", "k": args.k,
                      "dimension": problem.n, "best": best}), flush=True)


if __name__ == "__main__":
    main()
