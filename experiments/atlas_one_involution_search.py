"""Joint atlas/one-involution signal search in the natural A8 action.

This is a finite red-team experiment for the current FALSE endpoint.  Two
copies of GL(4,2) ~= A8 act through the natural eight-point permutation
representation, with relative position U.  A fixed diagonal involution T is
chosen so a distinguished transvection S satisfies S T S* = -T exactly.

The two measured losses are:

* the 648 necessary two-chart atlas centrality constraints; and
* commutation of the conjugates pi(g) T pi(g)* over the identity and the
  twelve chart generators.

Only normalized Hilbert--Schmidt defects are tested.  The atlas subsystem is
necessary but incomplete, and the conjugate window is finite, so a small
score is a structure-discovery signal rather than a proof certificate.
"""

import argparse
import json
import time
from pathlib import Path

import numpy as np

import atlas_two_chart_search as atlas


HERE = Path(__file__).resolve().parent
BEST_INNER_ALIGNMENT = np.array(
    [[0, 0, 0, 1],
     [0, 1, 0, 0],
     [0, 0, 1, 0],
     [1, 0, 0, 0]], dtype=np.uint8)


def permutation_matrix(images):
    size = len(images)
    matrix = np.zeros((size, size), dtype=np.complex128)
    for source, target in enumerate(images):
        matrix[target - 1, source] = 1.0
    return matrix


def matrix_hex(matrix):
    return atlas.matrix_key(matrix).hex()


def make_antipodal_involution(permutation):
    size = permutation.shape[0]
    images = np.argmax(permutation, axis=0)
    signs = np.zeros(size, dtype=np.float64)
    seen = set()
    for point in range(size):
        if point in seen:
            continue
        partner = int(images[point])
        if partner == point or int(images[partner]) != point:
            raise ValueError("distinguished element is not fixed-point-free order two")
        signs[point], signs[partner] = 1.0, -1.0
        seen.update((point, partner))
    involution = np.diag(signs.astype(np.complex128))
    error = np.linalg.norm(permutation @ involution @ permutation.conj().T +
                           involution)
    if error > 1e-12:
        raise AssertionError("failed exact antipodal construction")
    return involution


def conjugate_involution(word):
    return list(word) + [(0, None)] + atlas.inverse(word)


class JointProblem:
    def __init__(self, k, map_path, operator_diagnostics=False):
        self.k = k
        self.n = 8 * k
        self.operator_diagnostics = operator_diagnostics
        with open(map_path, "r", encoding="utf-8") as stream:
            raw_map = json.load(stream)["matrices"]
        base_reps = {key: permutation_matrix(images)
                     for key, images in raw_map.items()}

        relation_names, relations = atlas.relation_family()
        atlas.validate_relation_words(relation_names, relations)
        self.atlas_words = []
        self.atlas_names = []
        for relation_name, relation in zip(relation_names, relations):
            for generator_name, generator in atlas.factor_generators():
                word = atlas.commutator(generator, relation)
                if word:
                    self.atlas_words.append(word)
                    self.atlas_names.append("[%s,%s]" %
                                            (generator_name, relation_name))

        window = [("1", [])] + atlas.factor_generators()
        conjugates = [(name, conjugate_involution(word))
                      for name, word in window]
        self.orbit_words = []
        self.orbit_names = []
        for left in range(len(conjugates)):
            for right in range(left + 1, len(conjugates)):
                left_name, left_word = conjugates[left]
                right_name, right_word = conjugates[right]
                self.orbit_words.append(
                    left_word + right_word + left_word + right_word)
                self.orbit_names.append("[T_%s,T_%s]" %
                                        (left_name, right_name))

        distinct = {}
        for word in self.atlas_words + self.orbit_words:
            for factor, matrix in word:
                if factor:
                    distinct.setdefault(matrix_hex(matrix), matrix)
        missing = sorted(set(distinct) - set(base_reps))
        if missing:
            raise ValueError("A8 map omits %d matrices" % len(missing))
        eye_k = np.eye(k, dtype=np.complex128)
        self.reps = {key: np.kron(base_reps[key], eye_k)
                     for key in distinct}
        self.inner_seed = np.kron(
            base_reps[matrix_hex(BEST_INNER_ALIGNMENT)], eye_k)

        distinguished = atlas.transvection(0, 1)
        base_t = make_antipodal_involution(base_reps[matrix_hex(distinguished)])
        self.t = np.kron(base_t, eye_k)
        self.s = self.reps[matrix_hex(distinguished)]
        self.antipodal_defect = float(
            np.linalg.norm(self.s @ self.t @ self.s.conj().T + self.t) /
            np.sqrt(self.n))

    def factors(self, word, unitary):
        answer = []
        adjoint = unitary.conj().T
        for factor, matrix in word:
            if factor == 0:
                answer.append(self.t)
            else:
                rep = self.reps[matrix_hex(matrix)]
                answer.append(rep if factor == 1 else
                              unitary @ rep @ adjoint)
        return answer

    def trace_and_gradient(self, word, unitary, need_gradient):
        factors = self.factors(word, unitary)
        length = len(factors)
        prefix = [np.eye(self.n, dtype=np.complex128)]
        for factor in factors:
            prefix.append(prefix[-1] @ factor)
        trace = float(np.trace(prefix[-1]).real / self.n)
        if not need_gradient:
            return trace, None
        suffix = [None] * (length + 1)
        suffix[length] = np.eye(self.n, dtype=np.complex128)
        for position in range(length - 1, -1, -1):
            suffix[position] = factors[position] @ suffix[position + 1]
        gradient = np.zeros((self.n, self.n), dtype=np.complex128)
        for position, (chart, _) in enumerate(word):
            if chart == 2:
                current = factors[position]
                rest = suffix[position + 1] @ prefix[position]
                gradient += current @ rest - rest @ current
        return trace, gradient / self.n

    def family_score(self, words, unitary, indices, need_gradient):
        if indices is None:
            indices = range(len(words))
        total = 0.0
        gradient = (np.zeros((self.n, self.n), dtype=np.complex128)
                    if need_gradient else None)
        count = 0
        for index in indices:
            trace, word_gradient = self.trace_and_gradient(
                words[int(index)], unitary, need_gradient)
            total += trace
            if need_gradient:
                gradient += word_gradient
            count += 1
        return total / count, (gradient / count if need_gradient else None)

    def score(self, unitary, atlas_weight, atlas_indices=None,
              orbit_indices=None, need_gradient=False):
        atlas_score, atlas_gradient = self.family_score(
            self.atlas_words, unitary, atlas_indices, need_gradient)
        orbit_score, orbit_gradient = self.family_score(
            self.orbit_words, unitary, orbit_indices, need_gradient)
        score = atlas_weight * atlas_score + (1.0 - atlas_weight) * orbit_score
        if not need_gradient:
            return score, None
        gradient = (atlas_weight * atlas_gradient +
                    (1.0 - atlas_weight) * orbit_gradient)
        return score, gradient

    def family_diagnostics(self, words, names, unitary):
        traces = np.array([self.trace_and_gradient(word, unitary, False)[0]
                           for word in words])
        defects = np.sqrt(np.maximum(0.0, 2.0 - 2.0 * traces))
        worst = np.argsort(defects)[-5:][::-1]
        return {
            "rms_defect": float(np.sqrt(np.mean(defects ** 2))),
            "max_defect": float(defects.max()),
            "worst": [(names[int(index)], float(defects[int(index)]))
                      for index in worst],
        }

    def max_operator_defect(self, words, unitary):
        identity = np.eye(self.n, dtype=np.complex128)
        maximum = 0.0
        for word in words:
            product = identity
            for factor in self.factors(word, unitary):
                product = product @ factor
            maximum = max(maximum,
                          float(np.linalg.norm(product - identity, ord=2)))
        return maximum

    def diagnostics(self, unitary):
        diagnostics = {
            "atlas": self.family_diagnostics(
                self.atlas_words, self.atlas_names, unitary),
            "orbit": self.family_diagnostics(
                self.orbit_words, self.orbit_names, unitary),
            "antipodal_defect": self.antipodal_defect,
            "inner_seed_distance": float(
                np.linalg.norm(unitary - self.inner_seed) / np.sqrt(self.n)),
        }
        if self.operator_diagnostics:
            diagnostics["operator_max_defect"] = {
                "atlas": self.max_operator_defect(self.atlas_words, unitary),
                "orbit": self.max_operator_defect(self.orbit_words, unitary),
                "antipodal": float(np.linalg.norm(
                    self.s @ self.t @ self.s.conj().T + self.t, ord=2)),
            }
        return diagnostics


def cayley_left(unitary, tangent, step):
    identity = np.eye(unitary.shape[0], dtype=np.complex128)
    half = 0.5 * step * tangent
    return np.linalg.solve(identity - half, (identity + half) @ unitary)


def haar_unitary(size, rng):
    matrix = (rng.standard_normal((size, size)) +
              1j * rng.standard_normal((size, size)))
    qmat, rmat = np.linalg.qr(matrix)
    phases = np.diag(rmat).copy()
    phases /= np.where(np.abs(phases) == 0, 1.0, np.abs(phases))
    return qmat @ np.diag(phases.conj())


def initial_unitary(problem, start, seed, path):
    rng = np.random.default_rng(seed)
    if path:
        initial = np.load(path)
        initial_k = initial.shape[0] // 8
        if (initial.ndim != 2 or initial.shape[0] != initial.shape[1] or
                initial.shape[0] % 8 or problem.k % initial_k):
            raise ValueError("incompatible initial unitary")
        return np.kron(initial, np.eye(problem.k // initial_k,
                                      dtype=np.complex128))
    if start == "identity":
        unitary = np.eye(problem.n, dtype=np.complex128)
        if seed != 1729:
            noise = (rng.standard_normal((problem.n, problem.n)) +
                     1j * rng.standard_normal((problem.n, problem.n)))
            tangent = 0.5 * (noise - noise.conj().T) / np.sqrt(problem.n)
            unitary = cayley_left(unitary, tangent, 1e-3)
        return unitary
    if start == "inner":
        unitary = problem.inner_seed.copy()
        if seed != 1729:
            noise = (rng.standard_normal((problem.n, problem.n)) +
                     1j * rng.standard_normal((problem.n, problem.n)))
            tangent = 0.5 * (noise - noise.conj().T) / np.sqrt(problem.n)
            unitary = cayley_left(unitary, tangent, 1e-3)
        return unitary
    return haar_unitary(problem.n, rng)


def optimize(problem, atlas_weight, seed, iterations, atlas_batch,
             orbit_batch, report_every, start, initial_path):
    rng = np.random.default_rng(seed)
    unitary = initial_unitary(problem, start, seed, initial_path)
    best = unitary.copy()
    best_score, _ = problem.score(unitary, atlas_weight)
    best_diagnostics = problem.diagnostics(unitary)
    started = time.time()
    print(json.dumps({"event": "start", "seed": seed, "k": problem.k,
                      "dimension": problem.n, "atlas_weight": atlas_weight,
                      "atlas_constraints": len(problem.atlas_words),
                      "orbit_constraints": len(problem.orbit_words),
                      **best_diagnostics}), flush=True)
    for iteration in range(1, iterations + 1):
        atlas_size = min(atlas_batch, len(problem.atlas_words))
        orbit_size = min(orbit_batch, len(problem.orbit_words))
        atlas_indices = rng.choice(len(problem.atlas_words), atlas_size,
                                   replace=False)
        orbit_indices = rng.choice(len(problem.orbit_words), orbit_size,
                                   replace=False)
        old_score, gradient = problem.score(
            unitary, atlas_weight, atlas_indices, orbit_indices, True)
        skew = 0.5 * (gradient - gradient.conj().T)
        direction = -skew
        accepted = False
        for step in (3.0, 1.0, 0.3, 0.1, 0.03, 0.01):
            candidate = cayley_left(unitary, direction, step)
            new_score, _ = problem.score(
                candidate, atlas_weight, atlas_indices, orbit_indices, False)
            if new_score > old_score + 1e-12:
                unitary = candidate
                accepted = True
                break
        if not accepted:
            noise = (rng.standard_normal((problem.n, problem.n)) +
                     1j * rng.standard_normal((problem.n, problem.n)))
            kick = 0.5 * (noise - noise.conj().T) / np.sqrt(problem.n)
            unitary = cayley_left(unitary, kick, 1e-4)
        if iteration % report_every == 0 or iteration == iterations:
            full_score, _ = problem.score(unitary, atlas_weight)
            diagnostics = problem.diagnostics(unitary)
            if full_score > best_score:
                best_score = full_score
                best = unitary.copy()
                best_diagnostics = diagnostics
            print(json.dumps({"event": "progress", "seed": seed,
                              "iteration": iteration,
                              "elapsed_s": round(time.time() - started, 3),
                              "objective": full_score,
                              **diagnostics}), flush=True)
    return best, best_score, best_diagnostics


def check_gradient(problem, seed):
    rng = np.random.default_rng(seed)
    unitary = haar_unitary(problem.n, rng)
    noise = (rng.standard_normal((problem.n, problem.n)) +
             1j * rng.standard_normal((problem.n, problem.n)))
    tangent = 0.5 * (noise - noise.conj().T) / np.sqrt(problem.n)
    _, gradient = problem.score(unitary, 0.5, need_gradient=True)
    predicted = float(np.trace(gradient @ tangent).real)
    errors = []
    for step in (1e-3, 3e-4, 1e-4):
        plus, _ = problem.score(cayley_left(unitary, tangent, step), 0.5)
        minus, _ = problem.score(cayley_left(unitary, tangent, -step), 0.5)
        observed = (plus - minus) / (2.0 * step)
        errors.append({"step": step, "predicted": predicted,
                       "observed": observed,
                       "absolute_error": abs(predicted - observed)})
    print(json.dumps({"event": "gradient_check", "errors": errors}))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=1)
    parser.add_argument("--atlas-weight", type=float, default=0.5)
    parser.add_argument("--iters", type=int, default=100)
    parser.add_argument("--seeds", type=int, default=2)
    parser.add_argument("--atlas-batch", type=int, default=24)
    parser.add_argument("--orbit-batch", type=int, default=16)
    parser.add_argument("--report-every", type=int, default=20)
    parser.add_argument("--start", choices=("identity", "inner", "haar"),
                        default="identity")
    parser.add_argument("--init")
    parser.add_argument("--save")
    parser.add_argument("--map", default=str(HERE / "atlas-a8-natural.json"))
    parser.add_argument("--check-gradient", action="store_true")
    parser.add_argument("--operator-diagnostics", action="store_true")
    args = parser.parse_args()
    if not 0.0 <= args.atlas_weight <= 1.0:
        raise ValueError("atlas weight must lie in [0,1]")
    problem = JointProblem(args.k, args.map, args.operator_diagnostics)
    if args.check_gradient:
        check_gradient(problem, 1729)
        return
    results = []
    for offset in range(args.seeds):
        results.append(optimize(
            problem, args.atlas_weight, 1729 + offset, args.iters,
            args.atlas_batch, args.orbit_batch, args.report_every,
            args.start, args.init))
    best_unitary, objective, diagnostics = max(results, key=lambda item: item[1])
    if args.save:
        np.save(args.save, best_unitary)
    print(json.dumps({"event": "final", "k": args.k,
                      "dimension": problem.n,
                      "atlas_weight": args.atlas_weight,
                      "objective": objective,
                      **diagnostics}), flush=True)


if __name__ == "__main__":
    main()
