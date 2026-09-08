"""Compile and verify the native nine-word Thompson packet without expansion.

Run only on MSI after review. The default command uses the standard library
to verify literal word lengths and exact binary prefix operators. An explicit
--torch-checkpoint adds ONE CPU forward/backward check at dimension 24, with
one thread and no optimization. No search or lower-bound claim is made.

Expression convention: multiplication is written *, inverse ~, and X**Y
means Y^-1 X Y when Y is a word. Integer exponents mean ordinary powers.
gamma(X)=c X c^-1; gamma2(X)=c^-1 X c, using c^3=1 in the marked source.
"""

import argparse
import ast
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re
import time


ARTIFACT = (Path(__file__).resolve().parents[1] / "research/artifacts/"
            "leavitt-explicit-thompson-c-killing-certificate-2026-09-08.md")

# These are source expressions, not Python executed by eval. The parser below
# accepts only names, multiplication, inversion, powers, and the three calls.
DEFINITIONS = (
    ("d", "comm(b_2,gamma(b_1))"),
    ("h", "gamma2(d)"),
    ("a", "comm(d,h)"),
    ("e", "gamma(d)"),
    ("j", "a*e*~a"),
    ("r_star", "j*c*j*c"),
    ("u", "comm(b_2,gamma(b_3))"),
    ("w", "comm(gamma2(b_1),a)"),
    ("p_0", "gamma(b_2)"),
    ("q_0", "w"),
    ("p_1", "comm(e,u)"),
    ("q_1", "comm(gamma2(b_3),b_1)"),
    ("X_0", "p_0*q_0*p_0"),
    ("X_1", "p_1*q_1*p_1"),
    ("A", "j"),
    ("B", "X_0*X_1"),
    ("D", "gamma2(j)"),
    ("rho_1", "A**2"),
    ("rho_2", "B**3"),
    ("rho_3", "(A*B)**4"),
    ("rho_4", "D**(A*D)*~A"),
    ("rho_5", "~D*A**(B*D*A*D*A*A**(B*A))*A**(~B*D*A*D*A*A**(~B*A))"),
    ("rho_6", "comm(A**(~B*D*A*D),A**(~B*D*A*D*A**B*A**(~B*A)))"),
    ("rho_7", "comm(A**(B*D*A*D),A**(~B*D*A*D*A**B*A**(~B*A)))"),
    ("rho_8", "comm(A**(B*D*A**(B*D*A)),A**(B*D*A*D*A**B*A**(~B*A)))"),
)
ROW_NAMES = ("r_star",) + tuple(f"rho_{i}" for i in range(1, 9))
ONE = frozenset({("", "")})
MAX_POLYNOMIAL_TERMS = 4096
MAX_PRODUCT_PAIRS = 1000000
MAX_EQUALITY_SOURCE_DEPTH = 16


class WordDAG:
    def __init__(self):
        self.nodes = []
        self.lengths = []
        self.depths = []
        self.intern = {}
        self.names = {}
        for name in ("c", "b_1", "b_2", "b_3"):
            self.names[name] = self.add(("leaf", name))

    def add(self, node):
        if node in self.intern:
            return self.intern[node]
        index = len(self.nodes)
        self.intern[node] = index
        self.nodes.append(node)
        if node[0] == "leaf":
            length, depth = 1, 0
        elif node[0] == "inv":
            length, depth = self.lengths[node[1]], 1 + self.depths[node[1]]
        else:
            length = self.lengths[node[1]] + self.lengths[node[2]]
            depth = 1 + max(self.depths[node[1]], self.depths[node[2]])
        self.lengths.append(length)
        self.depths.append(depth)
        return index

    def mul(self, left, right):
        return self.add(("mul", left, right))

    def inv(self, word):
        node = self.nodes[word]
        return node[1] if node[0] == "inv" else self.add(("inv", word))

    def power(self, word, exponent):
        if exponent < 0:
            return self.power(self.inv(word), -exponent)
        if exponent == 1:
            return word
        if exponent < 1:
            raise ValueError("Only nonzero integer powers occur in this compiler")
        half = self.power(word, exponent // 2)
        square = self.mul(half, half)
        return square if exponent % 2 == 0 else self.mul(square, word)

    def parse(self, source):
        def integer(node):
            if isinstance(node, ast.Constant) and type(node.value) is int:
                return node.value
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
                inner = integer(node.operand)
                return -inner if inner is not None else None
            return None

        def visit(node):
            if isinstance(node, ast.Name):
                return self.names[node.id]
            if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Invert):
                return self.inv(visit(node.operand))
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
                return self.mul(visit(node.left), visit(node.right))
            if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
                base = visit(node.left)
                exponent = integer(node.right)
                if exponent is not None:
                    return self.power(base, exponent)
                actor = visit(node.right)
                return self.mul(self.mul(self.inv(actor), base), actor)
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and not node.keywords:
                args = [visit(arg) for arg in node.args]
                if node.func.id == "comm" and len(args) == 2:
                    left, right = args
                    return self.mul(self.mul(self.mul(left, right), self.inv(left)), self.inv(right))
                if node.func.id in ("gamma", "gamma2") and len(args) == 1:
                    cycle = self.names["c"]
                    actor = cycle if node.func.id == "gamma" else self.inv(cycle)
                    return self.mul(self.mul(actor, args[0]), self.inv(actor))
            raise ValueError(f"Unsupported source expression: {ast.dump(node)}")

        return visit(ast.parse(source, mode="eval").body)


def compile_program():
    graph = WordDAG()
    for name, expression in DEFINITIONS:
        graph.names[name] = graph.parse(expression)
    return graph


def evaluate_graph(graph, leaves, multiply, invert):
    """One value per DAG node; reused references also share reverse-mode work."""
    values = []
    for node in graph.nodes:
        if node[0] == "leaf":
            value = leaves[node[1]]
        elif node[0] == "inv":
            value = invert(values[node[1]])
        else:
            value = multiply(values[node[1]], values[node[2]])
        values.append(value)
    return values


def toggle(terms, term):
    if term in terms:
        terms.remove(term)
    else:
        terms.add(term)


def compact(polynomial):
    """Exact sibling contraction; no claim that this is a general normal form."""
    terms = set(polynomial)
    if len(terms) > MAX_POLYNOMIAL_TERMS:
        raise ArithmeticError("Exact prefix polynomial exceeded its fixed term cap")
    while True:
        parents = sorted({(target[:-1], source[:-1]) for target, source in terms
                          if target and source and target[-1] == source[-1]})
        for target, source in parents:
            zero, one = (target + "0", source + "0"), (target + "1", source + "1")
            if zero in terms and one in terms:
                terms.remove(zero)
                terms.remove(one)
                toggle(terms, (target, source))
                break
        else:
            return frozenset(terms)


def polynomial_product(left, right):
    """s_a t_b s_c t_d, with prefix cancellation and F2 coefficient parity."""
    if len(left) * len(right) > MAX_PRODUCT_PAIRS:
        raise ArithmeticError("Exact prefix product exceeded its fixed pair cap")
    terms = set()
    for target, source in left:
        for next_target, next_source in right:
            if next_target.startswith(source):
                toggle(terms, (target + next_target[len(source):], next_source))
            elif source.startswith(next_target):
                toggle(terms, (target, next_source + source[len(next_target):]))
    return compact(terms)


def polynomial_equal(left, right):
    """Compare after exact common-depth refinement of the input prefixes.

    At fixed input depth each remaining column is a free polynomial in the
    prefix-addition operators s_0,s_1, so zero means literal coefficient parity.
    """
    difference = set(left) ^ set(right)
    if not difference:
        return True
    depth = max(len(source) for _target, source in difference)
    if depth > MAX_EQUALITY_SOURCE_DEPTH:
        raise ArithmeticError("Exact prefix comparison exceeded its source-depth cap")
    expanded = set()
    for target, source in difference:
        for bits in itertools.product("01", repeat=depth - len(source)):
            suffix = "".join(bits)
            toggle(expanded, (target + suffix, source + suffix))
    return not expanded


def swap_table(first, second):
    if first.startswith(second) or second.startswith(first):
        raise ValueError("A cylinder swap requires incomparable prefixes")
    leaves = {""}
    while True:
        split = next((leaf for leaf in sorted(leaves)
                      if leaf not in (first, second)
                      and (first.startswith(leaf) or second.startswith(leaf))), None)
        if split is None:
            break
        leaves.remove(split)
        leaves.update((split + "0", split + "1"))
    return frozenset((second if leaf == first else first if leaf == second else leaf, leaf)
                     for leaf in leaves)


def exact_native_check(graph):
    cycle = frozenset({("01", "00"), ("1", "01"), ("00", "1")})
    cycle_inverse = frozenset((source, target) for target, source in cycle)
    b1 = ONE ^ {("000", "01")}
    b2 = ONE ^ {("00", "010")}
    b3 = ONE ^ {("000", "011"), ("001", "010")}
    leaves = {"c": (cycle, cycle_inverse), "b_1": (b1, b1),
              "b_2": (b2, b2), "b_3": (b3, b3)}

    # Group inverses are carried separately. A Leavitt adjoint would NOT be
    # the group inverse of these elementary shears.
    values = evaluate_graph(
        graph, leaves,
        lambda left, right: (polynomial_product(left[0], right[0]),
                             polynomial_product(right[1], left[1])),
        lambda value: (value[1], value[0]),
    )
    expected = {
        "d": ONE ^ {("00", "1")},
        "a": ONE ^ {("00", "01")},
        "p_0": ONE ^ {("01", "10")},
        "q_0": ONE ^ {("10", "01")},
        "p_1": ONE ^ {("01", "11")},
        "q_1": ONE ^ {("11", "01")},
        "A": swap_table("00", "01"),
        "X_0": swap_table("01", "10"),
        "X_1": swap_table("01", "11"),
        "D": swap_table("1", "00"),
        "B": frozenset({("00", "00"), ("11", "01"), ("01", "10"), ("10", "11")}),
    }
    compiler_checks = {name: polynomial_equal(values[graph.names[name]][0], target)
                       for name, target in expected.items()}
    inverse_checks = {
        name: polynomial_equal(polynomial_product(value[0], value[1]), ONE)
              and polynomial_equal(polynomial_product(value[1], value[0]), ONE)
        for name, value in leaves.items()
    }
    relator_checks = {name: polynomial_equal(values[graph.names[name]][0], ONE)
                      for name in ROW_NAMES}
    return {
        "representation": "Phi on complete code(00,01,1); pairs mean s_target t_source",
        "leaf_inverse_checks": inverse_checks,
        "compiler_prefix_checks": compiler_checks,
        "native_relator_identity_checks": relator_checks,
        "checks_passed": all(inverse_checks.values()) and all(compiler_checks.values())
                         and all(relator_checks.values()),
        "generator_prefix_tables": {name: sorted(values[graph.names[name]][0])
                                    for name in ("A", "B", "D", "X_0", "X_1")},
        "largest_retained_prefix_polynomial": max(len(part) for value in values for part in value),
    }


def source_length_check(graph, artifact_text):
    actual = {name: graph.lengths[index] for name, index in graph.names.items()}
    compared = {}
    for displayed, expected in re.findall(r"^\| `([^`]+)` \| (\d+) \|$", artifact_text, re.M):
        for name in re.split(r"[,=]", displayed):
            name = name.strip().replace("r_*", "r_star")
            if name in actual:
                compared[name] = {"source": int(expected), "compiled": actual[name],
                                  "matches": int(expected) == actual[name]}
    return {
        "comparisons": compared,
        "all_nine_relators_present": all(name in compared for name in ROW_NAMES),
        "checks_passed": all(name in compared for name in ROW_NAMES)
                         and all(item["matches"] for item in compared.values()),
    }


def torch_forward_backward(graph, checkpoint):
    """One explicit saved-input smoke check, with no iteration or update."""
    import torch

    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.use_deterministic_algorithms(True)
    payload = torch.load(checkpoint, map_location="cpu", weights_only=True)
    unitary = payload["best_U"].detach().to(dtype=torch.complex128, device="cpu")
    cycle = payload["C"].detach().to(dtype=torch.complex128, device="cpu")
    flips = payload["D"].detach().to(dtype=torch.complex128, device="cpu")
    if unitary.shape != (24, 24) or cycle.shape != (24, 24) or flips.shape != (3, 24, 24):
        raise ValueError("The optional smoke check accepts only the existing dimension-24 checkpoint")
    identity = torch.eye(24, dtype=torch.complex128, device="cpu")
    u_defect = float(torch.linalg.vector_norm(unitary.mH @ unitary - identity) / (24 ** 0.5))
    if u_defect > 1e-10 or not torch.isfinite(unitary).all():
        raise ArithmeticError("Saved U failed the unitary-input check")
    for a in range(3):
        for x in range(8):
            basis = identity[:, 8 * a + x]
            if not torch.equal(cycle @ basis, identity[:, 8 * ((a + 1) % 3) + x]):
                raise ArithmeticError("Saved C has the wrong frozen orientation")
            for bit in range(3):
                if not torch.equal(flips[bit] @ basis, identity[:, 8 * a + (x ^ (1 << bit))]):
                    raise ArithmeticError("Saved D has the wrong frozen orientation")
    unitary.requires_grad_(True)
    started = time.monotonic()
    leaves = {"c": cycle, **{f"b_{i + 1}": unitary @ flips[i] @ unitary.mH for i in range(3)}}
    values = evaluate_graph(graph, leaves, lambda left, right: left @ right, lambda value: value.mH)
    rows = [values[graph.names[name]] for name in ROW_NAMES]
    squared = torch.stack([(value - identity).abs().square().sum() / 24 for value in rows])
    loss = squared.sum()
    forward_seconds = time.monotonic() - started
    backward_started = time.monotonic()
    gradient, = torch.autograd.grad(loss, unitary)
    backward_seconds = time.monotonic() - backward_started
    finite = bool(torch.isfinite(squared).all() and torch.isfinite(gradient).all())
    return {
        "checkpoint": str(checkpoint),
        "checkpoint_sha256": hashlib.sha256(checkpoint.read_bytes()).hexdigest(),
        "torch_version": str(torch.__version__),
        "device": "cpu", "dtype": "complex128", "dimension": 24,
        "threads": torch.get_num_threads(), "interop_threads": torch.get_num_interop_threads(),
        "input_unitarity_defect": u_defect,
        "row_HS_residuals": dict(zip(ROW_NAMES, squared.detach().sqrt().tolist())),
        "gradient_frobenius_norm": float(torch.linalg.vector_norm(gradient)),
        "word_unitarity_defect_max": max(float(torch.linalg.vector_norm(value.detach().mH @ value.detach() - identity)
                                                / (24 ** 0.5)) for value in rows),
        "forward_seconds": forward_seconds, "backward_seconds": backward_seconds,
        "finite_values": finite,
        "optimization_steps": 0,
        "scope": "One saved-input numerical DAG replay; no lower bound or feasibility certificate",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--artifact", type=Path, default=ARTIFACT,
                        help="Exact source artifact whose current table is checked")
    parser.add_argument("--torch-checkpoint", type=Path,
                        help="Explicit existing pilot checkpoint for one CPU forward/backward replay")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.exists():
        parser.error("output must be new; this verifier does not overwrite files")
    started = time.monotonic()
    artifact_bytes = args.artifact.read_bytes()
    graph = compile_program()
    lengths = source_length_check(graph, artifact_bytes.decode("utf-8"))
    native = exact_native_check(graph)
    costs = Counter(node[0] for node in graph.nodes)
    row_lengths = {name: graph.lengths[graph.names[name]] for name in ROW_NAMES}
    torch_result = None
    if args.torch_checkpoint is not None:
        if not lengths["checks_passed"] or not native["checks_passed"]:
            raise ArithmeticError("Numerical replay requires exact source/native checks to pass first")
        torch_result = torch_forward_backward(graph, args.torch_checkpoint.resolve())
    checks_passed = lengths["checks_passed"] and native["checks_passed"]
    if torch_result is not None:
        checks_passed = checks_passed and torch_result["finite_values"]
    report = {
        "schema": "leavitt-nine-word-dag-v1",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "source_artifact": str(args.artifact),
        "source_artifact_sha256": hashlib.sha256(artifact_bytes).hexdigest(),
        "source_expressions": dict(DEFINITIONS),
        "word_lengths": row_lengths,
        "source_length_check": lengths,
        "exact_native_prefix_verification": native,
        "dag": {
            "nodes": graph.nodes,
            "named_roots": graph.names,
            "operation_counts": dict(costs),
            "max_depth": max(graph.depths),
            "forward_matrix_multiplications_with_three_conjugated_factors": costs["mul"] + 6,
            "reverse_matrix_multiplication_upper_bound": 2 * (costs["mul"] + 6),
            "expanded_letters_total": sum(row_lengths.values()),
            "expanded_letters_max": max(row_lengths.values()),
            "retained_forward_matrix_bytes_upper_bound_at_n24": len(graph.nodes) * 24 * 24 * 16,
            "complexity": "Each multiplication node is evaluated once and has at most two "
                          "matmul VJPs; inverse nodes are adjoints. Shared uses accumulate "
                          "gradients at one node. Cost depends on the DAG, not expanded lengths.",
        },
        "torch_replay": torch_result,
        "checks_passed": checks_passed,
        "elapsed_seconds": time.monotonic() - started,
        "scope": "Exact compiler/prefix verification and optional one-input numerical replay; "
                 "no optimization, dimension-uniform HS gap, or nonhyperlinearity conclusion",
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("x") as handle:
        json.dump(report, handle, indent=2, allow_nan=False)
        handle.write("\n")
    print(json.dumps({"output": str(output), "checks_passed": checks_passed,
                      "DAG_multiplications": costs["mul"],
                      "largest_expanded_word": max(row_lengths.values()),
                      "elapsed_seconds": report["elapsed_seconds"]}, allow_nan=False))
    return 0 if checks_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
