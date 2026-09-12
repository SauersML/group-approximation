#!/usr/bin/env python3
"""Run the exact relative-picture census for the affine Omega candidate."""

import importlib.util
from pathlib import Path


SOURCE = Path(__file__).with_name(
    "search-leavitt-degree4-relative-pictures.py")
SPEC = importlib.util.spec_from_file_location("pictures", SOURCE)
P = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(P)

P.UNITS["q"] = P.Q
P.INVERSES["q"] = P.Q

# W_8 = r t^2 a t^-1 c t^2 e t^-1 q t p t.  The target retained by the
# imported engine is Omega(c_0,p_0)=[c_0,p_0^2 c_0 p_0^-2].
P.RELATORS = (
    (("g", 0, "r", 1), ("g", 2, "a", 1), ("g", 1, "c", 1),
     ("g", 3, "e", 1), ("g", 2, "q", 1), ("g", 3, "p", 1),
     ("z", 1)),
    (("g", 1, "r", 1), ("g", 3, "a", 1), ("g", 2, "c", 1),
     ("z", 1), ("g", 0, "e", 1), ("z", -1),
     ("g", 3, "q", 1), ("z", 1), ("g", 0, "p", 1)),
    (("g", 2, "r", 1), ("z", 1), ("g", 0, "a", 1),
     ("z", -1), ("g", 3, "c", 1), ("z", 1),
     ("g", 1, "e", 1), ("g", 0, "q", 1), ("g", 1, "p", 1)),
    (("g", 3, "r", 1), ("z", 1), ("g", 1, "a", 1),
     ("g", 0, "c", 1), ("g", 2, "e", 1), ("g", 1, "q", 1),
     ("g", 2, "p", 1)),
)
P.VERTEX_TYPES = tuple((relator, orientation,
                        *P.vertex(relator, orientation))
                       for relator in range(4)
                       for orientation in (1, -1))


if __name__ == "__main__":
    P.main()
