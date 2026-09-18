"""Word lists of the trap group Gamma_trap (copied from the w10 orbit-trap
artifact trap_group.py, so this directory is self-contained)."""

GEN_NAMES = ["as", "at", "c", "b1", "bs", "bt", "u"]
LEFT = ["as", "at", "c"]
RIGHT = ["b1", "bs", "bt"]

DERIVED = [
    ("w1", ["u", "c", "u", "c"]),
    ("r", ["u", "b1", "u", "b1"]),
    ("us", ["w1", "as", "w1", "as"]),
    ("ut", ["w1", "at", "w1", "at"]),
    ("ws", ["us", "c", "us", "c"]),
    ("wt", ["ut", "c", "ut", "c"]),
    ("ust", ["wt", "as", "wt", "as"]),
    ("h", ["u", "ust"]),
]

UNIP = ["u", "us", "ut", "ust", "w1", "ws", "wt", "r"]

TRAP_RELS = [
    ("TRAP_R1", ["us"], ["r", "bs", "r", "bs"]),
    ("TRAP_R2", ["ut"], ["r", "bt", "r", "bt"]),
    ("TRAP_R3", ["u"], ["ws", "at", "ws", "at"]),
]
for _x in LEFT:
    for _y in RIGHT:
        TRAP_RELS.append(("LR_%s_%s" % (_x, _y), [_x, _y], [_y, _x]))
for _i, _x in enumerate(UNIP):
    for _y in UNIP[_i + 1:]:
        TRAP_RELS.append(("UU_%s_%s" % (_x, _y), [_x, _y], [_y, _x]))
INVOL_RELS = [("INV_%s" % g, [g, g], []) for g in GEN_NAMES]


def _comm(name, x, y):
    return (name, [x, y], [y, x])


EXTRA_RELS = [
    _comm("X_as_at", "as", "at"),
    _comm("X_bs_bt", "bs", "bt"),
    _comm("X_b1_r", "b1", "r"),
]
for _w in ["w1", "ws", "wt"]:
    EXTRA_RELS.append(_comm("X_c_" + _w, "c", _w))
    for _b in ["bs", "bt"]:
        EXTRA_RELS.append(_comm("X_%s_%s" % (_b, _w), _b, _w))
for _a in ["as", "at"]:
    for _x in ["u", "us", "ut", "ust", "r"]:
        EXTRA_RELS.append(_comm("X_%s_%s" % (_a, _x), _a, _x))
for _b in ["bs", "bt"]:
    for _x in ["u", "us", "ut", "ust"]:
        EXTRA_RELS.append(_comm("X_%s_%s" % (_b, _x), _b, _x))
