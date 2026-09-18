"""ctypes wrapper for the Neuwirth thickenability test thick2.c (built on first import)."""
import ctypes, os, subprocess
_here = os.path.dirname(os.path.abspath(__file__))
_so = os.path.join(_here, "libthick2.so")
if not os.path.exists(_so) or os.path.getmtime(_so) < os.path.getmtime(os.path.join(_here, "thick2.c")):
    subprocess.check_call(["gcc", "-O2", "-shared", "-fPIC", "-o", _so, os.path.join(_here, "thick2.c")])
_lib2 = ctypes.CDLL(_so)
_lib2.thick2.restype = ctypes.c_int
_lib2.thick2.argtypes = [ctypes.c_int, ctypes.POINTER(ctypes.c_int), ctypes.POINTER(ctypes.c_int), ctypes.c_long]
CODE = {'x': 1, 'X': -1, 'y': 2, 'Y': -2, 'z': 3, 'Z': -3, 'w': 4, 'W': -4}

def thick2(rels, cap=0):
    """True iff the presentation complex is thickenable (orientable 1-handle convention);
    None if the node cap is hit."""
    lets = [CODE[ch] for r in rels for ch in r]
    lens = [len(r) for r in rels]
    A = (ctypes.c_int * len(lens))(*lens); B = (ctypes.c_int * len(lets))(*lets)
    r = _lib2.thick2(len(rels), A, B, cap)
    if r == -1:
        raise ValueError("not cyclically reduced")
    return None if r == -2 else bool(r)
