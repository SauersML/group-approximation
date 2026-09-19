#!/usr/bin/env python3
"""Exact free-rank-eight core of profile27 I(0;131)."""

from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

PATH = Path(__file__).with_name("compress-l14-profile27-131-base.py")
SPEC = spec_from_file_location("profile27_131_base_i", PATH)
B = module_from_spec(SPEC)
SPEC.loader.exec_module(B)
FREE = B.FREE
SYSTEM, WORDS = B.build("I0131")
R0, R2, R4, K = (WORDS[name] for name in ("R0", "R2", "R4", "K"))
