"""Audit tick 26 (2026-10-28): Day 14's theorem that a pure ensemble is parallel to its state, as
the notes argue it - w = psi_i - <psi|psi_i> psi is orthogonal to psi, so <w|rho w> = 0 forces every
<phi|w> = 0, in particular <psi_i|w> = 0, so <w|w> = 0 (wip/d23/D14b.thy)."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D14b.thy")
edit("Day14_Pure_States.thy",
     remove=["pure_ensemble_parallel"],
     insert_after=[("pure_ensemble_parallel", [S["pure_ensemble_parallel"]])])
print("installed")
