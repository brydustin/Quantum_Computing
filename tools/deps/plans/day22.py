"""Audit tick 13 (2026-10-27): the complete positivity of a convex combination proved once
(completely_positive_convex, wip/d23/D22.thy); UCP_convex and CPTP_convex add their unital /
trace-preserving part in a few lines."""
import os, sys
sys.path.insert(0, os.path.dirname(__file__))
from planlib import *

S = scratch_blocks("wip/d23/D22.thy")
edit("Day22_Minimal_Kraus.thy", remove=["UCP_convex", "CPTP_convex"],
     insert_after=[("amplification_smult",
                    [txt(r"""Convex combinations: the amplification is linear in the map, and positive matrices are closed
under non-negative combinations, so $t\Phi_1+(1-t)\Phi_2$ is completely positive; it is unital, resp.
trace preserving, when $\Phi_1$ and $\Phi_2$ are."""), S["completely_positive_convex"]]),
                   ("UCP_convex", [S["UCP_convex"]]),
                   ("CPTP_convex", [S["CPTP_convex"]])])
print("installed")
