"""Check that the constants in D4Bound/Ledger.lean are outward roundings of the exact certificate values.

The Lean ledger uses, for each of the 124 census groups, a lower bound for the group's energy
floor, and an upper bound `urawUp` for the raw objective. This script reads the exact values
from census_floors.json and confirms, in exact rational arithmetic:

  * the Lean file lists exactly the 124 groups (N, j) of the census, each once;
  * each Lean floor is <= the exact floor and within 10^-24 of it;
  * urawUp >= the exact raw objective and within 10^-24 of it;
  * the raw objective minus the exact census minimum over 8 minus 3/8000000 equals the
    certificate's recorded objective (a consistency check of the inputs).

It also checks that the Lean definitions of lam, QN and the radii R1..R5 are the paper's.

Run from the lean/ folder:  python3 scripts/check_lean_inputs.py   Exit 0 means PASS.
"""
import json
import re
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent
DATA = LEAN.parent / "data"
TOL = Q(1, 10**24)


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def parse_exact(value):
    if type(value) not in (str, int):
        fail(f"inexact or nonnumeric certificate value: {value!r}")
    return Q(value)


def count(value, lo, hi):
    q = parse_exact(value)
    if q.denominator != 1 or not lo <= q <= hi:
        fail(f"count is not an integer in [{lo}, {hi}]: {value!r}")
    return q.numerator


lean = (LEAN / "D4Bound" / "Ledger.lean").read_text()
nbhd = (LEAN / "D4Bound" / "Neighbourhood.lean").read_text() + (LEAN / "D4Bound" / "FarPair.lean").read_text()
acc = json.loads((DATA / "census_floors.json").read_text())

for name, val in [("R1", "501473 / 500000"), ("R2", "1005643 / 1000000"), ("R3", "50379 / 50000"),
                  ("R4", "50767 / 50000"), ("R5", "102597 / 100000")]:
    if f"def {name} : ℝ := {val}" not in nbhd:
        fail(f"radius {name} is not {val}")
if "def lam (j : ℕ) : ℚ := if j = 1 then 3 / 1000000 else 1 / 1000000" not in lean:
    fail("lam is not 3/10^6 for j = 1 and 1/10^6 otherwise")
if "def QN (N : ℕ) : ℚ := (N : ℚ) * (13561 * N - 179244) / 250000" not in lean:
    fail("QN differs from N(13561 N - 179244)/250000")

block = re.search(r"def groups : List \(ℕ × ℕ × ℚ\) := \[(.*?)\]", lean, re.S)
if not block:
    fail("groups list not found")
rows = re.findall(r"\((\d+), (\d+), (\d+)/(\d+)\)", block.group(1))
lean_groups = {}
for N, j, num, den in rows:
    key = (int(N), int(j))
    if key in lean_groups:
        fail(f"duplicate group {key}")
    lean_groups[key] = Q(int(num), int(den))

exact = {}
for g in acc["profile"]:
    key = (count(g["N"], 0, 26), count(g["first_radius"], 1, 5))
    if key in exact:
        fail(f"duplicate census group {key}")
    exact[key] = parse_exact(g["new_floor"])

if len(exact) != 124 or set(exact) != set(lean_groups):
    fail(f"group sets differ: {len(exact)} census, {len(lean_groups)} Lean")
for key, lo in lean_groups.items():
    if not (lo <= exact[key] < lo + TOL):
        fail(f"floor of group {key} is not a 10^-24 lower rounding")

m = re.search(r"def urawUp : ℚ := (\d+)/(\d+)", lean)
if not m:
    fail("urawUp not found")
uup = Q(int(m.group(1)), int(m.group(2)))
uraw = Q(acc["exact_raw_objective"])
if not (uraw <= uup < uraw + TOL):
    fail("urawUp is not a 10^-24 upper rounding")

if Q(acc["exact_objective"]) != uraw - Q(acc["new_beta"]) / 8 - Q(acc["graph_saving"]):
    fail("recorded objective does not match raw objective, census minimum and graph saving")
if min(exact.values()) != Q(acc["new_beta"]):
    fail("census minimum differs from new_beta")

print("PASS: 124 groups, floors rounded down and urawUp rounded up by less than 10^-24; radii, lam and QN as in the paper")
