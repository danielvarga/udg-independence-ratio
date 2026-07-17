"""
This script verifies the G29 graph.
Inputs:
    verts_sym.npy     - symbolic vertices as SymPy objects
    congruences.txt   - a list of congruences between independent sets of verts_sym
    rational_dual.txt - a rational solution to the dual LP described below
"""

import numpy as np
import sympy as sp
from tqdm import tqdm, trange
import re
import ast
import math
from utils import pack_sets, find_containing_sets_packed, get_independent_subsets_from_matrix
from scipy.sparse import lil_matrix
from scipy.sparse import save_npz, load_npz

"""SETTINGS"""
"""
You can disable certain verification steps, which will load certain files
from the disk instead of recalculating them.
For fully rigorous verification, leave everything on "True".

This will take roughly 20-30 minutes, the majority of which is building the IEC matrix.
For the sake of readability, this was not optimized further.
"""
directory = "snail_reproduction"
BUILD_ADJ = True
VERIFY_CONGS = True
BUILD_IEC = True

"""VERIFY ATOMS"""
"""
Load symbolic vertices, calculate adjacency matrix symbolically and save it.
Then calculate atoms (independent sets) from the adjacency matrix.
The ie1 constraint vector is also built, which asserts that the total aggregate
weight on the first vertex must equal 1.
The primal constraint is:
    ie1 @ atom_weights = 1
"""

verts = np.load(directory + "/verts_sym.npy", allow_pickle=True)

n = len(verts)
if BUILD_ADJ:
    print("> BUILDING ADJACENCY MATRIX")
    A = np.zeros(shape=(n,n), dtype=bool)
    for i in tqdm(range(n)):
        for j in range(n):
            res = abs(verts[i]-verts[j]).equals(sp.sympify("1"))
            assert res is not None
                
            A[i][j] = res

    np.save(directory + "/true_adj.npy", A)
else:
    print("! SKIPPED BUILD_ADJ")
    A = np.load(directory + "/true_adj.npy")

atoms = get_independent_subsets_from_matrix(A)
print("> GENERATED", len(atoms), "ATOMS")
ie1 = atoms[:, 0]

"""VERIFY CONGS"""
"""
Load the list of congruences from congruences.txt, then verify them symbolically
using our symbolic vertices. This is done by going over all vertex pairs x,y in a congruence,
and checking if dist(f(x), f(y)) = dist(x,y). Memoization is used to speed up this process.
"""

congs = []
with open(directory + "/congruences.txt", "r") as f:
    pattern = re.compile(r"^\S+\s+(\[.*?\])\s*=\s*(\[.*?\])$")
    for line in f:
        match = pattern.match(line)
        if match:
            left = ast.literal_eval(match.group(1))
            right = ast.literal_eval(match.group(2))
            congs.append((left, right))
print("> LOADED", len(congs), "CONGRUENCES")

if VERIFY_CONGS:
    print("> VERIFYING CONGRUENCES")
    MEMO = np.zeros(shape=(n,n,n,n), dtype=int)
    for cong in tqdm(congs):
        left, right = cong

        assert len(left) == len(right)

        for i in range(len(left)):
            for j in range(len(left)):
                pre1 = left[i]
                img1 = right[i]
                pre2 = left[j]
                img2 = right[j]

                if MEMO[pre1][pre2][img1][img2]:
                    continue
                
                assert abs(verts[pre1] - verts[pre2]).equals(abs(verts[img1] - verts[img2]))

                MEMO[pre1][pre2][img1][img2] = 1
                MEMO[pre2][pre1][img1][img2] = 1
                MEMO[pre1][pre2][img2][img1] = 1
                MEMO[pre2][pre1][img2][img1] = 1
else:
    print("! SKIPPED VERIFY_CONGS")

"""BUILD IEC"""
"""
Build the IEC constraint matrix using our verified congruences.
Each row of this matrix asserts that the aggregate weights on a pair S,S' of isometric
atoms is the same. The final primal constraint is
    iec @ atom_weights = 0
"""

if BUILD_IEC:
    print("> BUILDING IEC MATRIX")

    packed_atoms = pack_sets(atoms)

    iec_lil = lil_matrix((len(congs), len(atoms)), dtype=int)
    for cong_idx in tqdm(range(len(congs))):
        left, right = congs[cong_idx]

        left_atom = np.zeros(shape=(n), dtype=int)
        left_atom[left] = 1
        right_atom = np.zeros(shape=(n), dtype=int)
        right_atom[right] = 1

        left_containing_atoms = find_containing_sets_packed(packed_atoms, left_atom)
        right_containing_atoms = find_containing_sets_packed(packed_atoms, right_atom)

        iec_row = np.zeros(shape=(len(atoms)), dtype=int)
        iec_row[left_containing_atoms] += 1
        iec_row[right_containing_atoms] -= 1

        iec_lil[cong_idx, :] = iec_row

    iec = iec_lil.tocsc()
    save_npz(directory + "/iec.npz", iec)
else:
    print("! SKIPPED BUILD_IEC")
    iec = load_npz(directory + "/iec.npz")

"""VERIFY RATIONAL DUAL"""
"""
Load the rational dual witness from rational_dual.txt, and verify.
The primal is
    minimize sum(atom_weights)
subject to
    atom_weights >= 0
    ie1 @ atom_weights = 1
    iec @ atom_weights = 0

Let d (delta) be the dual variable of ie1, and
y be the dual vector corresponding to the rows of iec.
Then the dual LP is:
    maximize d
subject to
    y @ iec + d @ ie1 <= 1

d = num/denum
Multiply by the common denominator denum

    -y_num @ iec - num @ ie1 + denum >= 0

Here we took the liberty of multiplying each numerator in rational_dual.txt
by -1, hence in the code:

    y_num @ iec - num @ ie1 + y_lcm >= 0

since we assert y_lcm = denum.
"""
def verify_witness(C, e, y):
    """
    This function verifies if the witness vector `y`
    indeed satisfies the system on inequalities
    y^T @ C - e * 4000716307/1000000018 + 1 >= 0
    y_numer^T @ C - e * 4000716307 + 1000000018 >= 0
    """

    num_iec, num_atoms = C.shape

    y_lcm = math.lcm(*(d for n, d in y))

    y_int = [
        n * y_lcm // d for n, d in y
    ]

    print("> VERIFYING DUAL", flush=True)

    numerator, denominator = 4000716307, 1000000018

    assert y_lcm == denominator

    min_slack = math.inf
    with trange(num_atoms) as progress_bar:
        for atom_id in progress_bar:

            col = C[:, atom_id]

            rows = col.indices
            vals = col.data

            neg_rows = rows[vals < 0]
            pos_rows = rows[vals > 0]

            scalar_prod =  sum(y_int[i] for i in pos_rows) - sum(y_int[i] for i in neg_rows)
            slack = scalar_prod - numerator * int(e[atom_id]) + y_lcm

            assert slack >= 0
            min_slack = min(slack, min_slack)

    print("+ WITNESS VERIFICATION COMPLETE.", flush=True)
    print("> MIN_SLACK =", min_slack, "DUAL_VAL =", numerator/denominator)

witness_file = directory + "/rational_dual.txt"
with open(witness_file) as f:
    y = [
        list(map(int, row.split()))
        for row in f.read().split('\n')
        if not row.startswith("#") and len(row.split())
    ]
print(f"> WITNESS VECTOR LOADED WITH {len(y)} ENTRIES")

verify_witness(iec, ie1, y)