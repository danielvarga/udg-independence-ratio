import numpy as np

def pack_sets(sets):
    """
    Atoms are boolean arrays with length=num_vertices.
    This function bit-packs them to make searching faster.
    """
    sets = np.asarray(sets, dtype=bool)
    return np.packbits(sets, axis=1, bitorder="little")

def find_containing_sets_packed(packed_sets, new_set):
    """
    Given a set of atoms packed by pack_sets, and another atom new_set (a boolean array with num_verts length)
    find all atoms that contain every vertex contained by new_set.
    In other words, find all independent vertex supersets of new_set.
    """
    new_set = np.asarray(new_set, dtype=bool)
    packed_new = np.packbits(new_set, bitorder="little")

    mask = ((packed_sets & packed_new) == packed_new).all(axis=1)
    return np.flatnonzero(mask)

def get_independent_subsets_from_matrix(adjacency_matrix):
    """
    Given a boolean adjacency matrix, find all independent sets.
    These are returned as boolean arrays with num_verts length, indicating which vertices are in
    which independent set. These independent sets are called "atoms".
    """
    n = adjacency_matrix.shape[0]
    assert adjacency_matrix.shape == (n, n)
    breadth = np.array([[0], [1]], dtype=bool)
    for i in range(1, n):
        row = adjacency_matrix[i, :i]

        can_add_vertex = ~np.any(
            breadth[:, row],
            axis=1
        )        
        new_breadth_len = len(breadth) + np.sum(can_add_vertex)

        new_breadth = np.empty(
            (new_breadth_len, i + 1),
            dtype=bool
        )
        new_breadth[:len(breadth), :i] = breadth
        new_breadth[:len(breadth), i] = False
        new_breadth[len(breadth):, :i] = breadth[can_add_vertex]
        new_breadth[len(breadth):, i] = True

        breadth = new_breadth

    return breadth