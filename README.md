# A Unit-Distance Graph in the Plane with Independence Ratio Below 1/4

Supplementary material for the paper [A unit-distance graph in the plane with independence ratio below 1/4](https://arxiv.org/abs/2606.28157) by Ákos Dúcz and Dániel Varga.

We present a unit-distance graph $G$ in the plane with geometric fractional chromatic number $\mathrm{GFCN}(G) > 4$. This implies the existence of a unit-distance graph in the plane with independence ratio below $1/4$, settling the second half of [Erdős Problem #1070](https://www.erdosproblems.com/1070): whether every $n$-point set in the plane must contain at least $n/4$ points with no two at distance $1$.

Our graph $G_{29}$ is presented as a list of 29 complex numbers, stored symbolically as SymPy objects. We also provide a Python script to symbolically verify that the graph is indeed a unit-distance graph, and to verify our dual witness, proving a lower bound on $\mathrm{GFCN}(G_{29})$.

The [`snail_reproduction`](snail_reproduction/) directory contains the supplementary material for reproducing the certificate:

- `verts_sym.npy` - a NumPy array containing 29 SymPy objects, our vertices.
- `congruences.txt` - a list of congruences between independent subsets of $G_{29}$.
- `rational_dual.txt` - a dual GFCN LP solution, as rational numbers, certifying $\mathrm{GFCN}(G_{29}) > 4$.
- `verify_data.py` - a verification script for the supplementary material.
- `utils.py` - utilities for `verify_data.py`.

Run the verification with:

```sh
python snail_reproduction/verify_data.py
```

The verification steps in detail:

1. We first load the symbolic vertices, and build an adjacency matrix $A$ using SymPy.
2. We calculate the independent sets of $G_{29}$, also called atoms, from $A$.
3. After loading the congruences, we again use SymPy to verify that each one is indeed an isometry.
4. We build the IEC matrix from the congruences, which describe our geometric congruence constraints.
5. Finally we load the rational dual solution and verify it using simple integer arithmetic.

The verification process takes roughly 20-30 minutes, and certain parts can be disabled if needed, provided that the necessary precomputed data is supplied beforehand.

![The graph G_29](snail_reproduction/figures/snail.svg)

![Congruence structure for G_29](snail_reproduction/figures/snail_congs.svg)

## Formalization

The [`formalization`](formalization/) directory contains the Lean formalization from [bbeatrix/unit-distance-graph-independence-ratio](https://github.com/bbeatrix/unit-distance-graph-independence-ratio), copied intact into this repository.

Many thanks to Beatrix Benkő for her work on the autoformalization.

## Planned Addition

A PDF will be added later presenting the case for a specific $10^{10^{10^{10^{13}}}}$ upper bound on the size of a unit-distance graph with the required independence ratio below $1/4$.
