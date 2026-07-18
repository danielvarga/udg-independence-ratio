# unit-distance-graph-independence-ratio

[Beatrix Benkő's](https://github.com/bbeatrix) Lean 4 formalization of Dúcz–Varga (2026) — A finite unit-distance graph in the plane with independence ratio below 1/4.

## Contents

- [The result](#the-result)
- [Building and verifying](#building-and-verifying)
- [Status and trust base](#status-and-trust-base)
- [The proof](#the-proof)
- [Corollaries](#corollaries)
- [Repository layout](#repository-layout)
- [Attribution](#attribution)

## The result

This repository contains a Lean 4 formalization of **Theorem 1 of [DV26]**, stated as
`exists_independenceRatio_lt_quarter` (`Main.lean`).

> **[DV26], Theorem 1.** *There exists a finite unit-distance graph G in the plane such that
> α(G)/|V(G)| < 1/4.*

Here α(G) denotes the independence number of G, and a *unit-distance graph* is a simple graph
whose vertices are points of ℝ² and whose edges join pairs of points at Euclidean distance
exactly 1.

**Background.** [Erdős problem 1070](https://www.erdosproblems.com/1070) asks: let f(n) be maximal such that among
any n points of ℝ² there are f(n) points no two of which are at distance 1 — estimate f(n); *in
particular, is it true that f(n) ≥ n/4?* The particular question asks, equivalently, whether every
finite unit-distance graph has independence ratio at least 1/4.

- [M23] developed the *geometric fractional chromatic number* framework and constructed a
  27-vertex unit-distance graph G₂₇ with χ_gf(G₂₇) = 4. This gives f(n) ≤ (1/4 + o(1))·n.
  Their Conjecture 1 asserted that 4 is optimal — the finitary fractional chromatic number of
  the plane equals 4, with no finite unit-distance graph exceeding it — and the particular
  question remained open.
- [DV26] answers it **in the negative** — the theorem formalized here. A two-vertex augmentation
  of G₂₇ yields a 29-vertex graph G₂₉ with χ_gf(G₂₉) > 4 (the certificate value is ≈ 4.0007),
  and a blow-up construction turns this into a finite unit-distance graph with independence
  ratio strictly below 1/4 — so the
  finitary fractional chromatic number of the plane in fact *exceeds* 4, disproving [M23]'s
  Conjecture 1. A fortiori χ_f(ℝ²) > 4 for the full (infinite) unit-distance graph of the plane.

Estimating f(n) in general remains open.

The citation keys link to the papers on the arXiv:

- **[DV26]** Á. Dúcz and D. Varga, *A unit-distance graph in the plane with independence ratio below 1/4*, 2026.
- **[M23]** M. Matolcsi, I. Z. Ruzsa, D. Varga and P. Zsámboki, *The fractional chromatic number of the plane is at least 4*, 2023.

## Building and verifying

The only dependencies are [Lean 4](https://lean-lang.org/) (pinned via `lean-toolchain`:
`leanprover/lean4:v4.32.0-rc1`) and [Mathlib4](https://github.com/leanprover-community/mathlib4)
(pinned to a commit via `lake-manifest.json`). With [elan](https://github.com/leanprover/elan)
installed, it picks up the pinned toolchain automatically:

```sh
lake exe cache get   # download prebuilt Mathlib oleans (without this, Mathlib builds from source)
lake build           # builds and checks the whole development
```

The build is dominated by Component 2's certificate checks (`CertificateVerification.lean`, ~10 minutes of
`native_decide` compilation); everything is cached afterwards. A successful `lake build` means
every proof in the development has been checked.

To confirm the axiom footprint of the main theorem, check that

```sh
echo 'import UnitDistanceGraphs.Main
#print axioms UnitDistanceGraphs.exists_independenceRatio_lt_quarter' | lake env lean --stdin
```

reports exactly `propext, Classical.choice, Quot.sound` plus 13 `*._native.native_decide.ax_*`
entries (one per `native_decide` call site: `feasBM`, `congOk_true`, `cong_lt`, 8 × `hcong_special`,
`wKeys_complete`, `wLookup_keys_ok`) — and in particular no `sorryAx`. See
[Status and trust base](#status-and-trust-base) for what those axioms assert.

## Status and trust base

**The proof is complete and `sorry`-free.** The top-level theorem `exists_independenceRatio_lt_quarter` (`Main.lean`) is proved end-to-end. `#print axioms` reports the three standard logical axioms

```
propext, Classical.choice, Quot.sound
```

plus one `*._native.native_decide.ax_*` axiom per `native_decide` call site (13 in all) — the "trust the compiled evaluation" assertions that `native_decide` introduces, entering **only** through Component 2's LP-certificate checks (full list below). **There is no `sorryAx`.** Components 1 and 3 need no axioms beyond the standard three, and even Component 2's geometry — vertex injectivity (`vtx_injective`/`sepOk`) and the entire adjacency matrix (`nonEdgeOk`/`H_symm`/edges) — is closed by kernel `decide` over scaled-integer interval boxes.

| Component | Result (Lean) | Status |
|---|---|---|
| **1** — [M23] Thm 1: first blow-up | `exists_chi_f_gt` | complete, `sorry`-free · kernel-clean |
| **2** — [DV26] Lemma 1: LP certificate | `chi_gf_G29_gt` | complete, `sorry`-free · uses `native_decide` |
| **3** — [M23] Thm 2: second blow-up | `exists_low_independence_ratio` | complete, `sorry`-free · kernel-clean |

<details>
<summary><b>The <code>native_decide</code> axioms</b></summary>

The non-kernel dependencies are the per-call-site `*._native.native_decide.ax_*` axioms — each asserts "the compiled evaluation of this closed `Bool` term returned `true`", extending trust to the compiler pipeline exactly as the classical `Lean.ofReduceBool` axiom does. Per the axiom trace, they enter through exactly these Component-2 checks (all over exact `Int`/`ℕ`/`ℚ`/bitmask data — **no floating point**, so no rounding risk):

- `feasBM` — the 498168-atom per-atom LP feasibility (`Int`), driving `cert_per_atom`;
- `wLookup_keys_ok`, `wKeys_complete`, `cong_lt` — the weight-cache validations;
- `congOk` — the bulk congruence check (16859 pairs), and `hcong_special` — the finite checks (bitmask decodings and exact-`ℚ` parameter values) for the two special nested-radical congruences.

Because the certificate is exact — the rational dual witness is scaled by its common denominator `certDen`, so the feasibility check is pure `Int` arithmetic — `native_decide` here verifies the *exact* inequalities, not a decimal approximation. (A floating-point certificate would make `native_decide` meaningless: it would faithfully certify a rounded value, not the real LP.)

`native_decide` is **not logically required** — kernel `decide` is complete for decidable propositions, so an in-kernel LP certificate is possible in principle. It is a **performance** necessity: these checks are ~10⁷–10⁸ operations over large embedded data using `HashMap`, `String` parsing, and `ℚ` arithmetic, which the kernel reduces far too slowly (and may exhaust memory).

In principle the `native_decide` checks could be replaced by kernel `decide` over a suitably re-encoded certificate, reducing the axiom footprint to the three standard axioms at the cost of a much longer (hours-long) one-time build.

</details>

## The proof

Theorem 1 of [DV26] combines three components, formalized in the order below. (On the naming: the *overall target* is Theorem 1 of [DV26]; **Component 2 is that paper's Lemma 1** — the novel certificate from which its Theorem 1 is deduced.) They assemble as follows (`Main.lean`):

> χ_gf(G₂₉) > 4  (Component 2)  →  a finite G' with χ_f(G') > 4  (Component 1)  →  ∃ H with α(H)/|V(H)| < 1/4  (Component 3).  ∎

### Component 1 — [M23] Theorem 1: first blow-up, via amenability

**Statement.** For any finite unit-distance graph G, χ_gf(G) is a lower bound on χ_f of the plane, and blow-ups of G yield finite unit-distance graphs G' with χ_f(G') arbitrarily close to χ_gf(G). In Lean, `exists_chi_f_gt`: for `c < χ_gf V` there is a finite `V'` with `c < χ_f V'` — the direction of [M23]'s Theorem 1 (which states the equality of the finitary suprema) that the pipeline needs. (The definitions it builds on — χ_gf, geometric fractional colorings — live in `Definitions.lean`.)

<details>
<summary><b>Proof details</b></summary>

**Approach.** Amenability of the plane isometry group supplies the Følner set that symmetrizes a fractional coloring of a blow-up into a geometric coloring of G. We follow [M23]'s *abstract* argument — **not** a constructive word-set route, which is provably impossible here: G₂₉'s congruence group contains an irrational-angle rotation (e.g. `cong553`, linear part with minimal polynomial `3x⁴+3x³+4x²+3x+3`, not a root of unity), so it has **exponential** growth and its word-balls are not Følner. Amenability instead comes from solvability of `ℂ ≃ᵢ ℂ = ℝ² ⋊ O(2)` — and `O(2)` is solvable while `O(d)` for `d ≥ 3` is not, which is exactly why the argument works in the plane and does not extend to higher dimensions.

**Key results** (`Folner.lean`, `FirstBlowUp.lean`, `PlaneColoring.lean`):

- **Amenability core** (`Folner.lean`, reusable/upstreamable, none of it in Mathlib): `folnerCond_of_extension` (amenability closed under group extensions — the crux), `folnerCond_of_isCyclic` / `_of_finite` / `_of_comm` (base cases), `folnerCond_of_isSolvable` (derived-series induction).
- **`IsSolvable (ℂ ≃ᵢ ℂ)`** (`FirstBlowUp.lean`): `O(2)` solvable via `det → ℝˣ`, then the Mazur–Ulam linear-part hom `ℂ≃ᵢℂ → O(2)` with abelian translation kernel.
- **`exists_folner_set`** (`FirstBlowUp.lean`): the single ε-invariant finite set the averaging needs (no polynomial growth, no word-sets, no countability).
- `weight_stability` (LP continuity/compactness), `exists_optimal_coloring` (χ_f attained), the **pullback + averaging** construction `avgColoring` with weight preservation and the eq-20 defect reduction `avgColoring_marginal_diff_le`, `chi_f_le_nine` (uniform χ_f ≤ 9), and the assembly `exists_blowup_close` → `exists_chi_f_gt`.

</details>

### Component 2 — [DV26] Lemma 1: the LP certificate

**Statement.** χ_gf(G₂₉) > 4, where G₂₉ is the 29-vertex graph obtained by adding two vertices v₀, v₁ to the 27-vertex graph G₂₇ of [M23]. In Lean, `chi_gf_G29_gt : 4 < χ_gf G29`. (The certified LP value is `certNum`/`certDen` ≈ 4.0007; the strict bound `> 4` is all the pipeline needs. On the `native_decide` axioms this component introduces, see [Status and trust base](#status-and-trust-base).)

<details>
<summary><b>Proof details</b></summary>

**Approach.** Take the explicit 29-point set in ℂ, enumerate all independent sets and their congruence classes, assemble the geometric-fractional-coloring LP, and verify that the rational dual witness from [the supplementary data](https://users.renyi.hu/~akos/ep1070/) certifies the bound — a port of the Python verification to Lean, with the certificate check reduced to exact integer arithmetic. In detail:

- **Vertices.** `G29` — the 29 vertices as **exact algebraic coordinates** (from `verts_sym.npy`): base vertices in ℚ(√3,√11,√33), plus the two added vertices with √5 and nested radicals. `vtx : Fin 29 → ℂ` and `vtx_injective` are proved by the **interval-arithmetic method** (`injective_of_boxes`): each vertex lies in a rational box, and the 29 boxes are pairwise separated (`sepOk`); box bounds are scaled integers, so `sepOk` is closed by **axiom-free kernel `decide`**.
- **Distance geometry.** `dist_baseVert_eq_one_iff` reduces every base-sublattice adjacency (all 351 pairs) to a rational `norm_num` check, via `dist² = P + Q√33` and irrationality of √33. The two added-vertex edges are proved by `linear_combination`: `dist_v0_v4` (with v₀ ∈ ℚ(√3,√5,√11)) and `dist_v1_v4` (with v₁'s **nested radical** √(415/8 + 79√33/8)). All added-vertex non-edges are closed in the adjacency matrix `H` (`G29Vertices.lean`): `H_adj_iff` gives the whole 406-pair adjacency kernel-clean — 355 non-edges by one bulk interval `decide` (tight 10⁻⁶ boxes), 51 edges exact. So the entire distance geometry of G₂₉ is machine-checked.
- **Weak LP duality.** `geomFractionalChromaticNumber_ge_of_dual`: a feasible rational dual certificate implies χ_gf V ≥ c — the rigorous core of the certificate method. The rational dual is cleared to the integer denominator `certDen`, giving the integer objective `certNum`/`certDen` with `cert_value_gt_four` (`4·certDen < certNum`).
- **Completeness** (`Definitions.lean`). `indepEnum G l` enumerates the independent subsets incrementally; `indepEnum_eq` proves it equals `l.toFinset.powerset.filter IsIndepSet` **by induction, avoiding the 2²⁹ powerset**; `indepEnum_map` transports it along a vertex relabelling, so a *computable* `Fin 29` Bool-matrix graph can stand in for the non-computable `planeGraph`.
- **Congruences.** `congruent_of_dist_eq` (`PlaneIsometry.lean`): two ℂ-families with equal pairwise distances are related by one plane isometry. `hcong_all` (`CertificateVerification.lean`) then proves all 16859 congruences: the 28 singletons and 16829 base congruences uniformly (base distances `√(P + 2Q√33)`, equal iff the rational (P,Q) agree), and the 2 nested-radical/degree-8 congruences by explicit `linear_combination`.
- **Per-atom feasibility** (`cert_per_atom` / `feasBM`, `CertificateVerification.lean`). The integer inequality `certNum·[v₀∈S] ≤ certIntSum S + certDen` at every independent set, via the reindexing crux `certIntSum_eq_powerset` (`certIntSum T = ∑_{T'⊆T} wF T'`) and the bitmask machinery below.

**Efficiency: the bitmask machinery.** A brute-force per-atom `native_decide` (16859 congruences × 498168 atoms) is too slow, and `native_decide` over `indepEnum H` is **infeasible** — `indepEnum` builds its 498168 sets with `Finset.union`, whose dedup is ~O(n²). So the check runs over a *list-based bitmask* enumeration (no dedup) with an O(1) weight cache, all in `CertificateVerification.lean`:

1. `encode : Finset (Fin 29) → ℕ` with round-trip `bitsToFinset (encode T) = T` (via Mathlib's `Nat.mem_bitIndices`), and bit-set = insert.
2. `indepEnumBM : List (Fin 29) → List ℕ` mirrors `indepEnum` on bitmasks (lists ⇒ no dedup ⇒ `native_decide`-fast); the correspondence `indepEnumBM_corr` is proved by **structural induction on `l`**.
3. Weight cache `wMap : Std.HashMap ℕ ℤ` with O(1) `wLookup`; correctness is a bounded `native_decide` over the cached keys (`wLookup_keys_ok`) + a completeness check (`wKeys_complete`) + a mask bound `cong_lt` (< 2²⁹).
4. `effSum m` is a **structural** submask sum (no `Finset`, precomputed powers of two), proved `= certIntSum (bitsToFinset m)`. Feasibility `feasBM` is one `native_decide` over `indepEnumBM (finRange 29)`, transferred to `cert_per_atom` via `indepEnumBM_corr` + `effSum_eq_certIntSum`.

`feasBM` is the load-bearing atom-feasibility check, wired to the abstract dual slack by a kernel-checked proof — so its correctness rests on that proof, not on any numeric agreement.

</details>

### Component 3 — [M23] Theorem 2: second blow-up

**Statement.** If χ_f(G') > 4 for a finite unit-distance graph G', then there is a finite unit-distance graph H with α(H)/|V(H)| < 1/4. In Lean, `exists_low_independence_ratio` (`SecondBlowUp.lean`, layers L1–L5a + assembly); being pure kernel-checked mathematics, it adds **no** axioms.

([M23]'s Theorem 2 states that the *finitary* fractional chromatic number of the plane equals its Hall ratio; [DV26] invokes only the blow-up construction inside its proof, which is what we formalize directly.)

<details>
<summary><b>Proof details</b></summary>

**Construction.** The witness H is a **large discrete cube A** in the lattice generated by V(G'):

1. **Lattice basis** (L1, `CubeBasis`). The ℤ-span of V' in ℂ is finitely generated and torsion-free, hence a free ℤ-module (`Module.basisOfFiniteTypeTorsionFree'`); this yields a basis `w : Fin d → ℂ` in which every vertex has integer coordinates bounded by some `k`.
2. **The cube** (L2). `A = { ∑ βᵢ wᵢ : |βᵢ| ≤ N }`, with `|A| = (2N+1)^d` (injectivity from ℤ-linear independence) and the boundary inclusion `x − z ∈ (N+k)`-cube for `x ∈ V'`, `z ∈ A`.
3. **Maximum independent set** (L3). `B ⊆ A` with `|B| = α(A)`, and `|V' − B| ≤ (2(N+k)+1)^d`.
4. **Averaged counting coloring** (L4). `γ(S) = |{ t ∈ V'−B : V' ∩ (B+t) = S }| / |B|` is a fractional coloring of V' (translation preserves distances, so each `V' ∩ (B+t)` is independent), covering every vertex with marginal exactly `1` and of weight `|V'−B| / |B|`.
5. **Assembly** (L5a + Part 2, `SecondBlowUp.lean`). Every fractional coloring has weight `≥ χ_f(V')`, so `χ_f(V') ≤ |V'−B|/|B|` with `|B| = α(A)`, giving `α(A) ≤ (2(N+k)+1)^d / χ_f(V')`. Dividing by `|A| = (2N+1)^d`,

   ```
   α(A)/|A|  ≤  (1/χ_f(V')) · ((2(N+k)+1)/(2N+1))^d.
   ```

   The boundary factor `→ 1` as `N → ∞` (`exists_good_N`), and `χ_f(V') > 4` makes `1/χ_f(V') < 1/4` **strictly**, so for a large enough cube `α(A)/|A| < 1/4`.

</details>

## Corollaries

[`Corollaries.lean`](UnitDistanceGraphs/Corollaries.lean) derives **Corollaries 1-3 of [DV26]**
from the theorem, with the same axiom footprint:

1. **χ_f(ℝ²) > 4** (`four_lt_planeFractionalChromaticNumber`). The fractional chromatic number
   of the full, infinite unit-distance graph of the plane exceeds 4: fractional colorings of
   the plane are `ℝ≥0∞`-weightings of independent point sets, and any such coloring restricts
   to a fractional coloring of the finite graph produced by Component 1. A finitary form
   `four_lt_finitaryPlaneFractionalChromaticNumber` (`sup_G χ_f(G) > 4`) is also provided.
2. **χ(ℝ²) ≥ 5** (`five_le_planeGraph_chromaticNumber`, with `planeGraph_not_colorable_four`).
   The chromatic number of the plane is at least 5; de Grey's 2018 bound is recovered here
   because a proper 4-coloring of the plane would force χ_f ≤ 4 on every finite unit-distance
   graph.
3. **m₁(ℝ²) < 1/4** (`maxAvoidingDensity_lt_quarter`). Every measurable planar set avoiding
   unit distances has upper density below 1/4, uniformly. Proof: each translate of Theorem 1's
   graph `H` meets such a set in an independent set, so averaging over translates in a large
   ball bounds the density by `α(H)/|V(H)| < 1/4`.

## Repository layout

| File (in `UnitDistanceGraphs/`) | Role |
|---|---|
| [`Definitions.lean`](UnitDistanceGraphs/Definitions.lean) | Core definitions (`planeGraph`, `independenceRatio`, `χ_f`, `χ_gf`), the `χ_gf` lower-bound API with weak LP duality, and the enumeration `indepEnum`. |
| **Component 1** | *[M23] Theorem 1: first blow-up, via amenability* |
| [`PlaneColoring.lean`](UnitDistanceGraphs/PlaneColoring.lean) | A square-grid 9-coloring of the plane ⇒ every finite plane unit-distance graph has `χ_f ≤ 9` (`chi_f_le_nine`). |
| [`Folner.lean`](UnitDistanceGraphs/Folner.lean) | `solvable ⇒ FolnerCond` from scratch: closure under group extensions + abelian/cyclic/finite base cases. |
| [`FirstBlowUp.lean`](UnitDistanceGraphs/FirstBlowUp.lean) | `IsSolvable (ℂ ≃ᵢ ℂ)`, `exists_folner_set`, and the blow-up/averaging: `exists_chi_f_gt`. |
| **Component 2** | *[DV26] Lemma 1: the LP certificate (`chi_gf_G29_gt`)* |
| [`G29.lean`](UnitDistanceGraphs/G29.lean) | The graph `G29` (exact algebraic coordinates), its distance lemmas, and the interval-arithmetic toolkit. |
| [`G29Vertices.lean`](UnitDistanceGraphs/G29Vertices.lean) | The 29 vertices with injectivity, and the adjacency matrix `H` (`H_adj_iff`) — all by kernel-`decide` interval arithmetic. |
| [`PlaneIsometry.lean`](UnitDistanceGraphs/PlaneIsometry.lean) | Plane congruence-extension: equal pairwise distances ⇒ a single isometry (`congruent_of_dist_eq`). |
| [`CertificateData.lean`](UnitDistanceGraphs/CertificateData.lean) | The embedded certificate data: the 16859 congruences with their positional alignment lists, the integer dual witness, and the objective `certNum`/`certDen`. |
| [`CertificateVerification.lean`](UnitDistanceGraphs/CertificateVerification.lean) | All 16859 congruences (`hcong_all`), the bitmask per-atom feasibility (`feasBM`/`cert_per_atom`), and the final `chi_gf_G29_gt`. |
| **Component 3** | *[M23] Theorem 2: second blow-up* |
| [`SecondBlowUp.lean`](UnitDistanceGraphs/SecondBlowUp.lean) | Component 3 in full: the lattice cube (layers L1–L5a) and the assembly `exists_low_independence_ratio`. |
| **Top level** | |
| [`Main.lean`](UnitDistanceGraphs/Main.lean) | `exists_independenceRatio_lt_quarter`: Theorem 1, assembled from the three components. |
| [`Corollaries.lean`](UnitDistanceGraphs/Corollaries.lean) | Corollaries 1-3 of [DV26]: `χ_f(ℝ²) > 4`, `χ(ℝ²) ≥ 5`, `m₁(ℝ²) < 1/4`. |

## Attribution

The **mathematical results** formalized here are due to their original authors: Theorem 1 and
Lemma 1 (the LP certificate) are by **Ákos Dúcz and Dániel Varga** [DV26]; the two blow-up theorems
(Components 1 and 3) are by **Máté Matolcsi, Imre Z. Ruzsa, Dániel Varga and Pál Zsámboki** [M23]; the certificate data
comes from the [supplementary material](https://users.renyi.hu/~akos/ep1070/) published with
[DV26].

This repository contains the **Lean 4 formalization** of those results; any mistake in the
formalization is independent of the original proofs and not attributable to the papers' authors.
The formalization was developed with the assistance of Anthropic's Claude models.

[DV26]: https://arxiv.org/abs/2606.28157
[M23]: https://arxiv.org/abs/2311.10069
