/-
Core definitions for the formalization of Theorem 1 of Dúcz–Varga (2026).

We work in the complex plane `ℂ ≅ ℝ²`. A *finite unit-distance graph* is given by a
finite vertex set `V : Finset ℂ`; two vertices are adjacent iff they are at Euclidean
distance exactly `1` (`planeGraph` below). We define the independence number and
independence ratio of such a graph, the fractional chromatic number `χ_f`, and the
geometric fractional chromatic number `χ_gf` of Matolcsi–Ruzsa–Varga–Zsámboki (2023).

References:
* [M23] arXiv:2311.10069, definitions of `χ_f` and `χ_gf`.
* [DV26] arXiv:2606.28157, Theorem 1.
-/

import Mathlib

namespace UnitDistanceGraphs

open Classical
open scoped BigOperators

noncomputable section

/-- The unit-distance graph of the plane: vertices are points of `ℂ`, and two points are
adjacent iff they are at Euclidean distance exactly `1`. A finite unit-distance graph is the
subgraph induced on a finite vertex set `V : Finset ℂ`. -/
def planeGraph : SimpleGraph ℂ where
  Adj z w := dist z w = 1
  symm := ⟨fun _ _ h => by rwa [dist_comm]⟩
  loopless := ⟨fun z h => by simp only [dist_self] at h; exact zero_ne_one h⟩

/-- A finite unit-distance graph in the plane, identified with its vertex set.
Adjacency is given by `planeGraph` (Euclidean distance `1`). -/
abbrev UnitDistanceGraph := Finset ℂ

variable (V : UnitDistanceGraph)

/-- The independent sets `ℐ(G)` of the finite unit-distance graph `V`: subsets of `V` no two
of whose (distinct) points are at distance `1`. -/
def indepSets : Finset (Finset ℂ) :=
  V.powerset.filter (fun S => planeGraph.IsIndepSet (↑S : Set ℂ))

/-- The independence number `α(G)`: the largest size of an independent subset of `V`. -/
def indepNum : ℕ :=
  (indepSets V).sup Finset.card

/-- The independence ratio `α(G) / |V(G)|`. -/
def independenceRatio : ℚ :=
  (indepNum V : ℚ) / (V.card : ℚ)

/-- Singletons of vertices are independent sets. -/
lemma singleton_mem_indepSets {G : UnitDistanceGraph} {v : ℂ} (hv : v ∈ G) :
    ({v} : Finset ℂ) ∈ indepSets G := by
  unfold indepSets
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨Finset.singleton_subset_iff.mpr hv, ?_⟩
  rw [Finset.coe_singleton]
  exact Set.pairwise_singleton _ _

/-! ### Fractional colorings -/

/-- The marginal weight a coloring `γ` places on independent sets containing a given subset `Y`:
`m(Y) = ∑_{S ∈ ℐ(G), Y ⊆ S} γ(S)`. For a singleton `Y = {x}` this is the total weight covering
the vertex `x`. -/
def marginal (γ : Finset ℂ → ℝ) (Y : Finset ℂ) : ℝ :=
  ∑ S ∈ (indepSets V).filter (fun S => Y ⊆ S), γ S

/-- The total weight `∑_{S ∈ ℐ(G)} γ(S)` of a coloring — the LP objective. -/
def weight (γ : Finset ℂ → ℝ) : ℝ :=
  ∑ S ∈ indepSets V, γ S

/-- A *fractional coloring* of `V`: nonnegative weights on independent sets covering every
vertex with total weight at least `1`. -/
structure IsFractionalColoring (γ : Finset ℂ → ℝ) : Prop where
  nonneg : ∀ S ∈ indepSets V, 0 ≤ γ S
  covers : ∀ x ∈ V, 1 ≤ marginal V γ {x}

/-- The fractional chromatic number `χ_f(G) = min_γ ∑_{S} γ(S)` over fractional colorings. -/
def fractionalChromaticNumber : ℝ :=
  sInf { w | ∃ γ, IsFractionalColoring V γ ∧ weight V γ = w }

/-! ### Geometric congruence and the geometric fractional chromatic number -/

/-- Two finite point sets in the plane are *congruent* if some Euclidean isometry of `ℂ`
(rotation, translation, reflection, or a composition) maps one onto the other. -/
def Congruent (Y Y' : Finset ℂ) : Prop :=
  ∃ φ : ℂ ≃ᵢ ℂ, Y' = Y.image (φ : ℂ → ℂ)

/-- A *geometric fractional coloring* is a fractional coloring whose marginals agree on
congruent subsets of `V`: `m(Y) = m(Y')` whenever `Y, Y' ⊆ V` are congruent. This encodes the
symmetry of the plane's isometry group. -/
structure IsGeometricFractionalColoring (γ : Finset ℂ → ℝ) : Prop
    extends IsFractionalColoring V γ where
  geometric : ∀ Y ∈ V.powerset, ∀ Y' ∈ V.powerset,
    Congruent Y Y' → marginal V γ Y = marginal V γ Y'

/-- The geometric fractional chromatic number `χ_gf(G) = min_γ ∑_{S} γ(S)` over geometric
fractional colorings. This is the quantity bounded below by the LP certificate of [DV26]. -/
def geomFractionalChromaticNumber : ℝ :=
  sInf { w | ∃ γ, IsGeometricFractionalColoring V γ ∧ weight V γ = w }

@[inherit_doc] scoped notation "χ_f" => fractionalChromaticNumber
@[inherit_doc] scoped notation "χ_gf" => geomFractionalChromaticNumber

/-! ### Lower bound API for `χ_gf`

The LP certificate of [DV26] establishes that *every* geometric fractional coloring of `G₂₉`
has weight `> 4.0007`. To turn such a statement into the bound `χ_gf(G₂₉) > 4.0007`, we use
that `χ_gf` is an infimum: a value `c` lying below the weight of every (geometric) coloring is a
lower bound for the infimum, provided at least one coloring exists. -/

/-- The set of attainable weights of geometric fractional colorings of `V`. `χ_gf V` is its
infimum. -/
def geomColoringWeights : Set ℝ :=
  { w | ∃ γ, IsGeometricFractionalColoring V γ ∧ weight V γ = w }

variable {V}

/-- **Lower bound for `χ_gf`.** If some geometric fractional coloring of `V` exists, and every
geometric fractional coloring has weight at least `c`, then `c ≤ χ_gf V`. This is the form in
which the LP certificate (Lemma 1 of [DV26]) is consumed. -/
theorem le_geomFractionalChromaticNumber {c : ℝ}
    (hne : ∃ γ, IsGeometricFractionalColoring V γ)
    (hlb : ∀ γ, IsGeometricFractionalColoring V γ → c ≤ weight V γ) :
    c ≤ χ_gf V := by
  apply le_csInf
  · obtain ⟨γ, hγ⟩ := hne
    exact ⟨weight V γ, γ, hγ, rfl⟩
  · rintro w ⟨γ, hγ, rfl⟩
    exact hlb γ hγ

end

/-- **Weak LP duality for `χ_gf` (dual certificate ⟹ lower bound).**

Suppose `V` has a distinguished covered vertex `v0`, a finite family of *genuine* congruences
`(L i, R i)` of `V`, dual weights `y i`, and a target `c ≥ 0`, and suppose the dual-feasibility
inequality holds at every independent set `S`:
`c · [v0 ∈ S] ≤ (∑ i, y i · ([L i ⊆ S] − [R i ⊆ S])) + 1`.
Then `c ≤ χ_gf V`.

This is the rigorous core of the LP-certificate method: it turns the arithmetic feasibility check
(`hfeas`) and the geometric facts (the `L i, R i` are actual congruences) into the bound. Proof:
sum `hfeas` over independent sets `S`, weighted by any geometric coloring `γ`; the geometric
constraints kill the `∑ i`-term (`marginal (L i) = marginal (R i)`), leaving
`c · marginal {v0} ≤ weight γ`, and `marginal {v0} ≥ 1` by covering. -/
theorem geomFractionalChromaticNumber_ge_of_dual
    {V : UnitDistanceGraph} {v0 : ℂ} (hv0 : v0 ∈ V)
    {ι : Type*} [Fintype ι] {L R : ι → Finset ℂ}
    (hLV : ∀ i, L i ⊆ V) (hRV : ∀ i, R i ⊆ V) (hcong : ∀ i, Congruent (L i) (R i))
    {y : ι → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hne : ∃ γ : Finset ℂ → ℝ, IsGeometricFractionalColoring V γ)
    (hfeas : ∀ S ∈ indepSets V,
      c * (if v0 ∈ S then (1 : ℝ) else 0)
        ≤ (∑ i, y i * ((if L i ⊆ S then (1 : ℝ) else 0) - (if R i ⊆ S then 1 else 0))) + 1) :
    c ≤ χ_gf V := by
  refine le_geomFractionalChromaticNumber hne (fun γ hγ => ?_)
  -- marginal as a sum with an indicator
  have hmarg : ∀ Y : Finset ℂ,
      (∑ S ∈ indepSets V, γ S * (if Y ⊆ S then (1 : ℝ) else 0)) = marginal V γ Y := by
    intro Y; unfold marginal; rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun S _ => by rw [mul_ite, mul_one, mul_zero])
  -- sum the feasibility inequality, weighted by γ S ≥ 0
  have hsum := Finset.sum_le_sum (fun S (hS : S ∈ indepSets V) =>
    mul_le_mul_of_nonneg_left (hfeas S hS) (hγ.nonneg S hS))
  -- left side collapses to c * marginal {v0}
  have hLHS : (∑ S ∈ indepSets V, γ S * (c * (if v0 ∈ S then (1 : ℝ) else 0)))
      = c * marginal V γ {v0} := by
    rw [← hmarg {v0}, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases h : v0 ∈ S
    · rw [if_pos h, if_pos (Finset.singleton_subset_iff.mpr h)]; ring
    · rw [if_neg h, if_neg (fun hsub => h (Finset.singleton_subset_iff.mp hsub))]; ring
  -- right side collapses to weight γ (the ∑ i term vanishes by the geometric constraints)
  have hRHS : (∑ S ∈ indepSets V,
        γ S * ((∑ i, y i * ((if L i ⊆ S then (1 : ℝ) else 0) - (if R i ⊆ S then 1 else 0))) + 1))
      = weight V γ := by
    have e1 : ∀ S, γ S * ((∑ i, y i * ((if L i ⊆ S then (1 : ℝ) else 0)
          - (if R i ⊆ S then 1 else 0))) + 1)
        = (∑ i, y i * (γ S * (if L i ⊆ S then (1 : ℝ) else 0)
            - γ S * (if R i ⊆ S then 1 else 0))) + γ S := by
      intro S
      rw [mul_add, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by ring)
    simp_rw [e1]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have hzero : (∑ i, ∑ S ∈ indepSets V,
        y i * (γ S * (if L i ⊆ S then (1 : ℝ) else 0) - γ S * (if R i ⊆ S then 1 else 0))) = 0 := by
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [← Finset.mul_sum]
      have : (∑ S ∈ indepSets V, (γ S * (if L i ⊆ S then (1 : ℝ) else 0)
            - γ S * (if R i ⊆ S then 1 else 0)))
          = marginal V γ (L i) - marginal V γ (R i) := by
        rw [Finset.sum_sub_distrib, hmarg, hmarg]
      rw [this, hγ.geometric (L i) (Finset.mem_powerset.mpr (hLV i)) (R i)
        (Finset.mem_powerset.mpr (hRV i)) (hcong i), sub_self, mul_zero]
    rw [hzero, zero_add, weight]
  rw [hLHS, hRHS] at hsum
  calc c = c * 1 := (mul_one c).symm
    _ ≤ c * marginal V γ {v0} := mul_le_mul_of_nonneg_left (hγ.covers v0 hv0) hc
    _ ≤ weight V γ := hsum

/- **[DV26] Lemma 1** (`chi_gf_G29_gt : 4 < χ_gf G₂₉`) is assembled downstream in `CertificateVerification.lean`,
which has access to the vertex enumeration (`G29Vertices`) and the arithmetic certificate
(`CertificateData`). It cannot live here: its proof needs `vtx`/`H` from `G29Vertices`, which
imports this file. This file provides the reusable pieces it consumes:
`geomFractionalChromaticNumber_ge_of_dual` (weak duality) and `indepSets_eq_image_indepEnum` (the
enumeration bridge). -/

/-! ### Computable enumeration of independent sets

Structural core of the completeness bridge for Component 2.

To run the `native_decide`-verified per-atom certificate (`feasBM`/`cert_per_atom` in `CertificateVerification.lean`)
against the *geometric* `indepSets G₂₉`, one must know that `indepSets G₂₉` is exactly the enumerated
atom list — the *completeness* direction. The obstacle is that `indepSets V = V.powerset.filter
IsIndepSet` ranges over the `2^|V|` powerset, which cannot be enumerated for `|V| = 29`.

This file removes that obstacle abstractly:

* `indepEnum G l` builds the independent subsets of a vertex list incrementally (the same breadth-first
  scheme mirrored on bitmasks by `indepEnumBM` in `CertificateVerification.lean`);
* `indepEnum_eq` proves it equals `l.toFinset.powerset.filter IsIndepSet`, by induction on `l` —
  never materializing the powerset;
* `indepEnum_map` shows it commutes with a vertex relabelling `f`, so a *computable* `Fin n` graph
  (Bool adjacency matrix) can stand in for the non-computable `planeGraph` by pulling back along the
  enumeration `Fin n → ℂ`.

Instantiated at the 29 vertices of `G₂₉` (with a decidable adjacency matching the real `dist = 1`
relation, via the distance lemmas in `G29.lean`), this pins `indepSets G₂₉` to the finite
enumeration. -/

section
open Finset
open scoped Classical

variable {α : Type*} [DecidableEq α]

/-- Recursive enumeration of the independent subsets of a vertex list: at each new vertex `v`, keep
all previous independent sets, and add `v` to those containing no neighbour of `v`. -/
def indepEnum (G : SimpleGraph α) [DecidableRel G.Adj] : List α → Finset (Finset α)
  | [] => {∅}
  | v :: vs =>
      indepEnum G vs ∪ ((indepEnum G vs).filter (fun S => ∀ w ∈ S, ¬ G.Adj v w)).image (insert v)

/-- Independence of `insert v T` (for `v ∉ T`): `T` is independent and `v` has no neighbour in `T`. -/
lemma isIndepSet_coe_insert (G : SimpleGraph α) (v : α) (T : Finset α) (hvT : v ∉ T) :
    G.IsIndepSet (↑(insert v T)) ↔ G.IsIndepSet (↑T) ∧ ∀ w ∈ T, ¬ G.Adj v w := by
  haveI : Std.Symm (fun a b : α => ¬ G.Adj a b) := ⟨fun _ _ h hba => h hba.symm⟩
  rw [SimpleGraph.isIndepSet_iff, SimpleGraph.isIndepSet_iff, Finset.coe_insert,
      Set.pairwise_insert_of_symm_of_notMem (by simpa using hvT)]
  simp only [Finset.mem_coe]

/-- **Completeness of the enumeration.** For a `Nodup` vertex list, the recursive enumeration is
exactly the set of independent subsets — proved by induction, without enumerating the `2^|l|`
powerset. -/
lemma indepEnum_eq (G : SimpleGraph α) [DecidableRel G.Adj] (l : List α) (hl : l.Nodup) :
    indepEnum G l = (l.toFinset.powerset).filter (fun (S : Finset α) => G.IsIndepSet (↑S : Set α)) := by
  induction l with
  | nil =>
    simp only [indepEnum, List.toFinset_nil, Finset.powerset_empty, Finset.filter_singleton]
    simp [SimpleGraph.isIndepSet_iff]
  | cons v vs ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨hv, hvs⟩ := hl
    have hvfin : v ∉ vs.toFinset := by simpa using hv
    ext S
    simp only [indepEnum, ih hvs, List.toFinset_cons, Finset.powerset_insert,
               Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_powerset]
    constructor
    · rintro (⟨hSmem, hSind⟩ | ⟨T, ⟨⟨hTmem, hTind⟩, hTadj⟩, rfl⟩)
      · exact ⟨Or.inl hSmem, hSind⟩
      · have hvT : v ∉ T := fun h => hvfin (hTmem h)
        exact ⟨Or.inr ⟨T, hTmem, rfl⟩, (isIndepSet_coe_insert G v T hvT).mpr ⟨hTind, hTadj⟩⟩
    · rintro ⟨hSmem | ⟨T, hTmem, rfl⟩, hSind⟩
      · exact Or.inl ⟨hSmem, hSind⟩
      · have hvT : v ∉ T := fun h => hvfin (hTmem h)
        obtain ⟨hTind, hTadj⟩ := (isIndepSet_coe_insert G v T hvT).mp hSind
        exact Or.inr ⟨T, ⟨⟨hTmem, hTind⟩, hTadj⟩, rfl⟩

/-- **`indepEnum` commutes with a vertex relabelling.** Pulling back along an enumeration
`f : Fin n → ℂ` lets a *computable* `Fin n` graph (Bool adjacency matrix) stand in for the
non-computable `planeGraph`: `indepEnum` on the ℂ-image equals the `Fin n` enumeration, imaged. -/
lemma indepEnum_map {β : Type*} [DecidableEq β] (f : α → β)
    (G : SimpleGraph β) [DecidableRel G.Adj] (l : List α) :
    indepEnum G (l.map f) = (indepEnum (G.comap f) l).image (Finset.image f) := by
  induction l with
  | nil => simp [indepEnum]
  | cons a vs ih =>
    ext S
    simp only [List.map_cons, indepEnum, ih, Finset.mem_union, Finset.mem_image,
      Finset.mem_filter, SimpleGraph.comap_adj]
    constructor
    · rintro (⟨T, hT, rfl⟩ | ⟨S', ⟨⟨T, hT, rfl⟩, hcond⟩, rfl⟩)
      · exact ⟨T, Or.inl hT, rfl⟩
      · refine ⟨insert a T, Or.inr ⟨T, ⟨hT, ?_⟩, rfl⟩, ?_⟩
        · intro w hw; exact hcond (f w) (Finset.mem_image_of_mem f hw)
        · rw [Finset.image_insert]
    · rintro ⟨T, (hT | ⟨T', ⟨hT', hcond⟩, rfl⟩), rfl⟩
      · exact Or.inl ⟨T, hT, rfl⟩
      · refine Or.inr ⟨Finset.image f T', ⟨⟨T', hT', rfl⟩, ?_⟩, ?_⟩
        · intro w hw
          rw [Finset.mem_image] at hw; obtain ⟨x, hx, rfl⟩ := hw
          exact hcond x hx
        · rw [Finset.image_insert]

/-- **`indepEnum` depends only on the adjacency relation.** Lets a *computable* Bool-matrix graph on
`Fin n` replace the (Classical-`Decidable`) `planeGraph.comap vtx`, which agrees with it. -/
lemma indepEnum_congr {G G' : SimpleGraph α} [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (h : ∀ v w, G.Adj v w ↔ G'.Adj v w) (l : List α) :
    indepEnum G l = indepEnum G' l := by
  induction l with
  | nil => simp only [indepEnum]
  | cons v vs ih =>
    simp only [indepEnum, ih]
    congr 1
    apply congrArg (Finset.image (insert v))
    apply Finset.filter_congr
    intro S _
    simp only [h]
end


/-- **Completeness, applied to the plane graph.** For any `Nodup` list of points, `indepSets` of
their finset is exactly the recursive enumeration `indepEnum planeGraph`. Instantiating at the 29
vertices of `G₂₉` reduces `indepSets G₂₉` to a finite enumeration (no `2²⁹` powerset). -/
lemma indepSets_eq_indepEnum (l : List ℂ) (hl : l.Nodup) :
    indepSets l.toFinset = indepEnum planeGraph l := by
  unfold indepSets
  exact (indepEnum_eq planeGraph l hl).symm

/-- **Wiring `indepSets` to a computable `Fin n` graph.** If `f : Fin n → ℂ` is an injective
enumeration of `V` and a decidable Bool-matrix graph `H` on `Fin n` has the same adjacency as
`planeGraph` pulled back along `f`, then `indepSets V` is the image, under `Finset.image f`, of the
*computable* enumeration `indepEnum H (finRange n)`. Applied to `G₂₉` (with `f = vtx` and `H` the
adjacency matrix), this reduces `indepSets G₂₉` to the certificate's atom set. -/
lemma indepSets_eq_image_indepEnum {n : ℕ} (V : Finset ℂ) (f : Fin n → ℂ)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (hf : Function.Injective f)
    (hV : V = ((List.finRange n).map f).toFinset)
    (hadj : ∀ i j, H.Adj i j ↔ planeGraph.Adj (f i) (f j)) :
    indepSets V = (indepEnum H (List.finRange n)).image (Finset.image f) := by
  have hHeq : ∀ i j, (planeGraph.comap f).Adj i j ↔ H.Adj i j := by
    intro i j; rw [SimpleGraph.comap_adj]; exact (hadj i j).symm
  rw [hV, indepSets_eq_indepEnum _ ((List.nodup_finRange n).map hf), indepEnum_map]
  refine congrArg (Finset.image (Finset.image f)) ?_
  exact indepEnum_congr hHeq _

end UnitDistanceGraphs
