/-
Corollaries 1–3 of Dúcz–Varga (2026), derived from Theorem 1 and its components.

* **Corollary 1** — `χ_f(ℝ²) > 4`: the fractional chromatic number of the full (infinite)
  unit-distance graph of the plane exceeds `4` (`four_lt_planeFractionalChromaticNumber`),
  together with its finitary form `four_lt_finitaryPlaneFractionalChromaticNumber`.
* **Corollary 2** — `χ(ℝ²) ≥ 5`: the chromatic number of the plane is at least `5`
  (`five_le_planeGraph_chromaticNumber`), recovering the de Grey bound from the fractional
  bound.
* **Corollary 3** — `m₁(ℝ²) < 1/4`: every measurable subset of the plane avoiding unit
  distances has upper density less than `1/4` (`maxAvoidingDensity_lt_quarter`), by an
  averaging argument against the graph of Theorem 1.

References:
* [DV26] arXiv:2606.28157, Corollaries 1–3.
-/

import UnitDistanceGraphs.Main

namespace UnitDistanceGraphs

open Classical Filter Metric MeasureTheory
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

/-! ### A proper plane coloring bounds `χ_f` of every finite unit-distance graph

The counting argument of `chi_f_le_nine`, generalized from the concrete square-grid
`9`-coloring to an arbitrary finite color type. It converts a proper coloring of the *plane*
into a fractional coloring of any finite `G`, so `χ_f G ≤ #colors`. -/

/-- If `c` colors the whole plane with a finite color type `κ` and no two points at distance `1`
share a color, then every finite unit-distance graph `G` has `χ_f G ≤ |κ|` (the color classes,
intersected with `G`, form an integral — hence fractional — coloring). -/
theorem chi_f_le_card_of_properColoring {κ : Type*} [Fintype κ] (c : ℂ → κ)
    (hc : ∀ z w : ℂ, dist z w = 1 → c z ≠ c w) (G : UnitDistanceGraph) :
    χ_f G ≤ Fintype.card κ := by
  set colors := G.image c with hcolors
  set cls : κ → Finset ℂ := fun a => G.filter (fun v => c v = a) with hcls
  -- each color class is an independent set
  have hclsindep : ∀ a ∈ colors, cls a ∈ indepSets G := by
    intro a _
    rw [indepSets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro z hz w hw _ hadj
    rw [Finset.mem_coe, hcls, Finset.mem_filter] at hz hw
    exact hc z w hadj (hz.2.trans hw.2.symm)
  set γ : Finset ℂ → ℝ := fun S => ((colors.filter (fun a => cls a = S)).card : ℝ) with hγ
  -- γ is a fractional coloring
  have hfeas : IsFractionalColoring G γ := by
    refine ⟨fun S _ => by simp only [hγ]; positivity, fun v hv => ?_⟩
    have hcvcolors : c v ∈ colors := Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hclsmem : cls (c v) ∈ (indepSets G).filter (fun S => {v} ⊆ S) := by
      rw [Finset.mem_filter]
      refine ⟨hclsindep _ hcvcolors, ?_⟩
      rw [Finset.singleton_subset_iff, hcls, Finset.mem_filter]
      exact ⟨hv, rfl⟩
    have hγpos : 1 ≤ γ (cls (c v)) := by
      simp only [hγ]
      have hmem : c v ∈ colors.filter (fun a => cls a = cls (c v)) :=
        Finset.mem_filter.mpr ⟨hcvcolors, rfl⟩
      have : 1 ≤ (colors.filter (fun a => cls a = cls (c v))).card :=
        Finset.card_pos.mpr ⟨c v, hmem⟩
      exact_mod_cast this
    calc (1 : ℝ) ≤ γ (cls (c v)) := hγpos
      _ ≤ marginal G γ {v} := Finset.single_le_sum (fun S _ => by simp only [hγ]; positivity) hclsmem
  -- weight of γ equals the number of colors used
  have hweight : weight G γ = (colors.card : ℝ) := by
    rw [weight]
    simp only [hγ]
    rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hclsindep]
  have hcard : colors.card ≤ Fintype.card κ := Finset.card_le_univ _
  have hbdd : BddBelow {w | ∃ γ', IsFractionalColoring G γ' ∧ weight G γ' = w} :=
    ⟨0, fun w hw => by
      obtain ⟨δ, hδ, rfl⟩ := hw
      exact Finset.sum_nonneg (fun S hS => hδ.nonneg S hS)⟩
  calc fractionalChromaticNumber G ≤ weight G γ := csInf_le hbdd ⟨γ, hfeas, rfl⟩
    _ = colors.card := hweight
    _ ≤ Fintype.card κ := by exact_mod_cast hcard

/-! ### Corollary 1 — `χ_f(ℝ²) > 4` -/

/-- The *finitary* fractional chromatic number of the plane: the supremum of `χ_f G` over all
finite unit-distance graphs `G` in the plane. (Bounded above by `9` via `chi_f_le_nine`, so the
real-valued supremum is honest.) -/
def finitaryPlaneFractionalChromaticNumber : ℝ :=
  ⨆ V : UnitDistanceGraph, χ_f V

/-- **Corollary 1 of [DV26], finitary form.** The finitary fractional chromatic number of the
plane exceeds `4`. -/
theorem four_lt_finitaryPlaneFractionalChromaticNumber :
    4 < finitaryPlaneFractionalChromaticNumber := by
  obtain ⟨V', hV'⟩ := exists_chi_f_gt G29 chi_gf_G29_gt
  have hbdd : BddAbove (Set.range fun V : UnitDistanceGraph => χ_f V) :=
    ⟨9, by rintro w ⟨V, rfl⟩; exact chi_f_le_nine V⟩
  exact lt_of_lt_of_le hV' (le_ciSup hbdd V')

/-- A fractional coloring of the *full, infinite* unit-distance graph of the plane:
`ℝ≥0∞`-valued weights on point sets, supported on independent sets (sets containing no two
points at distance `1`), whose total weight over the sets containing any given point is at
least `1`. (The `∑'` over the uncountable index is the `ℝ≥0∞`-tsum, i.e. the supremum of
finite subsums, so no summability hypothesis is needed.) -/
structure IsPlaneFractionalColoring (γ : Set ℂ → ℝ≥0∞) : Prop where
  indep : ∀ S : Set ℂ, γ S ≠ 0 → planeGraph.IsIndepSet S
  covers : ∀ x : ℂ, 1 ≤ ∑' S : {S : Set ℂ | x ∈ S}, γ S

/-- The fractional chromatic number `χ_f(ℝ²)` of the plane: the infimum of total weights of
fractional colorings of the full unit-distance graph of `ℂ`, valued in `ℝ≥0∞`. -/
def planeFractionalChromaticNumber : ℝ≥0∞ :=
  ⨅ (γ : Set ℂ → ℝ≥0∞) (_ : IsPlaneFractionalColoring γ), ∑' S, γ S

/-- **Restriction.** A fractional coloring of the whole plane restricts (by intersecting its
sets with `V` and pushing the weights forward) to a fractional coloring of any finite
unit-distance graph `V`, so `χ_f V` is a lower bound on its total weight. -/
theorem ofReal_chi_f_le_of_planeFractionalColoring (V : UnitDistanceGraph)
    {γ : Set ℂ → ℝ≥0∞} (hγ : IsPlaneFractionalColoring γ) :
    ENNReal.ofReal (χ_f V) ≤ ∑' S, γ S := by
  rcases eq_or_ne (∑' S, γ S) ⊤ with hWtop | hWtop
  · rw [hWtop]; exact le_top
  -- the restriction map and the fibre weights
  set g : Set ℂ → Finset ℂ := fun S => V.filter (fun v => v ∈ S) with hg
  set fib : Finset ℂ → ℝ≥0∞ := fun T => ∑' S : g ⁻¹' {T}, γ (S : Set ℂ) with hfib
  have hfibW : ∑' T, fib T = ∑' S, γ S := ENNReal.tsum_fiberwise γ g
  have hfib_ne_top : ∀ T, fib T ≠ ⊤ := fun T =>
    ne_top_of_le_ne_top hWtop (hfibW ▸ ENNReal.le_tsum T)
  -- fibre weights are supported on the independent sets of V
  have hfib_supp : ∀ T : Finset ℂ, fib T ≠ 0 → T ∈ indepSets V := by
    intro T hT
    have hex : ∃ S : g ⁻¹' {T}, γ (S : Set ℂ) ≠ 0 := by
      by_contra h
      push Not at h
      exact hT (by simp only [hfib]; exact ENNReal.tsum_eq_zero.mpr h)
    obtain ⟨⟨S, hST⟩, hS⟩ := hex
    have hgS : g S = T := hST
    rw [indepSets, Finset.mem_filter, Finset.mem_powerset, ← hgS]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    have hsub : (↑(g S) : Set ℂ) ⊆ S := fun z hz => (Finset.mem_filter.mp hz).2
    have hSind := hγ.indep S hS
    rw [SimpleGraph.isIndepSet_iff] at hSind ⊢
    exact hSind.mono hsub
  -- the covering condition transfers to the fibre weights
  have hmarg : ∀ x ∈ V,
      (1 : ℝ≥0∞) ≤ ∑ T ∈ (indepSets V).filter (fun T => x ∈ T), fib T := by
    intro x hxV
    have h1 : (1 : ℝ≥0∞) ≤ ∑' S : Set ℂ, ({S : Set ℂ | x ∈ S}).indicator γ S := by
      rw [← tsum_subtype]
      exact hγ.covers x
    have hinner : ∀ T : Finset ℂ,
        (∑' S : g ⁻¹' {T}, ({S : Set ℂ | x ∈ S}).indicator γ (S : Set ℂ))
          = if x ∈ T then fib T else 0 := by
      intro T
      by_cases hxT : x ∈ T
      · rw [if_pos hxT]
        simp only [hfib]
        refine tsum_congr fun ⟨S, hST⟩ => ?_
        have hgS : g S = T := hST
        have hxS : x ∈ S := by
          have hxg : x ∈ g S := by rw [hgS]; exact hxT
          exact (Finset.mem_filter.mp hxg).2
        exact Set.indicator_of_mem (show S ∈ {S : Set ℂ | x ∈ S} from hxS) γ
      · rw [if_neg hxT]
        refine ENNReal.tsum_eq_zero.mpr fun ⟨S, hST⟩ => ?_
        have hgS : g S = T := hST
        have hxS : x ∉ S := fun hxS =>
          hxT (by rw [← hgS]; exact Finset.mem_filter.mpr ⟨hxV, hxS⟩)
        exact Set.indicator_of_notMem (show S ∉ {S : Set ℂ | x ∈ S} from hxS) γ
    have hdec : (∑' S : Set ℂ, ({S : Set ℂ | x ∈ S}).indicator γ S)
        = ∑' T : Finset ℂ, (if x ∈ T then fib T else 0) := by
      rw [← ENNReal.tsum_fiberwise (fun S : Set ℂ => ({S : Set ℂ | x ∈ S}).indicator γ S) g]
      exact tsum_congr hinner
    have h2 := h1.trans_eq hdec
    have h3 : (∑' T : Finset ℂ, (if x ∈ T then fib T else 0))
        = ∑ T ∈ (indepSets V).filter (fun T => x ∈ T), fib T := by
      rw [Finset.sum_filter]
      refine tsum_eq_sum fun T hT => ?_
      by_cases hxT : x ∈ T
      · rw [if_pos hxT]
        by_contra hne
        exact hT (hfib_supp T hne)
      · rw [if_neg hxT]
    exact h3 ▸ h2
  -- assemble the induced real-valued fractional coloring of V
  set γ' : Finset ℂ → ℝ := fun T => (fib T).toReal with hγ'
  have hsum_le : ∑ T ∈ indepSets V, fib T ≤ ∑' S, γ S :=
    hfibW ▸ ENNReal.sum_le_tsum (indepSets V)
  have hsum_ne_top : (∑ T ∈ indepSets V, fib T) ≠ ⊤ := ne_top_of_le_ne_top hWtop hsum_le
  have hfrac : IsFractionalColoring V γ' := by
    refine ⟨fun S _ => ENNReal.toReal_nonneg, fun x hx => ?_⟩
    have hfilter_le : (∑ T ∈ (indepSets V).filter (fun T => x ∈ T), fib T)
        ≤ ∑ T ∈ indepSets V, fib T :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h1 := ENNReal.toReal_mono (ne_top_of_le_ne_top hsum_ne_top hfilter_le) (hmarg x hx)
    rw [ENNReal.toReal_one, ENNReal.toReal_sum (fun T _ => hfib_ne_top T)] at h1
    have hfe : (indepSets V).filter (fun S => {x} ⊆ S)
        = (indepSets V).filter (fun T => x ∈ T) :=
      Finset.filter_congr fun T _ => by rw [Finset.singleton_subset_iff]
    rw [marginal, hfe]
    exact h1
  have hchi : χ_f V ≤ (∑ T ∈ indepSets V, fib T).toReal := by
    have hwγ' : weight V γ' = (∑ T ∈ indepSets V, fib T).toReal := by
      rw [weight, ENNReal.toReal_sum (fun T _ => hfib_ne_top T)]
    have hbdd : BddBelow {w | ∃ γ0, IsFractionalColoring V γ0 ∧ weight V γ0 = w} :=
      ⟨0, fun w hw => by
        obtain ⟨δ, hδ, rfl⟩ := hw
        exact Finset.sum_nonneg (fun S hS => hδ.nonneg S hS)⟩
    calc χ_f V ≤ weight V γ' := csInf_le hbdd ⟨γ', hfrac, rfl⟩
      _ = _ := hwγ'
  calc ENNReal.ofReal (χ_f V) ≤ ENNReal.ofReal (∑ T ∈ indepSets V, fib T).toReal :=
        ENNReal.ofReal_le_ofReal hchi
    _ = ∑ T ∈ indepSets V, fib T := ENNReal.ofReal_toReal hsum_ne_top
    _ ≤ ∑' S, γ S := hsum_le

/-- **Corollary 1 of [DV26].** The fractional chromatic number of the plane exceeds `4`:
`χ_f(ℝ²) > 4`, for the full (infinite) unit-distance graph of the plane. -/
theorem four_lt_planeFractionalChromaticNumber :
    4 < planeFractionalChromaticNumber := by
  obtain ⟨V', hV'⟩ := exists_chi_f_gt G29 chi_gf_G29_gt
  have h4 : (4 : ℝ≥0∞) < ENNReal.ofReal (χ_f V') := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by simp]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans (by norm_num) hV')).mpr hV'
  exact lt_of_lt_of_le h4 (le_iInf fun γ => le_iInf fun hγ =>
    ofReal_chi_f_le_of_planeFractionalColoring V' hγ)

/-! ### Corollary 2 — `χ(ℝ²) ≥ 5` -/

/-- **Corollary 2 of [DV26], coloring form.** The plane admits no proper `4`-coloring:
`planeGraph` is not `4`-colorable. (First proved by de Grey (2018); here it falls out of the
fractional bound, since a proper `4`-coloring would force `χ_f ≤ 4` for every finite
unit-distance graph.) -/
theorem planeGraph_not_colorable_four : ¬ planeGraph.Colorable 4 := by
  rintro ⟨C⟩
  obtain ⟨V', hV'⟩ := exists_chi_f_gt G29 chi_gf_G29_gt
  have h := chi_f_le_card_of_properColoring C (fun z w hzw => C.valid hzw) V'
  rw [Fintype.card_fin] at h
  have h4 : χ_f V' ≤ 4 := by exact_mod_cast h
  linarith

/-- **Corollary 2 of [DV26].** The chromatic number of the plane is at least `5`:
`χ(ℝ²) ≥ 5`. -/
theorem five_le_planeGraph_chromaticNumber : 5 ≤ planeGraph.chromaticNumber := by
  have h5 : ((5 : ℕ) : ℕ∞) ≤ planeGraph.chromaticNumber := by
    rw [SimpleGraph.le_chromaticNumber_iff_colorable]
    intro m hm
    by_contra hlt
    push Not at hlt
    exact planeGraph_not_colorable_four (hm.mono (by omega))
  exact_mod_cast h5

/-! ### Corollary 3 — `m₁(ℝ²) < 1/4` -/

/-- A set of points in the plane is *1-avoiding* if it contains no two points at distance
exactly `1`. -/
def AvoidsUnitDistance (A : Set ℂ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, dist x y ≠ 1

/-- The upper (asymptotic) density of a set in the plane, along balls centered at the origin:
`limsup_{r → ∞} vol(A ∩ B_r) / vol(B_r)`, valued in `ℝ≥0∞`. -/
def upperDensity (A : Set ℂ) : ℝ≥0∞ :=
  limsup (fun r : ℝ => volume (A ∩ ball (0 : ℂ) r) / volume (ball (0 : ℂ) r)) atTop

/-- `m₁(ℝ²)`: the supremum of the upper densities of measurable 1-avoiding subsets of the
plane. -/
def maxAvoidingDensity : ℝ≥0∞ :=
  ⨆ (A : Set ℂ) (_ : MeasurableSet A) (_ : AvoidsUnitDistance A), upperDensity A

/-- **The averaging bound.** Every measurable 1-avoiding set has upper density at most the
independence ratio `α(H)/|V(H)|` of *any* nonempty finite unit-distance graph `H`: each
translate `H + x` meets `A` in (a translate of) an independent set of `H`, and integrating
this count over a large ball compares `|V(H)| · vol(A ∩ B_r)` with `α(H) · vol(B_{r+k})`. -/
theorem upperDensity_le_independenceRatio (H : UnitDistanceGraph) (hne : H.Nonempty)
    {A : Set ℂ} (hA : MeasurableSet A) (hAv : AvoidsUnitDistance A) :
    upperDensity A ≤ (indepNum H : ℝ≥0∞) / (H.card : ℝ≥0∞) := by
  set k : ℝ := H.sup' hne (fun v => ‖v‖) with hk
  have hk0 : 0 ≤ k := by
    obtain ⟨v, hv⟩ := hne
    exact le_trans (norm_nonneg v) (Finset.le_sup' _ hv)
  have hvk : ∀ v ∈ H, ‖v‖ ≤ k := fun v hv => Finset.le_sup' _ hv
  -- pointwise: every translate of H meets A in an independent set
  have hcount : ∀ x : ℂ,
      (∑ v ∈ H, A.indicator (1 : ℂ → ℝ≥0∞) (v + x)) ≤ (indepNum H : ℝ≥0∞) := by
    intro x
    have hmem : H.filter (fun v => v + x ∈ A) ∈ indepSets H := by
      rw [indepSets, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      rw [SimpleGraph.isIndepSet_iff]
      intro z hz w hw _ hadj
      rw [Finset.mem_coe, Finset.mem_filter] at hz hw
      refine hAv (z + x) hz.2 (w + x) hw.2 ?_
      rw [dist_add_right]
      exact hadj
    have hcard : (H.filter (fun v => v + x ∈ A)).card ≤ indepNum H :=
      Finset.le_sup (f := Finset.card) hmem
    calc (∑ v ∈ H, A.indicator (1 : ℂ → ℝ≥0∞) (v + x))
        = ((H.filter fun v => v + x ∈ A).card : ℝ≥0∞) := by
          rw [← Finset.sum_boole]
          exact Finset.sum_congr rfl fun v _ => by
            by_cases hv : v + x ∈ A <;> simp [hv]
      _ ≤ (indepNum H : ℝ≥0∞) := by exact_mod_cast hcard
  -- the key integrated bound
  have key : ∀ r : ℝ, (H.card : ℝ≥0∞) * volume (A ∩ ball (0 : ℂ) r)
      ≤ (indepNum H : ℝ≥0∞) * volume (ball (0 : ℂ) (r + k)) := by
    intro r
    have hmeas : ∀ v : ℂ, Measurable (fun x : ℂ => A.indicator (1 : ℂ → ℝ≥0∞) (v + x)) :=
      fun v => (measurable_one.indicator hA).comp (measurable_const_add v)
    -- each translate integrates to the volume of A in a shifted ball
    have htrans : ∀ v : ℂ,
        (∫⁻ x in ball (0 : ℂ) (r + k), A.indicator (1 : ℂ → ℝ≥0∞) (v + x) ∂volume)
          = volume (A ∩ ball v (r + k)) := by
      intro v
      have hpre : MeasurableSet ((fun x : ℂ => v + x) ⁻¹' A) :=
        hA.preimage (measurable_const_add v)
      have h1 : (fun x : ℂ => A.indicator (1 : ℂ → ℝ≥0∞) (v + x))
          = ((fun x : ℂ => v + x) ⁻¹' A).indicator (1 : ℂ → ℝ≥0∞) := by
        funext x
        by_cases hx : v + x ∈ A <;> simp [hx]
      rw [h1, lintegral_indicator_one hpre, Measure.restrict_apply hpre]
      have h2 : (fun x : ℂ => v + x) ⁻¹' A ∩ ball (0 : ℂ) (r + k)
          = (fun x : ℂ => v + x) ⁻¹' (A ∩ ball v (r + k)) := by
        rw [Set.preimage_inter]
        congr 1
        ext x
        simp [Metric.mem_ball, dist_eq_norm]
      rw [h2, measure_preimage_add]
    calc (H.card : ℝ≥0∞) * volume (A ∩ ball (0 : ℂ) r)
        = ∑ _v ∈ H, volume (A ∩ ball (0 : ℂ) r) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ v ∈ H, volume (A ∩ ball v (r + k)) := by
          refine Finset.sum_le_sum fun v hv => measure_mono (Set.inter_subset_inter_right _ ?_)
          refine ball_subset_ball' ?_
          rw [dist_zero_left]
          linarith [hvk v hv]
      _ = ∑ v ∈ H, ∫⁻ x in ball (0 : ℂ) (r + k), A.indicator (1 : ℂ → ℝ≥0∞) (v + x) ∂volume :=
          Finset.sum_congr rfl fun v _ => (htrans v).symm
      _ = ∫⁻ x in ball (0 : ℂ) (r + k), ∑ v ∈ H, A.indicator (1 : ℂ → ℝ≥0∞) (v + x) ∂volume :=
          (lintegral_finsetSum _ (fun v _ => hmeas v)).symm
      _ ≤ ∫⁻ _x in ball (0 : ℂ) (r + k), (indepNum H : ℝ≥0∞) ∂volume :=
          lintegral_mono fun x => hcount x
      _ = (indepNum H : ℝ≥0∞) * volume (ball (0 : ℂ) (r + k)) := setLIntegral_const _ _
  -- pass to densities
  set c : ℝ≥0∞ := (indepNum H : ℝ≥0∞) / (H.card : ℝ≥0∞) with hc
  have hcard0 : (H.card : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hne).ne'
  have hcardtop : (H.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hev : ∀ᶠ r in atTop, volume (A ∩ ball (0 : ℂ) r) / volume (ball (0 : ℂ) r)
      ≤ c * (volume (ball (0 : ℂ) (r + k)) / volume (ball (0 : ℂ) r)) := by
    refine Eventually.of_forall fun r => ?_
    have h1 : volume (A ∩ ball (0 : ℂ) r) ≤ c * volume (ball (0 : ℂ) (r + k)) := by
      have hrw : c * volume (ball (0 : ℂ) (r + k))
          = ((indepNum H : ℝ≥0∞) * volume (ball (0 : ℂ) (r + k))) / (H.card : ℝ≥0∞) := by
        rw [hc, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
      rw [hrw, ENNReal.le_div_iff_mul_le (Or.inl hcard0) (Or.inl hcardtop), mul_comm]
      exact key r
    calc volume (A ∩ ball (0 : ℂ) r) / volume (ball (0 : ℂ) r)
        ≤ (c * volume (ball (0 : ℂ) (r + k))) / volume (ball (0 : ℂ) r) :=
          ENNReal.div_le_div_right h1 _
      _ = c * (volume (ball (0 : ℂ) (r + k)) / volume (ball (0 : ℂ) r)) := by
          rw [mul_div_assoc]
  -- the ratio of ball volumes tends to 1
  have hratio : Tendsto (fun r : ℝ => volume (ball (0 : ℂ) (r + k)) / volume (ball (0 : ℂ) r))
      atTop (𝓝 1) := by
    have h0 : Tendsto (fun r : ℝ => k / r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have h1 : Tendsto (fun r : ℝ => (1 + k / r) ^ 2) atTop (𝓝 1) := by
      have := (tendsto_const_nhds.add h0).pow 2 (l := atTop) (f := fun r : ℝ => 1 + k / r)
      simpa using this
    have hoR : Tendsto (fun r : ℝ => ENNReal.ofReal ((1 + k / r) ^ 2)) atTop (𝓝 1) := by
      simpa using ENNReal.tendsto_ofReal h1
    refine hoR.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hrk : (0 : ℝ) ≤ r + k := by linarith
    rw [Complex.volume_ball, Complex.volume_ball,
      ENNReal.mul_div_mul_right _ _ (ENNReal.coe_ne_zero.mpr NNReal.pi_ne_zero)
        ENNReal.coe_ne_top,
      ← ENNReal.ofReal_pow hrk, ← ENNReal.ofReal_pow hr.le,
      ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    field_simp
  have hlim : Tendsto (fun r : ℝ => c * (volume (ball (0 : ℂ) (r + k)) / volume (ball (0 : ℂ) r)))
      atTop (𝓝 c) := by
    have := ENNReal.Tendsto.const_mul (a := c) hratio (Or.inl one_ne_zero)
    simpa using this
  exact le_of_le_of_eq (limsup_le_limsup hev) hlim.limsup_eq

/-- **Corollary 3 of [DV26].** `m₁(ℝ²) < 1/4`: the supremum of the upper densities of
measurable 1-avoiding subsets of the plane is strictly below `1/4` — every measurable set
avoiding unit distances misses a *uniform* positive fraction beyond `3/4` of the plane,
another conjecture of Erdős. -/
theorem maxAvoidingDensity_lt_quarter : maxAvoidingDensity < 1 / 4 := by
  obtain ⟨H, hne, hratio⟩ := exists_independenceRatio_lt_quarter
  have hcard0 : 0 < H.card := Finset.card_pos.mpr hne
  -- the rational independence-ratio bound, as a natural-number inequality
  have hnat : 4 * indepNum H < H.card := by
    rw [independenceRatio, div_lt_iff₀ (by exact_mod_cast hcard0)] at hratio
    have h4 : (4 * indepNum H : ℚ) < H.card := by linarith
    exact_mod_cast h4
  have hbound : (indepNum H : ℝ≥0∞) / (H.card : ℝ≥0∞) < 1 / 4 := by
    rw [ENNReal.div_lt_iff (Or.inl (Nat.cast_ne_zero.mpr hcard0.ne'))
      (Or.inl (ENNReal.natCast_ne_top _))]
    rw [show (1 / 4 : ℝ≥0∞) * (H.card : ℝ≥0∞) = (H.card : ℝ≥0∞) / 4 by
      rw [one_div, div_eq_mul_inv, mul_comm]]
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    calc (indepNum H : ℝ≥0∞) * 4 = ((4 * indepNum H : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ < (H.card : ℝ≥0∞) := by exact_mod_cast hnat
  refine lt_of_le_of_lt ?_ hbound
  exact iSup_le fun A => iSup_le fun hA => iSup_le fun hAv =>
    upperDensity_le_independenceRatio H hne hA hAv

end

end UnitDistanceGraphs
