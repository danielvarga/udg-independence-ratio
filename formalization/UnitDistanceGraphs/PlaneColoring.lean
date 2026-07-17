/-
A proper finite coloring of the plane avoiding unit distances, giving a uniform bound on the
fractional chromatic number of every finite unit-distance graph.

We use a square-grid `9`-coloring: color `z` by `(⌊z.re/s⌋ mod 3, ⌊z.im/s⌋ mod 3)` with `s = 7/10`.
Two points of the same color are never at distance exactly `1`: if they lie in the same grid cell
their squared distance is below `2s² = 49/50 < 1`; if they lie in different same-colored cells some
coordinate gap exceeds `2s = 7/5 > 1`. A proper `9`-coloring gives `χ_f ≤ 9`.
-/

import UnitDistanceGraphs.Definitions

namespace UnitDistanceGraphs

open Classical

noncomputable section

/-- The grid step of the coloring. -/
def gridStep : ℝ := 7 / 10

lemma gridStep_pos : 0 < gridStep := by unfold gridStep; norm_num

/-- The square-grid coloring of the plane with `9` colors. -/
def planeColoring (z : ℂ) : ZMod 3 × ZMod 3 :=
  ((⌊z.re / gridStep⌋ : ZMod 3), (⌊z.im / gridStep⌋ : ZMod 3))

lemma floor_mul_le (x : ℝ) : (⌊x / gridStep⌋ : ℝ) * gridStep ≤ x := by
  have h := Int.floor_le (x / gridStep)
  have := mul_le_mul_of_nonneg_right h (le_of_lt gridStep_pos)
  rwa [div_mul_cancel₀ _ (ne_of_gt gridStep_pos)] at this

lemma lt_floor_add_one_mul (x : ℝ) : x < ((⌊x / gridStep⌋ : ℝ) + 1) * gridStep := by
  have h := Int.lt_floor_add_one (x / gridStep)
  have := mul_lt_mul_of_pos_right h gridStep_pos
  rwa [div_mul_cancel₀ _ (ne_of_gt gridStep_pos)] at this

/-- Same-colored real coordinates that are within distance `1` lie in the same grid cell, so their
squared gap is below `gridStep²`. -/
lemma sq_sub_lt_of_color_eq {x y : ℝ}
    (h : (⌊x / gridStep⌋ : ZMod 3) = (⌊y / gridStep⌋ : ZMod 3)) (hxy : (x - y) ^ 2 ≤ 1) :
    (x - y) ^ 2 < gridStep ^ 2 := by
  set i := ⌊x / gridStep⌋ with hi
  set i' := ⌊y / gridStep⌋ with hi'
  have hs : gridStep = 7 / 10 := rfl
  -- floor coordinate bounds
  have hxl := floor_mul_le x
  have hxr := lt_floor_add_one_mul x
  have hyl := floor_mul_le y
  have hyr := lt_floor_add_one_mul y
  rw [← hi] at hxl hxr
  rw [← hi'] at hyl hyr
  rw [hs] at hxl hxr hyl hyr ⊢
  -- the floors are equal
  have hfe : i = i' := by
    by_contra hne
    have hdvd : (3 : ℤ) ∣ (i' - i) :=
      Int.ModEq.dvd ((ZMod.intCast_eq_intCast_iff i i' 3).mp h)
    have h3 : (3 : ℤ) ≤ |i' - i| :=
      Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))) ((dvd_abs _ _).mpr hdvd)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hge : (i' : ℝ) - i ≥ 3 := by
        have : (3 : ℤ) ≤ i' - i := by rw [abs_of_pos (by omega)] at h3; omega
        exact_mod_cast this
      have hyx : (7 / 5 : ℝ) < y - x := by nlinarith [hxr, hyl, hge]
      nlinarith [hyx, hxy]
    · have hge : (i : ℝ) - i' ≥ 3 := by
        have : (3 : ℤ) ≤ i - i' := by rw [abs_of_neg (by omega)] at h3; omega
        exact_mod_cast this
      have hxy' : (7 / 5 : ℝ) < x - y := by nlinarith [hxl, hyr, hge]
      nlinarith [hxy', hxy]
  -- same cell: |x - y| < gridStep
  rw [hfe] at hxl hxr
  nlinarith [hxl, hxr, hyl, hyr]

/-- The plane coloring is proper: same-colored points are never at unit distance. -/
lemma coloring_proper {z w : ℂ} (h : planeColoring z = planeColoring w) (hd : dist z w = 1) :
    False := by
  rw [planeColoring, planeColoring, Prod.mk.injEq] at h
  have hsq : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 1 := by
    have hd' := hd
    rw [Complex.dist_eq_re_im] at hd'
    have hnn : (0 : ℝ) ≤ (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by positivity
    rw [← Real.sq_sqrt hnn, hd']; norm_num
  have hre : (z.re - w.re) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (z.im - w.im)]
  have him : (z.im - w.im) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (z.re - w.re)]
  have hre' := sq_sub_lt_of_color_eq h.1 hre
  have him' := sq_sub_lt_of_color_eq h.2 him
  have hs : gridStep = 7 / 10 := rfl
  rw [hs] at hre' him'
  nlinarith [hre', him', hsq]

/-- **Uniform bound.** Every finite unit-distance graph in the plane has fractional chromatic
number at most `9`. -/
theorem chi_f_le_nine (G : UnitDistanceGraph) : fractionalChromaticNumber G ≤ 9 := by
  set colors := G.image planeColoring with hcolors
  set cls : ZMod 3 × ZMod 3 → Finset ℂ := fun a => G.filter (fun v => planeColoring v = a) with hcls
  -- each color class is an independent set
  have hclsindep : ∀ a ∈ colors, cls a ∈ indepSets G := by
    intro a _
    rw [indepSets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro z hz w hw _ hadj
    rw [Finset.mem_coe, hcls, Finset.mem_filter] at hz hw
    exact coloring_proper (hz.2.trans hw.2.symm) hadj
  set γ : Finset ℂ → ℝ := fun S => ((colors.filter (fun a => cls a = S)).card : ℝ) with hγ
  -- γ is a fractional coloring
  have hfeas : IsFractionalColoring G γ := by
    refine ⟨fun S _ => by simp only [hγ]; positivity, fun v hv => ?_⟩
    have hcvcolors : planeColoring v ∈ colors := Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hclsmem : cls (planeColoring v) ∈ (indepSets G).filter (fun S => {v} ⊆ S) := by
      rw [Finset.mem_filter]
      refine ⟨hclsindep _ hcvcolors, ?_⟩
      rw [Finset.singleton_subset_iff, hcls, Finset.mem_filter]
      exact ⟨hv, rfl⟩
    have hγpos : 1 ≤ γ (cls (planeColoring v)) := by
      simp only [hγ]
      have hmem : planeColoring v ∈ colors.filter (fun a => cls a = cls (planeColoring v)) :=
        Finset.mem_filter.mpr ⟨hcvcolors, rfl⟩
      have : 1 ≤ (colors.filter (fun a => cls a = cls (planeColoring v))).card :=
        Finset.card_pos.mpr ⟨planeColoring v, hmem⟩
      exact_mod_cast this
    calc (1 : ℝ) ≤ γ (cls (planeColoring v)) := hγpos
      _ ≤ marginal G γ {v} := Finset.single_le_sum (fun S _ => by simp only [hγ]; positivity) hclsmem
  -- weight of γ equals the number of colors used
  have hweight : weight G γ = (colors.card : ℝ) := by
    rw [weight]
    simp only [hγ]
    rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise hclsindep]
  have hcard : colors.card ≤ 9 := by
    calc colors.card ≤ Fintype.card (ZMod 3 × ZMod 3) := Finset.card_le_univ _
      _ = 9 := by rw [Fintype.card_prod, ZMod.card]
  have hbdd : BddBelow {w | ∃ γ', IsFractionalColoring G γ' ∧ weight G γ' = w} :=
    ⟨0, fun w hw => by
      obtain ⟨δ, hδ, rfl⟩ := hw
      exact Finset.sum_nonneg (fun S hS => hδ.nonneg S hS)⟩
  calc fractionalChromaticNumber G ≤ weight G γ := csInf_le hbdd ⟨γ, hfeas, rfl⟩
    _ = colors.card := hweight
    _ ≤ 9 := by exact_mod_cast hcard

end

end UnitDistanceGraphs
