/-
Explicit plane isometries `ℂ ≃ᵢ ℂ`, the building blocks for the congruence obligations `hcong` of
Component 2, culminating in the reusable plane congruence-extension lemma `congruent_of_dist_eq`.

Every Euclidean isometry of the plane is `z ↦ u·z + t` (orientation-preserving) or
`z ↦ u·z̄ + t` (orientation-reversing) for a unit `u` and a translation `t`. We bundle both as
`IsometryEquiv`s (`planeIso`, `planeIsoConj`); the extension theorem for finite congruent point sets
is assembled from these.
-/

import Mathlib
import UnitDistanceGraphs.Definitions

namespace UnitDistanceGraphs

open Complex

/-- The orientation-preserving plane isometry `z ↦ u·z + t` for a unit `u`. -/
noncomputable def planeIso (u t : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ᵢ ℂ where
  toFun z := u * z + t
  invFun w := u⁻¹ * (w - t)
  left_inv z := by
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    field_simp; ring
  right_inv w := by
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    field_simp; ring
  isometry_toFun := by
    refine Isometry.of_dist_eq (fun z w => ?_)
    simp only [dist_eq_norm]
    rw [show u * z + t - (u * w + t) = u * (z - w) by ring, norm_mul, hu, one_mul]

@[simp] lemma planeIso_apply (u t : ℂ) (hu : ‖u‖ = 1) (z : ℂ) :
    planeIso u t hu z = u * z + t := rfl

/-- For a unit `u`, `u · ū = 1`. -/
private lemma mul_conj_self {u : ℂ} (hu : ‖u‖ = 1) : u * (starRingEnd ℂ) u = 1 := by
  have h : Complex.normSq u = 1 := by
    have := Complex.normSq_eq_norm_sq u; rw [hu] at this; simpa using this
  rw [Complex.mul_conj, h, Complex.ofReal_one]

/-- The orientation-reversing plane isometry `z ↦ u·z̄ + t` for a unit `u`. -/
noncomputable def planeIsoConj (u t : ℂ) (hu : ‖u‖ = 1) : ℂ ≃ᵢ ℂ where
  toFun z := u * (starRingEnd ℂ) z + t
  invFun w := u * (starRingEnd ℂ) (w - t)
  left_inv z := by
    show u * (starRingEnd ℂ) (u * (starRingEnd ℂ) z + t - t) = z
    rw [add_sub_cancel_right, map_mul, Complex.conj_conj, ← mul_assoc, mul_conj_self hu, one_mul]
  right_inv w := by
    show u * (starRingEnd ℂ) (u * (starRingEnd ℂ) (w - t)) + t = w
    rw [map_mul, Complex.conj_conj, ← mul_assoc, mul_conj_self hu, one_mul, sub_add_cancel]
  isometry_toFun := by
    refine Isometry.of_dist_eq (fun z w => ?_)
    simp only [dist_eq_norm]
    rw [show u * (starRingEnd ℂ) z + t - (u * (starRingEnd ℂ) w + t)
          = u * ((starRingEnd ℂ) z - (starRingEnd ℂ) w) by ring, norm_mul, hu, one_mul,
        ← map_sub, Complex.norm_conj]

@[simp] lemma planeIsoConj_apply (u t : ℂ) (hu : ‖u‖ = 1) (z : ℂ) :
    planeIsoConj u t hu z = u * (starRingEnd ℂ) z + t := rfl

/-! ### The plane congruence-extension theorem

A point `q` with the same distances to `0` and `1` as a point `p` equals `p` or its conjugate; hence
a family with the same pairwise distances as another (both anchored at `0,1`) is its image or its
mirror image. Rescaling/translating two anchors to `0,1` gives: two point families with equal
pairwise distances are related by a single plane isometry. -/

/-- A point is determined by its distances to `0` and `1`, up to conjugation. -/
private lemma eq_or_conj_of_normSq {p q : ℂ} (h0 : ‖q‖ = ‖p‖) (h1 : ‖q - 1‖ = ‖p - 1‖) :
    q = p ∨ q = (starRingEnd ℂ) p := by
  have hns0 : Complex.normSq q = Complex.normSq p := by
    have : ‖q‖ ^ 2 = ‖p‖ ^ 2 := by rw [h0]
    rwa [Complex.sq_norm, Complex.sq_norm] at this
  have hns1 : Complex.normSq (q - 1) = Complex.normSq (p - 1) := by
    have : ‖q - 1‖ ^ 2 = ‖p - 1‖ ^ 2 := by rw [h1]
    rwa [Complex.sq_norm, Complex.sq_norm] at this
  simp only [Complex.normSq_apply] at hns0
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im] at hns1
  have hre : q.re = p.re := by linear_combination (hns0 - hns1) / 2
  have him : q.im = p.im ∨ q.im = -p.im := by
    have hsq : (q.im - p.im) * (q.im + p.im) = 0 := by
      linear_combination hns0 - (q.re + p.re) * hre
    rcases mul_eq_zero.mp hsq with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases him with h | h
  · exact Or.inl (Complex.ext hre h)
  · exact Or.inr (Complex.ext (by rw [Complex.conj_re]; exact hre)
      (by rw [Complex.conj_im]; exact h))

/-- **Plane congruence extension.** Two families of points in `ℂ` with equal pairwise distances are
related by a single Euclidean plane isometry. -/
theorem exists_isometryEquiv_of_dist_eq {ι : Type*} (v w : ι → ℂ)
    (h : ∀ i j, dist (v i) (v j) = dist (w i) (w j)) :
    ∃ φ : ℂ ≃ᵢ ℂ, ∀ i, φ (v i) = w i := by
  by_cases hconst : ∀ i j, v i = v j
  · rcases isEmpty_or_nonempty ι with he | he
    · exact ⟨planeIso 1 0 (by norm_num), fun i => (he.false i).elim⟩
    · obtain ⟨i0⟩ := he
      refine ⟨planeIso 1 (w i0 - v i0) (by norm_num), fun i => ?_⟩
      have hw : w i = w i0 := by
        have hd := h i i0; rw [hconst i i0, dist_self] at hd; exact dist_eq_zero.mp hd.symm
      rw [planeIso_apply, one_mul, hconst i i0, hw]; ring
  · push Not at hconst
    obtain ⟨i0, i1, hne⟩ := hconst
    set a := v i0 with ha
    set e := v i1 - a with he_def
    set a' := w i0 with ha'
    set e' := w i1 - a' with he'_def
    have he0 : e ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hnorm : ‖e'‖ = ‖e‖ := by
      have hd := h i0 i1
      rw [dist_eq_norm, dist_eq_norm, show v i0 - v i1 = -e by rw [he_def]; ring,
        show w i0 - w i1 = -e' by rw [he'_def]; ring, norm_neg, norm_neg] at hd
      exact hd.symm
    have he'0 : e' ≠ 0 := by rw [← norm_ne_zero_iff, hnorm]; exact norm_ne_zero_iff.mpr he0
    -- normalized coordinates `p i, q i` sharing anchors `0, 1`
    have hce : (starRingEnd ℂ) e ≠ 0 := by
      simpa only [ne_eq, map_eq_zero] using he0
    set p : ι → ℂ := fun i => (v i - a) / e with hp_def
    set q : ι → ℂ := fun i => (w i - a') / e' with hq_def
    have hpi : ∀ i, p i = (v i - a) / e := fun _ => rfl
    have hqi : ∀ i, q i = (w i - a') / e' := fun _ => rfl
    have hpq : ∀ i j, ‖q i - q j‖ = ‖p i - p j‖ := by
      intro i j
      have hd := h i j
      rw [dist_eq_norm, dist_eq_norm] at hd
      have e1 : v i - v j = (p i - p j) * e := by
        rw [hpi i, hpi j, div_sub_div_same, div_mul_cancel₀ _ he0]; ring
      have e2 : w i - w j = (q i - q j) * e' := by
        rw [hqi i, hqi j, div_sub_div_same, div_mul_cancel₀ _ he'0]; ring
      rw [e1, e2, norm_mul, norm_mul, hnorm] at hd
      exact (mul_right_cancel₀ (norm_ne_zero_iff.mpr he0) hd).symm
    have hp0 : p i0 = 0 := by rw [hpi, ← ha, sub_self, zero_div]
    have hp1 : p i1 = 1 := by rw [hpi, ← he_def, div_self he0]
    have hq0 : q i0 = 0 := by rw [hqi, ← ha', sub_self, zero_div]
    have hq1 : q i1 = 1 := by rw [hqi, ← he'_def, div_self he'0]
    have hchoice : ∀ i, q i = p i ∨ q i = (starRingEnd ℂ) (p i) := by
      intro i
      refine eq_or_conj_of_normSq ?_ ?_
      · have := hpq i i0; rwa [hq0, hp0, sub_zero, sub_zero] at this
      · have := hpq i i1; rwa [hq1, hp1] at this
    have hglobal : (∀ i, q i = p i) ∨ (∀ i, q i = (starRingEnd ℂ) (p i)) := by
      by_cases hall : ∀ i, q i = p i
      · exact Or.inl hall
      · push Not at hall
        obtain ⟨i2, hi2⟩ := hall
        have hq2 : q i2 = (starRingEnd ℂ) (p i2) := (hchoice i2).resolve_left hi2
        have hpim : (p i2).im ≠ 0 := by
          intro h0
          apply hi2
          rw [hq2]
          apply Complex.ext
          · exact Complex.conj_re _
          · rw [Complex.conj_im, h0, neg_zero]
        refine Or.inr (fun i => ?_)
        rcases hchoice i with hqp | hqc
        · have hdist := hpq i i2
          rw [hqp, hq2] at hdist
          have him0 : (p i).im = 0 := by
            have he2 := congrArg (· ^ 2) hdist
            simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
              Complex.conj_re, Complex.conj_im] at he2
            have hii : (p i).im * (p i2).im = 0 := by nlinarith [he2]
            exact (mul_eq_zero.mp hii).resolve_right hpim
          rw [hqp]
          apply Complex.ext
          · exact (Complex.conj_re _).symm
          · rw [Complex.conj_im, him0, neg_zero]
        · exact hqc
    rcases hglobal with hid | hcj
    · refine ⟨planeIso (e' / e) (a' - a * (e' / e))
        (by rw [norm_div, hnorm, div_self (norm_ne_zero_iff.mpr he0)]), fun i => ?_⟩
      have hqp := hid i
      rw [hpi, hqi] at hqp
      have hwi : w i = a' + (v i - a) * (e' / e) := by
        field_simp [he0, he'0] at hqp
        field_simp [he0]
        linear_combination hqp
      rw [planeIso_apply, hwi]; ring
    · refine ⟨planeIsoConj (e' / (starRingEnd ℂ) e)
        (a' - (starRingEnd ℂ) a * (e' / (starRingEnd ℂ) e))
        (by rw [norm_div, Complex.norm_conj, hnorm, div_self (norm_ne_zero_iff.mpr he0)]),
        fun i => ?_⟩
      have hqc := hcj i
      rw [hpi, hqi, map_div₀, map_sub] at hqc
      have hwi : w i = a' + (e' / (starRingEnd ℂ) e) *
          ((starRingEnd ℂ) (v i) - (starRingEnd ℂ) a) := by
        field_simp [hce, he'0] at hqc
        field_simp [hce]
        linear_combination hqc
      rw [planeIsoConj_apply, hwi, map_sub]; ring

/-- **Congruence from equal pairwise distances.** If two families `vA, vB : ι → ℂ` have equal
pairwise distances, their images are congruent point sets. This is the interface used to discharge
the congruence obligations: supplying pairwise distances (not an explicit isometry). -/
theorem congruent_of_dist_eq {ι : Type*} [Fintype ι] (vA vB : ι → ℂ)
    (h : ∀ i j, dist (vA i) (vA j) = dist (vB i) (vB j)) :
    Congruent (Finset.image vA Finset.univ) (Finset.image vB Finset.univ) := by
  obtain ⟨φ, hφ⟩ := exists_isometryEquiv_of_dist_eq vA vB h
  refine ⟨φ, ?_⟩
  rw [Finset.image_image]
  exact Finset.image_congr (fun i _ => (hφ i).symm)

end UnitDistanceGraphs
