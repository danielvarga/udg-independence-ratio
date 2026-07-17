/-
The 29 vertices of `G₂₉`: enumeration, injectivity, identification with `G29`, and the
adjacency matrix — the complete kernel-checked geometry of the vertex set, in three parts.

### Part 1 — enumeration and injectivity (`vtx`, `vtx_injective`)

Ordered vertex enumeration `vtx : Fin 29 → ℂ` of `G₂₉` and its injectivity (`vtx_injective`),
by the interval method (`injective_of_boxes`): each vertex lies in a rational box (checked inline
in `hval` by a defeq `show` + `linarith` over √-bounds), and the 29 boxes are pairwise separated
(`hsep`). Box bounds are scaled integers (`/1000`) so the separation `sepOk` is closed by the
axiom-free kernel `decide`.

Design notes:
* the box bounds are scaled to integers because the kernel's `decide` accelerates `Int` but chokes
  on `ℚ` — this is what keeps `vtx_injective` axiom-free (no `native_decide`);
* `hval` checks all 29 box memberships in a single `fin_cases` theorem; each membership is closed
  by a defeq `show` + `linarith` over the √-bounds, which keeps per-case elaboration cheap.

### Part 2 — `vtx` enumerates `G₂₉` (`image_vtx_eq_G29`)

`vtx` enumerates `G₂₉`: `image_vtx_eq_G29`. Base vertices match by `ring`, `v₀` by defeq,
`v₁` via the nested-radical identities `rad1`–`rad4`.

### Part 3 — the adjacency matrix (`H`, `H_adj_iff`)

Adjacency of the vertex enumeration `vtx : Fin 29 → ℂ` (from Part 1): a computable Bool
adjacency matrix `H` on `Fin 29` matching the geometric relation `dist (vtx i) (vtx j) = 1`.

Non-edges are handled uniformly by **interval arithmetic**: each vertex lies in a rational box
(`hval`, from Part 1, retightened here), so the squared distance
`(Δre)² + (Δim)²` lies in a rational interval computed from the boxes; when that interval excludes
`1`, the pair is a non-edge. This covers the base sublattice *and* the two nested-radical vertices
`v₀, v₁` uniformly — including the tight non-edge `(1,22)` at `dist² ≈ 1.0231`. The 51 edges are the
exact `dist = 1` facts (`dist_baseVert_eq_one_iff` + `dist_v0_v4`, `dist_v1_v4`).
-/

import UnitDistanceGraphs.G29

namespace UnitDistanceGraphs

/-! ### Part 1 — enumeration and injectivity -/

/-- The 29 vertices of `G₂₉`, ordered as in the certificate data. -/
noncomputable def vtx : Fin 29 → ℂ :=
  ![(⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ),
    (⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ),
    (baseVert (14/3) 0 2 (1/3)),
    (baseVert (9/2) 0 2 (1/2)),
    (baseVert (47/12) (-1/12) (23/12) (1/12)),
    (baseVert (19/4) (-1/12) (23/12) (1/4)),
    (baseVert (55/12) (-1/12) (23/12) (5/12)),
    (baseVert (67/12) (-1/12) (23/12) (5/12)),
    (baseVert (61/12) (-1/12) (29/12) (5/12)),
    (baseVert (59/12) (-1/12) (17/12) (7/12)),
    (baseVert (65/12) (-1/12) (23/12) (7/12)),
    (baseVert (59/12) (-1/12) (29/12) (7/12)),
    (baseVert (16/3) (-1/6) (7/3) (1/6)),
    (baseVert (17/3) (-1/6) (11/6) (1/3)),
    (baseVert (25/6) (-1/6) (7/3) (1/3)),
    (baseVert (31/6) (-1/6) (7/3) (1/3)),
    (baseVert (11/2) (-1/6) (11/6) (1/2)),
    (baseVert 5 (-1/6) (7/3) (1/2)),
    (baseVert (13/3) (-1/6) (11/6) (2/3)),
    (baseVert (29/6) (-1/6) (7/3) (2/3)),
    (baseVert (31/6) (-1/6) (11/6) (5/6)),
    (baseVert (61/12) (-1/4) (5/4) (5/12)),
    (baseVert (55/12) (-1/4) (7/4) (5/12)),
    (baseVert (67/12) (-1/4) (7/4) (5/12)),
    (baseVert (53/12) (-1/4) (7/4) (7/12)),
    (baseVert (65/12) (-1/4) (7/4) (7/12)),
    (baseVert (59/12) (-1/4) (9/4) (7/12)),
    (baseVert (71/12) (-1/4) (9/4) (7/12)),
    (baseVert (31/6) (-1/3) (13/6) (1/3))]

/-- Scaled-integer re lower box bounds (`/1000`), for the axiom-free `decide` separation check. -/
def aReLo : Array Int := #[2521, 2441, 4665, 4499, 3436, 4270, 4103, 5103, 4603, 4436, 4936, 4436, 4374, 4708, 3208, 4208, 4541, 4041, 3374, 3874, 4208, 3646, 3146, 4146, 2979, 3979, 3479, 4479, 3250]
/-- Scaled-integer re upper box bounds (`/1000`), for the axiom-free `decide` separation check. -/
def aReHi : Array Int := #[2524, 2444, 4668, 4501, 3439, 4273, 4106, 5106, 4606, 4439, 4939, 4439, 4377, 4711, 3211, 4211, 4544, 4044, 3377, 3877, 4211, 3649, 3149, 4149, 2982, 3982, 3482, 4482, 3253]
/-- Scaled-integer im lower box bounds (`/1000`), for the axiom-free `decide` separation check. -/
def aImLo : Array Int := #[3997, 3686, 4568, 5121, 3595, 4147, 4700, 4700, 5566, 4387, 5253, 6119, 4593, 4279, 5145, 5145, 4832, 5698, 5385, 6251, 5938, 3545, 4412, 4412, 4964, 4964, 5830, 5830, 4857]
/-- Scaled-integer im upper box bounds (`/1000`), for the axiom-free `decide` separation check. -/
def aImHi : Array Int := #[4000, 3689, 4571, 5124, 3598, 4150, 4703, 4703, 5569, 4390, 5256, 6122, 4596, 4282, 5149, 5149, 4835, 5701, 5388, 6254, 5941, 3549, 4415, 4415, 4967, 4967, 5833, 5833, 4860]
def vReLo (i : Fin 29) : ℚ := (aReLo[i.val]! : ℚ) / 1000
def vReHi (i : Fin 29) : ℚ := (aReHi[i.val]! : ℚ) / 1000
def vImLo (i : Fin 29) : ℚ := (aImLo[i.val]! : ℚ) / 1000
def vImHi (i : Fin 29) : ℚ := (aImHi[i.val]! : ℚ) / 1000

/-! ### Rational bounds on the surds -/
lemma s3l : ((34641/20000) : ℝ) ≤ Real.sqrt 3 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
lemma s3u : Real.sqrt 3 ≤ ((86603/50000) : ℝ) := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
lemma s5l : ((111803/50000) : ℝ) ≤ Real.sqrt 5 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
lemma s5u : Real.sqrt 5 ≤ ((223607/100000) : ℝ) := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
lemma s11l : ((165831/50000) : ℝ) ≤ Real.sqrt 11 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 11 by norm_num), Real.sqrt_nonneg 11]
lemma s11u : Real.sqrt 11 ≤ ((331663/100000) : ℝ) := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 11 by norm_num), Real.sqrt_nonneg 11]
lemma s15l : ((193649/50000) : ℝ) ≤ Real.sqrt 15 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num), Real.sqrt_nonneg 15]
lemma s15u : Real.sqrt 15 ≤ ((387299/100000) : ℝ) := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 15 by norm_num), Real.sqrt_nonneg 15]
lemma s33l : ((71807/12500) : ℝ) ≤ Real.sqrt 33 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num), Real.sqrt_nonneg 33]
lemma s33u : Real.sqrt 33 ≤ ((574457/100000) : ℝ) := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num), Real.sqrt_nonneg 33]
lemma s165l : ((1284523/100000) : ℝ) ≤ Real.sqrt 165 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 165 by norm_num), Real.sqrt_nonneg 165]
lemma s165u : Real.sqrt 165 ≤ ((321131/25000) : ℝ) := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 165 by norm_num), Real.sqrt_nonneg 165]
lemma hN0 : (0:ℝ) ≤ v1Radical := Real.sqrt_nonneg _
lemma hNsq : v1Radical ^ 2 = 415/8 + 79 * Real.sqrt 33 / 8 := by rw [v1Radical, Real.sq_sqrt (by positivity)]
lemma vNl : ((260531/25000) : ℝ) ≤ v1Radical := by nlinarith [hNsq, s33l, hN0]
lemma vNu : v1Radical ≤ ((1042127/100000) : ℝ) := by nlinarith [hNsq, s33u, hN0]

/-! ### Pairwise box separation (axiom-free `decide`) -/
def sepOk : Bool := (List.range 29).all (fun i => (List.range 29).all (fun j =>
  (i == j) || decide (aReHi[i]! < aReLo[j]!) || decide (aReHi[j]! < aReLo[i]!)
  || decide (aImHi[i]! < aImLo[j]!) || decide (aImHi[j]! < aImLo[i]!)))
lemma sepOk_true : sepOk = true := by decide
lemma qbridge (a b : ℤ) : ((a:ℚ)/1000 < (b:ℚ)/1000) ↔ (a < b) := by
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0:ℚ) < 1000)]; exact_mod_cast Iff.rfl
lemma hsep (i j : Fin 29) (hij : i ≠ j) :
    vReHi i < vReLo j ∨ vReHi j < vReLo i ∨ vImHi i < vImLo j ∨ vImHi j < vImLo i := by
  have h2 := (List.all_eq_true.mp ((List.all_eq_true.mp sepOk_true) i.val
    (List.mem_range.mpr i.isLt))) j.val (List.mem_range.mpr j.isLt)
  have hne : (i.val == j.val) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hij (Fin.ext h)
  rw [hne, Bool.false_or] at h2
  simp only [vReHi, vReLo, vImHi, vImLo, qbridge]
  simpa only [Bool.or_eq_true, decide_eq_true_eq, or_assoc] using h2

/-! ### Box membership for every vertex (one `fin_cases`, checked inline) -/
set_option maxHeartbeats 1000000 in
lemma hval : ∀ i : Fin 29, ((vReLo i : ℚ):ℝ) ≤ (vtx i).re ∧ (vtx i).re ≤ ((vReHi i:ℚ):ℝ) ∧
    ((vImLo i:ℚ):ℝ) ≤ (vtx i).im ∧ (vtx i).im ≤ ((vImHi i:ℚ):ℝ) := by
  intro i; fin_cases i
  · show (((2521/1000 : ℚ)):ℝ) ≤ ((⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)).re ∧ ((⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)).re ≤ (((2524/1000 : ℚ)):ℝ) ∧ (((3997/1000 : ℚ)):ℝ) ≤ ((⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)).im ∧ ((⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)).im ≤ (((4000/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((2441/1000 : ℚ)):ℝ) ≤ ((⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)).re ∧ ((⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)).re ≤ (((2444/1000 : ℚ)):ℝ) ∧ (((3686/1000 : ℚ)):ℝ) ≤ ((⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)).im ∧ ((⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)).im ≤ (((3689/1000 : ℚ)):ℝ)
    -- `nlinarith` fallback retained here (unlike the other vertices): the `i = 1` vertex
    -- involves the nested radical `v1Radical`, so plain `linarith` does not close all bounds.
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [] <;> push_cast <;> first | linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u] | nlinarith [s3l, s3u, s11l, s11u, s33l, s33u, vNl, vNu, hN0, Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sqrt_nonneg 33]
  · show (((4665/1000 : ℚ)):ℝ) ≤ ((baseVert (14/3) 0 2 (1/3))).re ∧ ((baseVert (14/3) 0 2 (1/3))).re ≤ (((4668/1000 : ℚ)):ℝ) ∧ (((4568/1000 : ℚ)):ℝ) ≤ ((baseVert (14/3) 0 2 (1/3))).im ∧ ((baseVert (14/3) 0 2 (1/3))).im ≤ (((4571/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4499/1000 : ℚ)):ℝ) ≤ ((baseVert (9/2) 0 2 (1/2))).re ∧ ((baseVert (9/2) 0 2 (1/2))).re ≤ (((4501/1000 : ℚ)):ℝ) ∧ (((5121/1000 : ℚ)):ℝ) ≤ ((baseVert (9/2) 0 2 (1/2))).im ∧ ((baseVert (9/2) 0 2 (1/2))).im ≤ (((5124/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3436/1000 : ℚ)):ℝ) ≤ ((baseVert (47/12) (-1/12) (23/12) (1/12))).re ∧ ((baseVert (47/12) (-1/12) (23/12) (1/12))).re ≤ (((3439/1000 : ℚ)):ℝ) ∧ (((3595/1000 : ℚ)):ℝ) ≤ ((baseVert (47/12) (-1/12) (23/12) (1/12))).im ∧ ((baseVert (47/12) (-1/12) (23/12) (1/12))).im ≤ (((3598/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4270/1000 : ℚ)):ℝ) ≤ ((baseVert (19/4) (-1/12) (23/12) (1/4))).re ∧ ((baseVert (19/4) (-1/12) (23/12) (1/4))).re ≤ (((4273/1000 : ℚ)):ℝ) ∧ (((4147/1000 : ℚ)):ℝ) ≤ ((baseVert (19/4) (-1/12) (23/12) (1/4))).im ∧ ((baseVert (19/4) (-1/12) (23/12) (1/4))).im ≤ (((4150/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4103/1000 : ℚ)):ℝ) ≤ ((baseVert (55/12) (-1/12) (23/12) (5/12))).re ∧ ((baseVert (55/12) (-1/12) (23/12) (5/12))).re ≤ (((4106/1000 : ℚ)):ℝ) ∧ (((4700/1000 : ℚ)):ℝ) ≤ ((baseVert (55/12) (-1/12) (23/12) (5/12))).im ∧ ((baseVert (55/12) (-1/12) (23/12) (5/12))).im ≤ (((4703/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((5103/1000 : ℚ)):ℝ) ≤ ((baseVert (67/12) (-1/12) (23/12) (5/12))).re ∧ ((baseVert (67/12) (-1/12) (23/12) (5/12))).re ≤ (((5106/1000 : ℚ)):ℝ) ∧ (((4700/1000 : ℚ)):ℝ) ≤ ((baseVert (67/12) (-1/12) (23/12) (5/12))).im ∧ ((baseVert (67/12) (-1/12) (23/12) (5/12))).im ≤ (((4703/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4603/1000 : ℚ)):ℝ) ≤ ((baseVert (61/12) (-1/12) (29/12) (5/12))).re ∧ ((baseVert (61/12) (-1/12) (29/12) (5/12))).re ≤ (((4606/1000 : ℚ)):ℝ) ∧ (((5566/1000 : ℚ)):ℝ) ≤ ((baseVert (61/12) (-1/12) (29/12) (5/12))).im ∧ ((baseVert (61/12) (-1/12) (29/12) (5/12))).im ≤ (((5569/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4436/1000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/12) (17/12) (7/12))).re ∧ ((baseVert (59/12) (-1/12) (17/12) (7/12))).re ≤ (((4439/1000 : ℚ)):ℝ) ∧ (((4387/1000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/12) (17/12) (7/12))).im ∧ ((baseVert (59/12) (-1/12) (17/12) (7/12))).im ≤ (((4390/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4936/1000 : ℚ)):ℝ) ≤ ((baseVert (65/12) (-1/12) (23/12) (7/12))).re ∧ ((baseVert (65/12) (-1/12) (23/12) (7/12))).re ≤ (((4939/1000 : ℚ)):ℝ) ∧ (((5253/1000 : ℚ)):ℝ) ≤ ((baseVert (65/12) (-1/12) (23/12) (7/12))).im ∧ ((baseVert (65/12) (-1/12) (23/12) (7/12))).im ≤ (((5256/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4436/1000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/12) (29/12) (7/12))).re ∧ ((baseVert (59/12) (-1/12) (29/12) (7/12))).re ≤ (((4439/1000 : ℚ)):ℝ) ∧ (((6119/1000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/12) (29/12) (7/12))).im ∧ ((baseVert (59/12) (-1/12) (29/12) (7/12))).im ≤ (((6122/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4374/1000 : ℚ)):ℝ) ≤ ((baseVert (16/3) (-1/6) (7/3) (1/6))).re ∧ ((baseVert (16/3) (-1/6) (7/3) (1/6))).re ≤ (((4377/1000 : ℚ)):ℝ) ∧ (((4593/1000 : ℚ)):ℝ) ≤ ((baseVert (16/3) (-1/6) (7/3) (1/6))).im ∧ ((baseVert (16/3) (-1/6) (7/3) (1/6))).im ≤ (((4596/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4708/1000 : ℚ)):ℝ) ≤ ((baseVert (17/3) (-1/6) (11/6) (1/3))).re ∧ ((baseVert (17/3) (-1/6) (11/6) (1/3))).re ≤ (((4711/1000 : ℚ)):ℝ) ∧ (((4279/1000 : ℚ)):ℝ) ≤ ((baseVert (17/3) (-1/6) (11/6) (1/3))).im ∧ ((baseVert (17/3) (-1/6) (11/6) (1/3))).im ≤ (((4282/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3208/1000 : ℚ)):ℝ) ≤ ((baseVert (25/6) (-1/6) (7/3) (1/3))).re ∧ ((baseVert (25/6) (-1/6) (7/3) (1/3))).re ≤ (((3211/1000 : ℚ)):ℝ) ∧ (((5145/1000 : ℚ)):ℝ) ≤ ((baseVert (25/6) (-1/6) (7/3) (1/3))).im ∧ ((baseVert (25/6) (-1/6) (7/3) (1/3))).im ≤ (((5149/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4208/1000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/6) (7/3) (1/3))).re ∧ ((baseVert (31/6) (-1/6) (7/3) (1/3))).re ≤ (((4211/1000 : ℚ)):ℝ) ∧ (((5145/1000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/6) (7/3) (1/3))).im ∧ ((baseVert (31/6) (-1/6) (7/3) (1/3))).im ≤ (((5149/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4541/1000 : ℚ)):ℝ) ≤ ((baseVert (11/2) (-1/6) (11/6) (1/2))).re ∧ ((baseVert (11/2) (-1/6) (11/6) (1/2))).re ≤ (((4544/1000 : ℚ)):ℝ) ∧ (((4832/1000 : ℚ)):ℝ) ≤ ((baseVert (11/2) (-1/6) (11/6) (1/2))).im ∧ ((baseVert (11/2) (-1/6) (11/6) (1/2))).im ≤ (((4835/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4041/1000 : ℚ)):ℝ) ≤ ((baseVert 5 (-1/6) (7/3) (1/2))).re ∧ ((baseVert 5 (-1/6) (7/3) (1/2))).re ≤ (((4044/1000 : ℚ)):ℝ) ∧ (((5698/1000 : ℚ)):ℝ) ≤ ((baseVert 5 (-1/6) (7/3) (1/2))).im ∧ ((baseVert 5 (-1/6) (7/3) (1/2))).im ≤ (((5701/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3374/1000 : ℚ)):ℝ) ≤ ((baseVert (13/3) (-1/6) (11/6) (2/3))).re ∧ ((baseVert (13/3) (-1/6) (11/6) (2/3))).re ≤ (((3377/1000 : ℚ)):ℝ) ∧ (((5385/1000 : ℚ)):ℝ) ≤ ((baseVert (13/3) (-1/6) (11/6) (2/3))).im ∧ ((baseVert (13/3) (-1/6) (11/6) (2/3))).im ≤ (((5388/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3874/1000 : ℚ)):ℝ) ≤ ((baseVert (29/6) (-1/6) (7/3) (2/3))).re ∧ ((baseVert (29/6) (-1/6) (7/3) (2/3))).re ≤ (((3877/1000 : ℚ)):ℝ) ∧ (((6251/1000 : ℚ)):ℝ) ≤ ((baseVert (29/6) (-1/6) (7/3) (2/3))).im ∧ ((baseVert (29/6) (-1/6) (7/3) (2/3))).im ≤ (((6254/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4208/1000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/6) (11/6) (5/6))).re ∧ ((baseVert (31/6) (-1/6) (11/6) (5/6))).re ≤ (((4211/1000 : ℚ)):ℝ) ∧ (((5938/1000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/6) (11/6) (5/6))).im ∧ ((baseVert (31/6) (-1/6) (11/6) (5/6))).im ≤ (((5941/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3646/1000 : ℚ)):ℝ) ≤ ((baseVert (61/12) (-1/4) (5/4) (5/12))).re ∧ ((baseVert (61/12) (-1/4) (5/4) (5/12))).re ≤ (((3649/1000 : ℚ)):ℝ) ∧ (((3545/1000 : ℚ)):ℝ) ≤ ((baseVert (61/12) (-1/4) (5/4) (5/12))).im ∧ ((baseVert (61/12) (-1/4) (5/4) (5/12))).im ≤ (((3549/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3146/1000 : ℚ)):ℝ) ≤ ((baseVert (55/12) (-1/4) (7/4) (5/12))).re ∧ ((baseVert (55/12) (-1/4) (7/4) (5/12))).re ≤ (((3149/1000 : ℚ)):ℝ) ∧ (((4412/1000 : ℚ)):ℝ) ≤ ((baseVert (55/12) (-1/4) (7/4) (5/12))).im ∧ ((baseVert (55/12) (-1/4) (7/4) (5/12))).im ≤ (((4415/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4146/1000 : ℚ)):ℝ) ≤ ((baseVert (67/12) (-1/4) (7/4) (5/12))).re ∧ ((baseVert (67/12) (-1/4) (7/4) (5/12))).re ≤ (((4149/1000 : ℚ)):ℝ) ∧ (((4412/1000 : ℚ)):ℝ) ≤ ((baseVert (67/12) (-1/4) (7/4) (5/12))).im ∧ ((baseVert (67/12) (-1/4) (7/4) (5/12))).im ≤ (((4415/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((2979/1000 : ℚ)):ℝ) ≤ ((baseVert (53/12) (-1/4) (7/4) (7/12))).re ∧ ((baseVert (53/12) (-1/4) (7/4) (7/12))).re ≤ (((2982/1000 : ℚ)):ℝ) ∧ (((4964/1000 : ℚ)):ℝ) ≤ ((baseVert (53/12) (-1/4) (7/4) (7/12))).im ∧ ((baseVert (53/12) (-1/4) (7/4) (7/12))).im ≤ (((4967/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3979/1000 : ℚ)):ℝ) ≤ ((baseVert (65/12) (-1/4) (7/4) (7/12))).re ∧ ((baseVert (65/12) (-1/4) (7/4) (7/12))).re ≤ (((3982/1000 : ℚ)):ℝ) ∧ (((4964/1000 : ℚ)):ℝ) ≤ ((baseVert (65/12) (-1/4) (7/4) (7/12))).im ∧ ((baseVert (65/12) (-1/4) (7/4) (7/12))).im ≤ (((4967/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3479/1000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/4) (9/4) (7/12))).re ∧ ((baseVert (59/12) (-1/4) (9/4) (7/12))).re ≤ (((3482/1000 : ℚ)):ℝ) ∧ (((5830/1000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/4) (9/4) (7/12))).im ∧ ((baseVert (59/12) (-1/4) (9/4) (7/12))).im ≤ (((5833/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((4479/1000 : ℚ)):ℝ) ≤ ((baseVert (71/12) (-1/4) (9/4) (7/12))).re ∧ ((baseVert (71/12) (-1/4) (9/4) (7/12))).re ≤ (((4482/1000 : ℚ)):ℝ) ∧ (((5830/1000 : ℚ)):ℝ) ≤ ((baseVert (71/12) (-1/4) (9/4) (7/12))).im ∧ ((baseVert (71/12) (-1/4) (9/4) (7/12))).im ≤ (((5833/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]
  · show (((3250/1000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/3) (13/6) (1/3))).re ∧ ((baseVert (31/6) (-1/3) (13/6) (1/3))).re ≤ (((3253/1000 : ℚ)):ℝ) ∧ (((4857/1000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/3) (13/6) (1/3))).im ∧ ((baseVert (31/6) (-1/3) (13/6) (1/3))).im ≤ (((4860/1000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u]

/-- **The vertex enumeration is injective** — `G₂₉` has 29 distinct vertices in bijection with
`Fin 29`. Axiom-clean (`propext, Classical.choice, Quot.sound`). -/
theorem vtx_injective : Function.Injective vtx :=
  injective_of_boxes vtx vReLo vReHi vImLo vImHi hval hsep

/-! ### Part 2 — `vtx` enumerates `G₂₉` -/

section
open Real

lemma rad1 : Real.sqrt (9130 + 1738 * Real.sqrt 33) = 4 * v1Radical * Real.sqrt 11 := by
  have hNsq : v1Radical ^ 2 = 415/8 + 79 * Real.sqrt 33 / 8 := by rw [v1Radical, Real.sq_sqrt (by positivity)]
  have hh : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  rw [show (9130:ℝ) + 1738 * Real.sqrt 33 = (4 * v1Radical * Real.sqrt 11)^2 by nlinarith [hNsq, hh]]
  exact Real.sqrt_sq (by simp only [v1Radical]; positivity)
lemma rad2 : Real.sqrt (2490 + 474 * Real.sqrt 33) = 4 * v1Radical * Real.sqrt 3 := by
  have hNsq : v1Radical ^ 2 = 415/8 + 79 * Real.sqrt 33 / 8 := by rw [v1Radical, Real.sq_sqrt (by positivity)]
  have hh : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [show (2490:ℝ) + 474 * Real.sqrt 33 = (4 * v1Radical * Real.sqrt 3)^2 by nlinarith [hNsq, hh]]
  exact Real.sqrt_sq (by simp only [v1Radical]; positivity)
lemma rad3 : Real.sqrt (27390 + 5214 * Real.sqrt 33) = 4 * v1Radical * Real.sqrt 33 := by
  have hNsq : v1Radical ^ 2 = 415/8 + 79 * Real.sqrt 33 / 8 := by rw [v1Radical, Real.sq_sqrt (by positivity)]
  have hh : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  rw [show (27390:ℝ) + 5214 * Real.sqrt 33 = (4 * v1Radical * Real.sqrt 33)^2 by nlinarith [hNsq, hh]]
  exact Real.sqrt_sq (by simp only [v1Radical]; positivity)
lemma rad4 : Real.sqrt (830 + 158 * Real.sqrt 33) = 4 * v1Radical := by
  have hNsq : v1Radical ^ 2 = 415/8 + 79 * Real.sqrt 33 / 8 := by rw [v1Radical, Real.sq_sqrt (by positivity)]
  rw [show (830:ℝ) + 158 * Real.sqrt 33 = (4 * v1Radical)^2 by nlinarith [hNsq]]
  exact Real.sqrt_sq (by simp only [v1Radical]; positivity)
lemma veq_0 : vtx 0 = (⟨((25 / 6 : ℝ) + ((-3 / 16 : ℝ) * Real.sqrt (5)) + ((-1 / 6 : ℝ) * Real.sqrt (33)) + ((-1 / 48 : ℝ) * Real.sqrt (165))),     (((1 / 6 : ℝ) * Real.sqrt (15)) + ((1 / 48 : ℝ) * Real.sqrt (11)) + ((91 / 48 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  simp only [vtx, Matrix.cons_val_zero]
lemma veq_1 : vtx 1 = (⟨((103 / 24 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33)) + ((-1 / 128 : ℝ) * Real.sqrt ((9130 + (1738 * Real.sqrt (33))))) + ((1 / 384 : ℝ) * Real.sqrt ((2490 + (474 * Real.sqrt (33)))))),     (((-1 / 384 : ℝ) * Real.sqrt ((27390 + (5214 * Real.sqrt (33))))) + ((3 / 128 : ℝ) * Real.sqrt ((830 + (158 * Real.sqrt (33))))) + ((7 / 48 : ℝ) * Real.sqrt (11)) + ((79 / 48 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  simp only [vtx, Matrix.cons_val_one, Complex.ext_iff, rad1, rad2, rad3, rad4]
  constructor <;> push_cast <;> ring
lemma veq_2 : vtx 2 = (⟨(14 / 3 : ℝ),     ((2 * Real.sqrt (3)) + ((1 / 3 : ℝ) * Real.sqrt (11)))⟩ : ℂ) := by
  show (baseVert (14/3) 0 2 (1/3) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_3 : vtx 3 = (⟨(9 / 2 : ℝ),     (((1 / 2 : ℝ) * Real.sqrt (11)) + (2 * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (9/2) 0 2 (1/2) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_4 : vtx 4 = (⟨((47 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),     (((1 / 12 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (47/12) (-1/12) (23/12) (1/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_5 : vtx 5 = (⟨((19 / 4 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),     (((1 / 4 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (19/4) (-1/12) (23/12) (1/4) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_6 : vtx 6 = (⟨((55 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),     (((5 / 12 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (55/12) (-1/12) (23/12) (5/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_7 : vtx 7 = (⟨((67 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),     (((5 / 12 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (67/12) (-1/12) (23/12) (5/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_8 : vtx 8 = (⟨((61 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),     (((5 / 12 : ℝ) * Real.sqrt (11)) + ((29 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (61/12) (-1/12) (29/12) (5/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_9 : vtx 9 = (⟨((59 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),     (((7 / 12 : ℝ) * Real.sqrt (11)) + ((17 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (59/12) (-1/12) (17/12) (7/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_10 : vtx 10 = (⟨((65 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),     (((7 / 12 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (65/12) (-1/12) (23/12) (7/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_11 : vtx 11 = (⟨((59 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),     (((7 / 12 : ℝ) * Real.sqrt (11)) + ((29 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (59/12) (-1/12) (29/12) (7/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_12 : vtx 12 = (⟨((16 / 3 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((1 / 6 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (16/3) (-1/6) (7/3) (1/6) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_13 : vtx 13 = (⟨((17 / 3 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((1 / 3 : ℝ) * Real.sqrt (11)) + ((11 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (17/3) (-1/6) (11/6) (1/3) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_14 : vtx 14 = (⟨((25 / 6 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((1 / 3 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (25/6) (-1/6) (7/3) (1/3) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_15 : vtx 15 = (⟨((31 / 6 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((1 / 3 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (31/6) (-1/6) (7/3) (1/3) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_16 : vtx 16 = (⟨((11 / 2 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((1 / 2 : ℝ) * Real.sqrt (11)) + ((11 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (11/2) (-1/6) (11/6) (1/2) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_17 : vtx 17 = (⟨(5 + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((1 / 2 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert 5 (-1/6) (7/3) (1/2) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_18 : vtx 18 = (⟨((13 / 3 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((2 / 3 : ℝ) * Real.sqrt (11)) + ((11 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (13/3) (-1/6) (11/6) (2/3) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_19 : vtx 19 = (⟨((29 / 6 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((2 / 3 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (29/6) (-1/6) (7/3) (2/3) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_20 : vtx 20 = (⟨((31 / 6 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),     (((5 / 6 : ℝ) * Real.sqrt (11)) + ((11 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (31/6) (-1/6) (11/6) (5/6) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_21 : vtx 21 = (⟨((61 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),     (((5 / 4 : ℝ) * Real.sqrt (3)) + ((5 / 12 : ℝ) * Real.sqrt (11)))⟩ : ℂ) := by
  show (baseVert (61/12) (-1/4) (5/4) (5/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_22 : vtx 22 = (⟨((55 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),     (((5 / 12 : ℝ) * Real.sqrt (11)) + ((7 / 4 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (55/12) (-1/4) (7/4) (5/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_23 : vtx 23 = (⟨((67 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),     (((5 / 12 : ℝ) * Real.sqrt (11)) + ((7 / 4 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (67/12) (-1/4) (7/4) (5/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_24 : vtx 24 = (⟨((53 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),     (((7 / 4 : ℝ) * Real.sqrt (3)) + ((7 / 12 : ℝ) * Real.sqrt (11)))⟩ : ℂ) := by
  show (baseVert (53/12) (-1/4) (7/4) (7/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_25 : vtx 25 = (⟨((65 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),     (((7 / 4 : ℝ) * Real.sqrt (3)) + ((7 / 12 : ℝ) * Real.sqrt (11)))⟩ : ℂ) := by
  show (baseVert (65/12) (-1/4) (7/4) (7/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_26 : vtx 26 = (⟨((59 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),     (((7 / 12 : ℝ) * Real.sqrt (11)) + ((9 / 4 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (59/12) (-1/4) (9/4) (7/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_27 : vtx 27 = (⟨((71 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),     (((7 / 12 : ℝ) * Real.sqrt (11)) + ((9 / 4 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (71/12) (-1/4) (9/4) (7/12) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring
lemma veq_28 : vtx 28 = (⟨((31 / 6 : ℝ) + ((-1 / 3 : ℝ) * Real.sqrt (33))),     (((1 / 3 : ℝ) * Real.sqrt (11)) + ((13 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ) := by
  show (baseVert (31/6) (-1/3) (13/6) (1/3) : ℂ) = _
  simp only [baseVert, Complex.ext_iff]
  constructor <;> push_cast <;> ring

lemma image_vtx_eq_G29 : Finset.image vtx Finset.univ = G29 := by
  apply Finset.Subset.antisymm
  · rw [Finset.image_subset_iff]; intro i _; fin_cases i
    · show vtx 0 ∈ G29
      rw [veq_0]; unfold G29; exact Finset.mem_insert_self _ _
    · show vtx 1 ∈ G29
      rw [veq_1]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · show vtx 2 ∈ G29
      rw [veq_2]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    · show vtx 3 ∈ G29
      rw [veq_3]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
    · show vtx 4 ∈ G29
      rw [veq_4]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))
    · show vtx 5 ∈ G29
      rw [veq_5]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
    · show vtx 6 ∈ G29
      rw [veq_6]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))
    · show vtx 7 ∈ G29
      rw [veq_7]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))
    · show vtx 8 ∈ G29
      rw [veq_8]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))
    · show vtx 9 ∈ G29
      rw [veq_9]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))
    · show vtx 10 ∈ G29
      rw [veq_10]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))
    · show vtx 11 ∈ G29
      rw [veq_11]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))
    · show vtx 12 ∈ G29
      rw [veq_12]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))))
    · show vtx 13 ∈ G29
      rw [veq_13]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))))
    · show vtx 14 ∈ G29
      rw [veq_14]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))))))
    · show vtx 15 ∈ G29
      rw [veq_15]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))))))
    · show vtx 16 ∈ G29
      rw [veq_16]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))))))))
    · show vtx 17 ∈ G29
      rw [veq_17]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))))))))
    · show vtx 18 ∈ G29
      rw [veq_18]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))))))))))
    · show vtx 19 ∈ G29
      rw [veq_19]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))))))))))
    · show vtx 20 ∈ G29
      rw [veq_20]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))))))))))))
    · show vtx 21 ∈ G29
      rw [veq_21]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))))))))))))
    · show vtx 22 ∈ G29
      rw [veq_22]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))))))))))))))
    · show vtx 23 ∈ G29
      rw [veq_23]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))))))))))))))
    · show vtx 24 ∈ G29
      rw [veq_24]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))))))))))))))))
    · show vtx 25 ∈ G29
      rw [veq_25]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))))))))))))))))
    · show vtx 26 ∈ G29
      rw [veq_26]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))))))))))))))))))))))))
    · show vtx 27 ∈ G29
      rw [veq_27]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))))))))))))))))))))))))
    · show vtx 28 ∈ G29
      rw [veq_28]; unfold G29; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))))))))))))))))))))))))))
  · intro z hz
    simp only [G29, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, veq_0⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, veq_1⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, veq_2⟩
    · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, veq_3⟩
    · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, veq_4⟩
    · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, veq_5⟩
    · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, veq_6⟩
    · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, veq_7⟩
    · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, veq_8⟩
    · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, veq_9⟩
    · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, veq_10⟩
    · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, veq_11⟩
    · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, veq_12⟩
    · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, veq_13⟩
    · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, veq_14⟩
    · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, veq_15⟩
    · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, veq_16⟩
    · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, veq_17⟩
    · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, veq_18⟩
    · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, veq_19⟩
    · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, veq_20⟩
    · exact Finset.mem_image.mpr ⟨21, Finset.mem_univ _, veq_21⟩
    · exact Finset.mem_image.mpr ⟨22, Finset.mem_univ _, veq_22⟩
    · exact Finset.mem_image.mpr ⟨23, Finset.mem_univ _, veq_23⟩
    · exact Finset.mem_image.mpr ⟨24, Finset.mem_univ _, veq_24⟩
    · exact Finset.mem_image.mpr ⟨25, Finset.mem_univ _, veq_25⟩
    · exact Finset.mem_image.mpr ⟨26, Finset.mem_univ _, veq_26⟩
    · exact Finset.mem_image.mpr ⟨27, Finset.mem_univ _, veq_27⟩
    · exact Finset.mem_image.mpr ⟨28, Finset.mem_univ _, veq_28⟩

lemma G29_eq_map_toFinset : G29 = ((List.finRange 29).map vtx).toFinset := by
  rw [← image_vtx_eq_G29]; ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, List.mem_toFinset, List.mem_map,
    List.mem_finRange]

end

/-! ### Part 3 — the adjacency matrix -/

/-! ### General interval bounds for a squared coordinate difference

For `a ∈ [aL, aH]` and `b ∈ [bL, bH]` (rational box bounds), the squared difference `(a - b)²`
lies between `cLo` and `cHi`. These are the two reusable facts driving the bulk non-edge check;
they are applied *by term* (never re-run per pair). -/

/-- Interval **lower** bound for `(a - b)²` given `a ∈ [aL,aH]`, `b ∈ [bL,bH]`. When the boxes are
separated (`aH < bL` or `bH < aL`) it is the squared gap; otherwise `0`. -/
def cLo (aL aH bL bH : ℚ) : ℚ :=
  if aH < bL then (bL - aH) ^ 2 else if bH < aL then (aL - bH) ^ 2 else 0

/-- Interval **upper** bound for `(a - b)²`: the larger squared endpoint of `a - b ∈ [aL-bH, aH-bL]`. -/
def cHi (aL aH bL bH : ℚ) : ℚ :=
  max ((aH - bL) ^ 2) ((aL - bH) ^ 2)

lemma cLo_le {a b : ℝ} {aL aH bL bH : ℚ}
    (ha : (aL : ℝ) ≤ a) (ha' : a ≤ (aH : ℝ)) (hb : (bL : ℝ) ≤ b) (hb' : b ≤ (bH : ℝ)) :
    ((cLo aL aH bL bH : ℚ) : ℝ) ≤ (a - b) ^ 2 := by
  unfold cLo
  split_ifs with h1 h2
  · have h1' : (aH : ℝ) < (bL : ℝ) := by exact_mod_cast h1
    push_cast; nlinarith
  · have h2' : (bH : ℝ) < (aL : ℝ) := by exact_mod_cast h2
    push_cast; nlinarith
  · push_cast; positivity

lemma le_cHi {a b : ℝ} {aL aH bL bH : ℚ}
    (ha : (aL : ℝ) ≤ a) (ha' : a ≤ (aH : ℝ)) (hb : (bL : ℝ) ≤ b) (hb' : b ≤ (bH : ℝ)) :
    (a - b) ^ 2 ≤ ((cHi aL aH bL bH : ℚ) : ℝ) := by
  unfold cHi
  push_cast
  rcases le_total 0 (a - b) with hd | hd
  · exact le_max_of_le_left (by nlinarith)
  · exact le_max_of_le_right (by nlinarith)

/-! ### Integer-scaled versions (for an axiom-free kernel `decide`)

The boxes are scaled integers over `10⁶` (`bReLo6`, …). `iCLo`/`iCHi` are `cLo`/`cHi` on the raw
integers; the bridge lemmas show `cLo (·/10⁶) = iCLo · / 10¹²` (and likewise `cHi`), so the bulk
non-edge check runs as integer arithmetic (`decide` accelerates `Int`, chokes on `ℚ`). -/

def iCLo (aL aH bL bH : ℤ) : ℤ :=
  if aH < bL then (bL - aH) ^ 2 else if bH < aL then (aL - bH) ^ 2 else 0

def iCHi (aL aH bL bH : ℤ) : ℤ :=
  max ((aH - bL) ^ 2) ((aL - bH) ^ 2)

private lemma qbridge6 (a b : ℤ) : ((a : ℚ) / 1000000 < (b : ℚ) / 1000000) ↔ (a < b) := by
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0:ℚ) < 1000000)]; exact_mod_cast Iff.rfl

lemma cLo_int (aL aH bL bH : ℤ) :
    cLo ((aL:ℚ)/1000000) ((aH:ℚ)/1000000) ((bL:ℚ)/1000000) ((bH:ℚ)/1000000)
      = (iCLo aL aH bL bH : ℚ) / 1000000000000 := by
  unfold cLo iCLo
  simp only [qbridge6]
  split_ifs <;> push_cast <;> ring

lemma cHi_int (aL aH bL bH : ℤ) :
    cHi ((aL:ℚ)/1000000) ((aH:ℚ)/1000000) ((bL:ℚ)/1000000) ((bH:ℚ)/1000000)
      = (iCHi aL aH bL bH : ℚ) / 1000000000000 := by
  unfold cHi iCHi
  have e1 : ((aH:ℚ)/1000000 - (bL:ℚ)/1000000) ^ 2 = (((aH - bL) ^ 2 : ℤ):ℚ) / 1000000000000 := by
    push_cast; ring
  have e2 : ((aL:ℚ)/1000000 - (bH:ℚ)/1000000) ^ 2 = (((aL - bH) ^ 2 : ℤ):ℚ) / 1000000000000 := by
    push_cast; ring
  rw [e1, e2, Int.cast_max, max_div_div_right (by norm_num : (0:ℚ) ≤ 1000000000000)]

/-! ### Product bounds for the nested radical `v₁` (so every box is linear-provable) -/
lemma vN3l  : ((9025054371/500000000 : ℝ)) ≤ v1Radical * Real.sqrt 3 := by
  nlinarith [vNl, vNu, s3l, s3u, hN0, Real.sqrt_nonneg 3]
lemma vN3u  : v1Radical * Real.sqrt 3 ≤ ((90251324581/5000000000 : ℝ)) := by
  nlinarith [vNl, vNu, s3l, s3u, hN0, Real.sqrt_nonneg 3]
lemma vN11l : ((43204116261/1250000000 : ℝ)) ≤ v1Radical * Real.sqrt 11 := by
  nlinarith [vNl, vNu, s11l, s11u, hN0, Real.sqrt_nonneg 11]
lemma vN11u : v1Radical * Real.sqrt 11 ≤ ((345634967201/10000000000 : ℝ)) := by
  nlinarith [vNl, vNu, s11l, s11u, hN0, Real.sqrt_nonneg 11]
def bReLo6 : Array Int := #[2522366, 2442151, 4666666, 4500000, 3437952, 4271285, 4104619, 5104619, 4604619, 4437952, 4937952, 4437952, 4375905, 4709238, 3209238, 4209238, 4542571, 4042571, 3375905, 3875905, 4209238, 3647190, 3147190, 4147190, 2980524, 3980524, 3480524, 4480524, 3251810]
def bReHi6 : Array Int := #[2522370, 2442161, 4666667, 4500000, 3437954, 4271287, 4104620, 5104620, 4604620, 4437954, 4937954, 4437954, 4375907, 4709240, 3209240, 4209240, 4542574, 4042574, 3375907, 3875907, 4209240, 3647194, 3147194, 4147194, 2980527, 3980527, 3480527, 4480527, 3251814]
def bImLo6 : Array Int := #[3998271, 3687729, 4569640, 5122410, 3596147, 4148917, 4701687, 4701687, 5567712, 4388432, 5254457, 6120482, 4594220, 4280965, 5146990, 5146990, 4833735, 5699760, 5386505, 6252530, 5939275, 3546987, 4413012, 4413012, 4965782, 4965782, 5831807, 5831807, 4858315]
def bImHi6 : Array Int := #[3998292, 3687754, 4569664, 5122435, 3596168, 4148940, 4701711, 4701711, 5567741, 4388453, 5254483, 6120513, 4594245, 4280987, 5147017, 5147017, 4833759, 5699789, 5386530, 6252560, 5939302, 3547005, 4413035, 4413035, 4965806, 4965806, 5831836, 5831836, 4858340]
noncomputable def qReLo6 (i : Fin 29) : ℚ := (bReLo6[i.val]! : ℚ) / 1000000
noncomputable def qReHi6 (i : Fin 29) : ℚ := (bReHi6[i.val]! : ℚ) / 1000000
noncomputable def qImLo6 (i : Fin 29) : ℚ := (bImLo6[i.val]! : ℚ) / 1000000
noncomputable def qImHi6 (i : Fin 29) : ℚ := (bImHi6[i.val]! : ℚ) / 1000000

set_option maxHeartbeats 2000000 in
lemma hval6 : ∀ i : Fin 29, ((qReLo6 i : ℚ):ℝ) ≤ (vtx i).re ∧ (vtx i).re ≤ ((qReHi6 i:ℚ):ℝ) ∧
    ((qImLo6 i:ℚ):ℝ) ≤ (vtx i).im ∧ (vtx i).im ≤ ((qImHi6 i:ℚ):ℝ) := by
  intro i; fin_cases i
  · show (((2522366/1000000 : ℚ)):ℝ) ≤ ((⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)).re ∧ ((⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)).re ≤ (((2522370/1000000 : ℚ)):ℝ) ∧ (((3998271/1000000 : ℚ)):ℝ) ≤ ((⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)).im ∧ ((⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165, (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)).im ≤ (((3998292/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((2442151/1000000 : ℚ)):ℝ) ≤ ((⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)).re ∧ ((⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)).re ≤ (((2442161/1000000 : ℚ)):ℝ) ∧ (((3687729/1000000 : ℚ)):ℝ) ≤ ((⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)).im ∧ ((⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11), (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)).im ≤ (((3687754/1000000 : ℚ)):ℝ)
    -- `nlinarith` fallback retained here (unlike the other vertices): the `i = 1` vertex
    -- involves the nested radical `v1Radical`, so plain `linarith` does not close all bounds.
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [] <;> push_cast <;> first | linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u] | nlinarith [s3l, s3u, s11l, s11u, s33l, s33u, vNl, vNu, hN0, Real.sqrt_nonneg 3, Real.sqrt_nonneg 11, Real.sqrt_nonneg 33]
  · show (((4666666/1000000 : ℚ)):ℝ) ≤ ((baseVert (14/3) 0 2 (1/3))).re ∧ ((baseVert (14/3) 0 2 (1/3))).re ≤ (((4666667/1000000 : ℚ)):ℝ) ∧ (((4569640/1000000 : ℚ)):ℝ) ≤ ((baseVert (14/3) 0 2 (1/3))).im ∧ ((baseVert (14/3) 0 2 (1/3))).im ≤ (((4569664/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4500000/1000000 : ℚ)):ℝ) ≤ ((baseVert (9/2) 0 2 (1/2))).re ∧ ((baseVert (9/2) 0 2 (1/2))).re ≤ (((4500000/1000000 : ℚ)):ℝ) ∧ (((5122410/1000000 : ℚ)):ℝ) ≤ ((baseVert (9/2) 0 2 (1/2))).im ∧ ((baseVert (9/2) 0 2 (1/2))).im ≤ (((5122435/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3437952/1000000 : ℚ)):ℝ) ≤ ((baseVert (47/12) (-1/12) (23/12) (1/12))).re ∧ ((baseVert (47/12) (-1/12) (23/12) (1/12))).re ≤ (((3437954/1000000 : ℚ)):ℝ) ∧ (((3596147/1000000 : ℚ)):ℝ) ≤ ((baseVert (47/12) (-1/12) (23/12) (1/12))).im ∧ ((baseVert (47/12) (-1/12) (23/12) (1/12))).im ≤ (((3596168/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4271285/1000000 : ℚ)):ℝ) ≤ ((baseVert (19/4) (-1/12) (23/12) (1/4))).re ∧ ((baseVert (19/4) (-1/12) (23/12) (1/4))).re ≤ (((4271287/1000000 : ℚ)):ℝ) ∧ (((4148917/1000000 : ℚ)):ℝ) ≤ ((baseVert (19/4) (-1/12) (23/12) (1/4))).im ∧ ((baseVert (19/4) (-1/12) (23/12) (1/4))).im ≤ (((4148940/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4104619/1000000 : ℚ)):ℝ) ≤ ((baseVert (55/12) (-1/12) (23/12) (5/12))).re ∧ ((baseVert (55/12) (-1/12) (23/12) (5/12))).re ≤ (((4104620/1000000 : ℚ)):ℝ) ∧ (((4701687/1000000 : ℚ)):ℝ) ≤ ((baseVert (55/12) (-1/12) (23/12) (5/12))).im ∧ ((baseVert (55/12) (-1/12) (23/12) (5/12))).im ≤ (((4701711/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((5104619/1000000 : ℚ)):ℝ) ≤ ((baseVert (67/12) (-1/12) (23/12) (5/12))).re ∧ ((baseVert (67/12) (-1/12) (23/12) (5/12))).re ≤ (((5104620/1000000 : ℚ)):ℝ) ∧ (((4701687/1000000 : ℚ)):ℝ) ≤ ((baseVert (67/12) (-1/12) (23/12) (5/12))).im ∧ ((baseVert (67/12) (-1/12) (23/12) (5/12))).im ≤ (((4701711/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4604619/1000000 : ℚ)):ℝ) ≤ ((baseVert (61/12) (-1/12) (29/12) (5/12))).re ∧ ((baseVert (61/12) (-1/12) (29/12) (5/12))).re ≤ (((4604620/1000000 : ℚ)):ℝ) ∧ (((5567712/1000000 : ℚ)):ℝ) ≤ ((baseVert (61/12) (-1/12) (29/12) (5/12))).im ∧ ((baseVert (61/12) (-1/12) (29/12) (5/12))).im ≤ (((5567741/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4437952/1000000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/12) (17/12) (7/12))).re ∧ ((baseVert (59/12) (-1/12) (17/12) (7/12))).re ≤ (((4437954/1000000 : ℚ)):ℝ) ∧ (((4388432/1000000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/12) (17/12) (7/12))).im ∧ ((baseVert (59/12) (-1/12) (17/12) (7/12))).im ≤ (((4388453/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4937952/1000000 : ℚ)):ℝ) ≤ ((baseVert (65/12) (-1/12) (23/12) (7/12))).re ∧ ((baseVert (65/12) (-1/12) (23/12) (7/12))).re ≤ (((4937954/1000000 : ℚ)):ℝ) ∧ (((5254457/1000000 : ℚ)):ℝ) ≤ ((baseVert (65/12) (-1/12) (23/12) (7/12))).im ∧ ((baseVert (65/12) (-1/12) (23/12) (7/12))).im ≤ (((5254483/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4437952/1000000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/12) (29/12) (7/12))).re ∧ ((baseVert (59/12) (-1/12) (29/12) (7/12))).re ≤ (((4437954/1000000 : ℚ)):ℝ) ∧ (((6120482/1000000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/12) (29/12) (7/12))).im ∧ ((baseVert (59/12) (-1/12) (29/12) (7/12))).im ≤ (((6120513/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4375905/1000000 : ℚ)):ℝ) ≤ ((baseVert (16/3) (-1/6) (7/3) (1/6))).re ∧ ((baseVert (16/3) (-1/6) (7/3) (1/6))).re ≤ (((4375907/1000000 : ℚ)):ℝ) ∧ (((4594220/1000000 : ℚ)):ℝ) ≤ ((baseVert (16/3) (-1/6) (7/3) (1/6))).im ∧ ((baseVert (16/3) (-1/6) (7/3) (1/6))).im ≤ (((4594245/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4709238/1000000 : ℚ)):ℝ) ≤ ((baseVert (17/3) (-1/6) (11/6) (1/3))).re ∧ ((baseVert (17/3) (-1/6) (11/6) (1/3))).re ≤ (((4709240/1000000 : ℚ)):ℝ) ∧ (((4280965/1000000 : ℚ)):ℝ) ≤ ((baseVert (17/3) (-1/6) (11/6) (1/3))).im ∧ ((baseVert (17/3) (-1/6) (11/6) (1/3))).im ≤ (((4280987/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3209238/1000000 : ℚ)):ℝ) ≤ ((baseVert (25/6) (-1/6) (7/3) (1/3))).re ∧ ((baseVert (25/6) (-1/6) (7/3) (1/3))).re ≤ (((3209240/1000000 : ℚ)):ℝ) ∧ (((5146990/1000000 : ℚ)):ℝ) ≤ ((baseVert (25/6) (-1/6) (7/3) (1/3))).im ∧ ((baseVert (25/6) (-1/6) (7/3) (1/3))).im ≤ (((5147017/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4209238/1000000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/6) (7/3) (1/3))).re ∧ ((baseVert (31/6) (-1/6) (7/3) (1/3))).re ≤ (((4209240/1000000 : ℚ)):ℝ) ∧ (((5146990/1000000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/6) (7/3) (1/3))).im ∧ ((baseVert (31/6) (-1/6) (7/3) (1/3))).im ≤ (((5147017/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4542571/1000000 : ℚ)):ℝ) ≤ ((baseVert (11/2) (-1/6) (11/6) (1/2))).re ∧ ((baseVert (11/2) (-1/6) (11/6) (1/2))).re ≤ (((4542574/1000000 : ℚ)):ℝ) ∧ (((4833735/1000000 : ℚ)):ℝ) ≤ ((baseVert (11/2) (-1/6) (11/6) (1/2))).im ∧ ((baseVert (11/2) (-1/6) (11/6) (1/2))).im ≤ (((4833759/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4042571/1000000 : ℚ)):ℝ) ≤ ((baseVert 5 (-1/6) (7/3) (1/2))).re ∧ ((baseVert 5 (-1/6) (7/3) (1/2))).re ≤ (((4042574/1000000 : ℚ)):ℝ) ∧ (((5699760/1000000 : ℚ)):ℝ) ≤ ((baseVert 5 (-1/6) (7/3) (1/2))).im ∧ ((baseVert 5 (-1/6) (7/3) (1/2))).im ≤ (((5699789/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3375905/1000000 : ℚ)):ℝ) ≤ ((baseVert (13/3) (-1/6) (11/6) (2/3))).re ∧ ((baseVert (13/3) (-1/6) (11/6) (2/3))).re ≤ (((3375907/1000000 : ℚ)):ℝ) ∧ (((5386505/1000000 : ℚ)):ℝ) ≤ ((baseVert (13/3) (-1/6) (11/6) (2/3))).im ∧ ((baseVert (13/3) (-1/6) (11/6) (2/3))).im ≤ (((5386530/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3875905/1000000 : ℚ)):ℝ) ≤ ((baseVert (29/6) (-1/6) (7/3) (2/3))).re ∧ ((baseVert (29/6) (-1/6) (7/3) (2/3))).re ≤ (((3875907/1000000 : ℚ)):ℝ) ∧ (((6252530/1000000 : ℚ)):ℝ) ≤ ((baseVert (29/6) (-1/6) (7/3) (2/3))).im ∧ ((baseVert (29/6) (-1/6) (7/3) (2/3))).im ≤ (((6252560/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4209238/1000000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/6) (11/6) (5/6))).re ∧ ((baseVert (31/6) (-1/6) (11/6) (5/6))).re ≤ (((4209240/1000000 : ℚ)):ℝ) ∧ (((5939275/1000000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/6) (11/6) (5/6))).im ∧ ((baseVert (31/6) (-1/6) (11/6) (5/6))).im ≤ (((5939302/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3647190/1000000 : ℚ)):ℝ) ≤ ((baseVert (61/12) (-1/4) (5/4) (5/12))).re ∧ ((baseVert (61/12) (-1/4) (5/4) (5/12))).re ≤ (((3647194/1000000 : ℚ)):ℝ) ∧ (((3546987/1000000 : ℚ)):ℝ) ≤ ((baseVert (61/12) (-1/4) (5/4) (5/12))).im ∧ ((baseVert (61/12) (-1/4) (5/4) (5/12))).im ≤ (((3547005/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3147190/1000000 : ℚ)):ℝ) ≤ ((baseVert (55/12) (-1/4) (7/4) (5/12))).re ∧ ((baseVert (55/12) (-1/4) (7/4) (5/12))).re ≤ (((3147194/1000000 : ℚ)):ℝ) ∧ (((4413012/1000000 : ℚ)):ℝ) ≤ ((baseVert (55/12) (-1/4) (7/4) (5/12))).im ∧ ((baseVert (55/12) (-1/4) (7/4) (5/12))).im ≤ (((4413035/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4147190/1000000 : ℚ)):ℝ) ≤ ((baseVert (67/12) (-1/4) (7/4) (5/12))).re ∧ ((baseVert (67/12) (-1/4) (7/4) (5/12))).re ≤ (((4147194/1000000 : ℚ)):ℝ) ∧ (((4413012/1000000 : ℚ)):ℝ) ≤ ((baseVert (67/12) (-1/4) (7/4) (5/12))).im ∧ ((baseVert (67/12) (-1/4) (7/4) (5/12))).im ≤ (((4413035/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((2980524/1000000 : ℚ)):ℝ) ≤ ((baseVert (53/12) (-1/4) (7/4) (7/12))).re ∧ ((baseVert (53/12) (-1/4) (7/4) (7/12))).re ≤ (((2980527/1000000 : ℚ)):ℝ) ∧ (((4965782/1000000 : ℚ)):ℝ) ≤ ((baseVert (53/12) (-1/4) (7/4) (7/12))).im ∧ ((baseVert (53/12) (-1/4) (7/4) (7/12))).im ≤ (((4965806/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3980524/1000000 : ℚ)):ℝ) ≤ ((baseVert (65/12) (-1/4) (7/4) (7/12))).re ∧ ((baseVert (65/12) (-1/4) (7/4) (7/12))).re ≤ (((3980527/1000000 : ℚ)):ℝ) ∧ (((4965782/1000000 : ℚ)):ℝ) ≤ ((baseVert (65/12) (-1/4) (7/4) (7/12))).im ∧ ((baseVert (65/12) (-1/4) (7/4) (7/12))).im ≤ (((4965806/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3480524/1000000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/4) (9/4) (7/12))).re ∧ ((baseVert (59/12) (-1/4) (9/4) (7/12))).re ≤ (((3480527/1000000 : ℚ)):ℝ) ∧ (((5831807/1000000 : ℚ)):ℝ) ≤ ((baseVert (59/12) (-1/4) (9/4) (7/12))).im ∧ ((baseVert (59/12) (-1/4) (9/4) (7/12))).im ≤ (((5831836/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((4480524/1000000 : ℚ)):ℝ) ≤ ((baseVert (71/12) (-1/4) (9/4) (7/12))).re ∧ ((baseVert (71/12) (-1/4) (9/4) (7/12))).re ≤ (((4480527/1000000 : ℚ)):ℝ) ∧ (((5831807/1000000 : ℚ)):ℝ) ≤ ((baseVert (71/12) (-1/4) (9/4) (7/12))).im ∧ ((baseVert (71/12) (-1/4) (9/4) (7/12))).im ≤ (((5831836/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]
  · show (((3251810/1000000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/3) (13/6) (1/3))).re ∧ ((baseVert (31/6) (-1/3) (13/6) (1/3))).re ≤ (((3251814/1000000 : ℚ)):ℝ) ∧ (((4858315/1000000 : ℚ)):ℝ) ≤ ((baseVert (31/6) (-1/3) (13/6) (1/3))).im ∧ ((baseVert (31/6) (-1/3) (13/6) (1/3))).im ≤ (((4858340/1000000 : ℚ)):ℝ)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [baseVert] <;> push_cast <;> linarith [s3l, s3u, s5l, s5u, s11l, s11u, s15l, s15u, s33l, s33u, s165l, s165u, vN3l, vN3u, vN11l, vN11u]

/-! ### Squared-distance interval bounds (integer-scaled), applied by term -/

lemma sqdist_ge_int (i j : Fin 29) :
    ((iCLo (bReLo6[i.val]!) (bReHi6[i.val]!) (bReLo6[j.val]!) (bReHi6[j.val]!)
      + iCLo (bImLo6[i.val]!) (bImHi6[i.val]!) (bImLo6[j.val]!) (bImHi6[j.val]!) : ℤ) : ℝ)
      / 1000000000000
      ≤ ((vtx i).re - (vtx j).re) ^ 2 + ((vtx i).im - (vtx j).im) ^ 2 := by
  obtain ⟨a1, a2, a3, a4⟩ := hval6 i
  obtain ⟨b1, b2, b3, b4⟩ := hval6 j
  have hre := cLo_le a1 a2 b1 b2
  have him := cLo_le a3 a4 b3 b4
  simp only [qReLo6, qReHi6, qImLo6, qImHi6, cLo_int] at hre him
  push_cast at hre him ⊢
  linarith

lemma sqdist_le_int (i j : Fin 29) :
    ((vtx i).re - (vtx j).re) ^ 2 + ((vtx i).im - (vtx j).im) ^ 2 ≤
    ((iCHi (bReLo6[i.val]!) (bReHi6[i.val]!) (bReLo6[j.val]!) (bReHi6[j.val]!)
      + iCHi (bImLo6[i.val]!) (bImHi6[i.val]!) (bImLo6[j.val]!) (bImHi6[j.val]!) : ℤ) : ℝ)
      / 1000000000000 := by
  obtain ⟨a1, a2, a3, a4⟩ := hval6 i
  obtain ⟨b1, b2, b3, b4⟩ := hval6 j
  have hre := le_cHi a1 a2 b1 b2
  have him := le_cHi a3 a4 b3 b4
  simp only [qReLo6, qReHi6, qImLo6, qImHi6, cHi_int] at hre him
  push_cast at hre him ⊢
  linarith

/-- Edge `v₁ ~ v₄` in the ordered enumeration (`v₁` written in `v1Radical` form). -/
lemma dist_e_1_4 : dist (vtx 1) (vtx 4) = 1 := by
  have h1 : vtx 1 = (⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33
        + (-1/8) * v1Radical * ((-1/12) * Real.sqrt 3 + (1/4) * Real.sqrt 11),
      (1/8) * v1Radical * ((3/4) + (-1/12) * Real.sqrt 33)
        + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ) := by
    simp only [vtx, Matrix.cons_val_one, Complex.ext_iff]
    constructor <;> push_cast <;> ring
  have h4 : vtx 4 = (⟨(47/12 : ℝ) + (-1/12) * Real.sqrt 33,
      (1/12) * Real.sqrt 11 + (23/12) * Real.sqrt 3⟩ : ℂ) := by
    show (baseVert (47/12) (-1/12) (23/12) (1/12) : ℂ) = _
    simp only [baseVert, Complex.ext_iff]
    constructor <;> push_cast <;> ring
  rw [h1, h4]; exact dist_v1_v4

/-! ### The adjacency matrix `H` (51 edges) and its match with `dist = 1` -/
def edgeListN : List (ℕ × ℕ) := [(0, 4), (1, 4), (2, 8), (3, 5), (3, 11), (4, 5), (5, 7), (5, 15), (6, 7), (6, 8), (6, 10), (6, 14), (6, 17), (6, 18), (6, 22), (7, 8), (7, 15), (7, 23), (8, 12), (8, 19), (9, 10), (10, 11), (10, 13), (10, 17), (10, 20), (10, 25), (11, 15), (11, 26), (13, 15), (13, 25), (14, 15), (14, 17), (15, 26), (15, 28), (16, 17), (16, 27), (18, 19), (18, 20), (18, 22), (20, 25), (21, 22), (21, 23), (22, 23), (22, 25), (23, 28), (24, 25), (24, 26), (25, 26), (25, 27), (26, 27), (26, 28)]

/-- Bool adjacency: `(i,j)` (either orientation) is one of the 51 edges. -/
def adjB (i j : ℕ) : Bool :=
  edgeListN.any (fun p => (p.1 == i && p.2 == j) || (p.1 == j && p.2 == i))

/-- Bulk interval non-edge check: for every non-edge pair, the box `dist²` interval excludes 1. -/
def nonEdgeOk : Bool := (List.range 29).all (fun i => (List.range 29).all (fun j =>
  adjB i j
  || decide (1000000000000 < iCLo (bReLo6[i]!) (bReHi6[i]!) (bReLo6[j]!) (bReHi6[j]!)
                    + iCLo (bImLo6[i]!) (bImHi6[i]!) (bImLo6[j]!) (bImHi6[j]!))
  || decide (iCHi (bReLo6[i]!) (bReHi6[i]!) (bReLo6[j]!) (bReHi6[j]!)
                    + iCHi (bImLo6[i]!) (bImHi6[i]!) (bImLo6[j]!) (bImHi6[j]!) < 1000000000000)))

lemma nonEdgeOk_true : nonEdgeOk = true := by decide

def edgeList : List (Fin 29 × Fin 29) := [((0 : Fin 29), (4 : Fin 29)), ((1 : Fin 29), (4 : Fin 29)), ((2 : Fin 29), (8 : Fin 29)), ((3 : Fin 29), (5 : Fin 29)), ((3 : Fin 29), (11 : Fin 29)), ((4 : Fin 29), (5 : Fin 29)), ((5 : Fin 29), (7 : Fin 29)), ((5 : Fin 29), (15 : Fin 29)), ((6 : Fin 29), (7 : Fin 29)), ((6 : Fin 29), (8 : Fin 29)), ((6 : Fin 29), (10 : Fin 29)), ((6 : Fin 29), (14 : Fin 29)), ((6 : Fin 29), (17 : Fin 29)), ((6 : Fin 29), (18 : Fin 29)), ((6 : Fin 29), (22 : Fin 29)), ((7 : Fin 29), (8 : Fin 29)), ((7 : Fin 29), (15 : Fin 29)), ((7 : Fin 29), (23 : Fin 29)), ((8 : Fin 29), (12 : Fin 29)), ((8 : Fin 29), (19 : Fin 29)), ((9 : Fin 29), (10 : Fin 29)), ((10 : Fin 29), (11 : Fin 29)), ((10 : Fin 29), (13 : Fin 29)), ((10 : Fin 29), (17 : Fin 29)), ((10 : Fin 29), (20 : Fin 29)), ((10 : Fin 29), (25 : Fin 29)), ((11 : Fin 29), (15 : Fin 29)), ((11 : Fin 29), (26 : Fin 29)), ((13 : Fin 29), (15 : Fin 29)), ((13 : Fin 29), (25 : Fin 29)), ((14 : Fin 29), (15 : Fin 29)), ((14 : Fin 29), (17 : Fin 29)), ((15 : Fin 29), (26 : Fin 29)), ((15 : Fin 29), (28 : Fin 29)), ((16 : Fin 29), (17 : Fin 29)), ((16 : Fin 29), (27 : Fin 29)), ((18 : Fin 29), (19 : Fin 29)), ((18 : Fin 29), (20 : Fin 29)), ((18 : Fin 29), (22 : Fin 29)), ((20 : Fin 29), (25 : Fin 29)), ((21 : Fin 29), (22 : Fin 29)), ((21 : Fin 29), (23 : Fin 29)), ((22 : Fin 29), (23 : Fin 29)), ((22 : Fin 29), (25 : Fin 29)), ((23 : Fin 29), (28 : Fin 29)), ((24 : Fin 29), (25 : Fin 29)), ((24 : Fin 29), (26 : Fin 29)), ((25 : Fin 29), (26 : Fin 29)), ((25 : Fin 29), (27 : Fin 29)), ((26 : Fin 29), (27 : Fin 29)), ((26 : Fin 29), (28 : Fin 29))]

set_option maxHeartbeats 1000000 in
/-- Each of the 51 edges is genuinely at unit distance. -/
lemma edgeList_dist : ∀ p ∈ edgeList, dist (vtx p.1) (vtx p.2) = 1 := by
  intro p hp
  fin_cases hp
  · show dist (vtx 0) (vtx 4) = 1
    rw [veq_0, veq_4]; exact dist_v0_v4
  · show dist (vtx 1) (vtx 4) = 1
    exact dist_e_1_4
  · show dist (baseVert (14/3) 0 2 (1/3)) (baseVert (61/12) (-1/12) (29/12) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (9/2) 0 2 (1/2)) (baseVert (19/4) (-1/12) (23/12) (1/4)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (9/2) 0 2 (1/2)) (baseVert (59/12) (-1/12) (29/12) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (47/12) (-1/12) (23/12) (1/12)) (baseVert (19/4) (-1/12) (23/12) (1/4)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (19/4) (-1/12) (23/12) (1/4)) (baseVert (67/12) (-1/12) (23/12) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (19/4) (-1/12) (23/12) (1/4)) (baseVert (31/6) (-1/6) (7/3) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/12) (23/12) (5/12)) (baseVert (67/12) (-1/12) (23/12) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/12) (23/12) (5/12)) (baseVert (61/12) (-1/12) (29/12) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/12) (23/12) (5/12)) (baseVert (65/12) (-1/12) (23/12) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/12) (23/12) (5/12)) (baseVert (25/6) (-1/6) (7/3) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/12) (23/12) (5/12)) (baseVert 5 (-1/6) (7/3) (1/2)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/12) (23/12) (5/12)) (baseVert (13/3) (-1/6) (11/6) (2/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/12) (23/12) (5/12)) (baseVert (55/12) (-1/4) (7/4) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (67/12) (-1/12) (23/12) (5/12)) (baseVert (61/12) (-1/12) (29/12) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (67/12) (-1/12) (23/12) (5/12)) (baseVert (31/6) (-1/6) (7/3) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (67/12) (-1/12) (23/12) (5/12)) (baseVert (67/12) (-1/4) (7/4) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (61/12) (-1/12) (29/12) (5/12)) (baseVert (16/3) (-1/6) (7/3) (1/6)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (61/12) (-1/12) (29/12) (5/12)) (baseVert (29/6) (-1/6) (7/3) (2/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (59/12) (-1/12) (17/12) (7/12)) (baseVert (65/12) (-1/12) (23/12) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (65/12) (-1/12) (23/12) (7/12)) (baseVert (59/12) (-1/12) (29/12) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (65/12) (-1/12) (23/12) (7/12)) (baseVert (17/3) (-1/6) (11/6) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (65/12) (-1/12) (23/12) (7/12)) (baseVert 5 (-1/6) (7/3) (1/2)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (65/12) (-1/12) (23/12) (7/12)) (baseVert (31/6) (-1/6) (11/6) (5/6)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (65/12) (-1/12) (23/12) (7/12)) (baseVert (65/12) (-1/4) (7/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (59/12) (-1/12) (29/12) (7/12)) (baseVert (31/6) (-1/6) (7/3) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (59/12) (-1/12) (29/12) (7/12)) (baseVert (59/12) (-1/4) (9/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (17/3) (-1/6) (11/6) (1/3)) (baseVert (31/6) (-1/6) (7/3) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (17/3) (-1/6) (11/6) (1/3)) (baseVert (65/12) (-1/4) (7/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (25/6) (-1/6) (7/3) (1/3)) (baseVert (31/6) (-1/6) (7/3) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (25/6) (-1/6) (7/3) (1/3)) (baseVert 5 (-1/6) (7/3) (1/2)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (31/6) (-1/6) (7/3) (1/3)) (baseVert (59/12) (-1/4) (9/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (31/6) (-1/6) (7/3) (1/3)) (baseVert (31/6) (-1/3) (13/6) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (11/2) (-1/6) (11/6) (1/2)) (baseVert 5 (-1/6) (7/3) (1/2)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (11/2) (-1/6) (11/6) (1/2)) (baseVert (71/12) (-1/4) (9/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (13/3) (-1/6) (11/6) (2/3)) (baseVert (29/6) (-1/6) (7/3) (2/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (13/3) (-1/6) (11/6) (2/3)) (baseVert (31/6) (-1/6) (11/6) (5/6)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (13/3) (-1/6) (11/6) (2/3)) (baseVert (55/12) (-1/4) (7/4) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (31/6) (-1/6) (11/6) (5/6)) (baseVert (65/12) (-1/4) (7/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (61/12) (-1/4) (5/4) (5/12)) (baseVert (55/12) (-1/4) (7/4) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (61/12) (-1/4) (5/4) (5/12)) (baseVert (67/12) (-1/4) (7/4) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/4) (7/4) (5/12)) (baseVert (67/12) (-1/4) (7/4) (5/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (55/12) (-1/4) (7/4) (5/12)) (baseVert (65/12) (-1/4) (7/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (67/12) (-1/4) (7/4) (5/12)) (baseVert (31/6) (-1/3) (13/6) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (53/12) (-1/4) (7/4) (7/12)) (baseVert (65/12) (-1/4) (7/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (53/12) (-1/4) (7/4) (7/12)) (baseVert (59/12) (-1/4) (9/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (65/12) (-1/4) (7/4) (7/12)) (baseVert (59/12) (-1/4) (9/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (65/12) (-1/4) (7/4) (7/12)) (baseVert (71/12) (-1/4) (9/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (59/12) (-1/4) (9/4) (7/12)) (baseVert (71/12) (-1/4) (9/4) (7/12)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num
  · show dist (baseVert (59/12) (-1/4) (9/4) (7/12)) (baseVert (31/6) (-1/3) (13/6) (1/3)) = 1
    rw [dist_baseVert_eq_one_iff]; norm_num

/-! ### The two adjacency directions, then the equivalence `H.Adj ↔ dist = 1` -/

/-- **Non-edges** are settled uniformly by the bulk interval check. -/
lemma hadj_nonedge (i j : Fin 29) (h : adjB i.val j.val = false) :
    dist (vtx i) (vtx j) ≠ 1 := by
  intro hd
  rw [Complex.dist_eq_re_im, Real.sqrt_eq_one] at hd
  have hall := (List.all_eq_true.mp ((List.all_eq_true.mp nonEdgeOk_true) i.val
    (List.mem_range.mpr i.isLt))) j.val (List.mem_range.mpr j.isLt)
  simp only [h, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hall
  rcases hall with hlo | hhi
  · have hge := sqdist_ge_int i j
    rw [hd, div_le_one (by norm_num : (0:ℝ) < 1000000000000)] at hge
    have : (1000000000000 : ℝ) <
        ((iCLo (bReLo6[i.val]!) (bReHi6[i.val]!) (bReLo6[j.val]!) (bReHi6[j.val]!)
          + iCLo (bImLo6[i.val]!) (bImHi6[i.val]!) (bImLo6[j.val]!) (bImHi6[j.val]!) : ℤ) : ℝ) := by
      exact_mod_cast hlo
    linarith
  · have hle := sqdist_le_int i j
    rw [hd, le_div_iff₀ (by norm_num : (0:ℝ) < 1000000000000)] at hle
    have : ((iCHi (bReLo6[i.val]!) (bReHi6[i.val]!) (bReLo6[j.val]!) (bReHi6[j.val]!)
          + iCHi (bImLo6[i.val]!) (bImHi6[i.val]!) (bImLo6[j.val]!) (bImHi6[j.val]!) : ℤ) : ℝ)
        < 1000000000000 := by exact_mod_cast hhi
    linarith

/-- The Bool matrix's `true` entries are exactly the listed edges (either orientation). -/
lemma adjB_true_mem : ∀ i j : Fin 29, adjB i.val j.val = true →
    (i, j) ∈ edgeList ∨ (j, i) ∈ edgeList := by decide

/-- **Edges** are the exact `dist = 1` facts. -/
lemma hadj_edge (i j : Fin 29) (h : adjB i.val j.val = true) : dist (vtx i) (vtx j) = 1 := by
  rcases adjB_true_mem i j h with hm | hm
  · exact edgeList_dist _ hm
  · rw [dist_comm]; exact edgeList_dist _ hm

lemma H_symm : ∀ i j : Fin 29, adjB i.val j.val = true → adjB j.val i.val = true := by decide
lemma H_loopless : ∀ i : Fin 29, ¬ (adjB i.val i.val = true) := by decide

/-- The computable adjacency matrix `H` on `Fin 29`. -/
def H : SimpleGraph (Fin 29) where
  Adj i j := adjB i.val j.val = true
  symm := ⟨fun i j h => H_symm i j h⟩
  loopless := ⟨fun i h => H_loopless i h⟩

instance : DecidableRel H.Adj := fun i j => decidable_of_iff (adjB i.val j.val = true) Iff.rfl

/-- **The adjacency matrix matches the geometric relation** — hypothesis 2 of
`indepSets_eq_image_indepEnum` for `f = vtx`. -/
lemma H_adj_iff (i j : Fin 29) : H.Adj i j ↔ planeGraph.Adj (vtx i) (vtx j) := by
  show (adjB i.val j.val = true) ↔ dist (vtx i) (vtx j) = 1
  rcases Bool.eq_false_or_eq_true (adjB i.val j.val) with h | h
  · rw [h]; simpa using hadj_edge i j h
  · rw [h]; simpa using hadj_nonedge i j h

end UnitDistanceGraphs
