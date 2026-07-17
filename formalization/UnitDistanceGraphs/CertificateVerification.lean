/-
Final assembly of **[DV26] Lemma 1**: `chi_gf_G29_gt : 4 < χ_gf G₂₉` (Component 2).

This is the top of the Component-2 tower — the only file with access to *both* the geometric
enumeration (`G29Vertices`: `vtx`, `H`, `vtx_injective`, `H_adj_iff`, `G29 = image vtx`) and the
arithmetic dual certificate data (`CertificateData`: the congruence/weight strings and `certNum`/`certDen`).
The certificate's per-atom feasibility is (re)proved here as `feasBM`/`cert_per_atom`.

It applies `geomFractionalChromaticNumber_ge_of_dual` (weak LP duality, from `Definitions`) with
`c = certNum / certDen > 4`, discharging its hypotheses via the certificate:

* `hv0`      — `v0 ∈ G₂₉` (proved inline from the `G29` definition);
* `L, R, y`  — the 16859 congruence pairs and dual weights, decoded from the certificate strings
               into `Finset ℂ` / `ℝ` families;
* `hLV/hRV`  — each decoded set is a subset of `G₂₉`;
* `hcong`    — each `(Lᵢ, Rᵢ)` is a genuine ℂ-isometry image (the geometric congruences);
* `hne`      — a geometric fractional coloring of `G₂₉` exists;
* `hfeas`    — the per-independent-set dual feasibility, obtained by transporting `cert_per_atom`
               along `indepSets_eq_image_indepEnum` (the `Finset (Fin 29) ↔ bitmask` bridge).

Then `cert_value_gt_four` (`4·certDen < certNum`) gives `4 < c ≤ χ_gf G₂₉`.
-/

import UnitDistanceGraphs.G29Vertices
import UnitDistanceGraphs.CertificateData
import UnitDistanceGraphs.PlaneIsometry

namespace UnitDistanceGraphs

open scoped Classical

/-! ### Decoding the certificate strings into geometric families

The certificate (`CertificateData.lean`) stores the 16859 congruence pairs and dual weights as
space-separated `UInt32` bitmasks / `Int`s. Here we parse them into `Finset ℂ` / `ℝ` families
indexed by `Fin numCong`, so they can feed `geomFractionalChromaticNumber_ge_of_dual`. A bitmask
`m` encodes the vertex subset `{k : Fin 29 | m.testBit k}`, imaged into `ℂ` by `vtx`. -/

/-- Parse a space-separated string of `Nat` bitmasks. -/
def parseMasks (s : String) : Array UInt32 :=
  (s.splitOn " ").toArray.map (fun t => (t.toNat!).toUInt32)

/-- Parse a space-separated string of `Int`s. -/
def parseInts (s : String) : Array Int :=
  (s.splitOn " ").toArray.map (fun t => t.toInt!)

def congLArr : Array UInt32 := parseMasks Certificate.congLStr
def congRArr : Array UInt32 := parseMasks Certificate.congRStr
def yArr : Array Int := parseInts Certificate.yStr

/-- Number of congruence pairs (16859). -/
def numCong : ℕ := congLArr.size

/-- The vertex subset of `Fin 29` encoded by a `Nat` bitmask. -/
def bitsToFinset (m : ℕ) : Finset (Fin 29) :=
  Finset.univ.filter (fun k => m.testBit k.val = true)

/-- The `i`-th congruence's left point set in `ℂ` (a subset of `G₂₉`). -/
noncomputable def Lfam (i : Fin numCong) : Finset ℂ :=
  (bitsToFinset (congLArr[i.val]!).toNat).image vtx

/-- The `i`-th congruence's right point set in `ℂ` (a subset of `G₂₉`). -/
noncomputable def Rfam (i : Fin numCong) : Finset ℂ :=
  (bitsToFinset (congRArr[i.val]!).toNat).image vtx

/-- The `i`-th dual weight (integer witness scaled by the common denominator `certDen`). -/
noncomputable def yfam (i : Fin numCong) : ℝ := (yArr[i.val]! : ℝ) / (Certificate.certDen : ℝ)

lemma Lfam_subset (i : Fin numCong) : Lfam i ⊆ G29 := by
  rw [Lfam, ← image_vtx_eq_G29]; exact Finset.image_subset_image (Finset.subset_univ _)

lemma Rfam_subset (i : Fin numCong) : Rfam i ⊆ G29 := by
  rw [Rfam, ← image_vtx_eq_G29]; exact Finset.image_subset_image (Finset.subset_univ _)

/-! ### A geometric fractional coloring exists (nonemptiness `hne`)

Unit weight on every singleton. Its marginal on `Y` counts the independent singletons `⊇ Y`, so it
depends only on `|Y|` (`|V|` for `∅`, `1` for a singleton, `0` for `|Y| ≥ 2`) — and congruence
preserves cardinality, so the coloring is geometric. -/

/-- The coloring placing unit weight on every singleton independent set. -/
noncomputable def singletonColoring : Finset ℂ → ℝ := fun S => if S.card = 1 then 1 else 0

lemma marginal_singletonColoring (Y : Finset ℂ) :
    marginal G29 singletonColoring Y
      = (((indepSets G29).filter (fun S => Y ⊆ S ∧ S.card = 1)).card : ℝ) := by
  unfold marginal singletonColoring
  rw [Finset.sum_boole, Finset.filter_filter]

lemma marginal_singleton_eq_zero {Y : Finset ℂ} (hY : 2 ≤ Y.card) :
    marginal G29 singletonColoring Y = 0 := by
  rw [marginal_singletonColoring, Finset.card_eq_zero.mpr, Nat.cast_zero]
  rw [Finset.filter_eq_empty_iff]
  rintro S _ ⟨hYS, hc⟩
  have := Finset.card_le_card hYS
  omega

lemma marginal_singletonColoring_singleton {x : ℂ} (hx : x ∈ G29) :
    marginal G29 singletonColoring {x} = 1 := by
  rw [marginal_singletonColoring]
  have : (indepSets G29).filter (fun S => {x} ⊆ S ∧ S.card = 1) = {{x}} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hsub, hc⟩
      obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp hc
      rw [Finset.singleton_subset_iff, Finset.mem_singleton] at hsub
      rw [hsub]
    · rintro rfl
      exact ⟨singleton_mem_indepSets hx, Finset.Subset.refl _, Finset.card_singleton _⟩
  rw [this, Finset.card_singleton, Nat.cast_one]

/-- **Nonemptiness**: `G₂₉` admits a geometric fractional coloring. -/
lemma exists_geomColoring : ∃ γ, IsGeometricFractionalColoring G29 γ := by
  refine ⟨singletonColoring, ?_, ?_⟩
  · refine ⟨fun S _ => ?_, fun x hx => ?_⟩
    · unfold singletonColoring; split <;> norm_num
    · rw [marginal_singletonColoring_singleton hx]
  · intro Y hY Y' hY' hcong
    obtain ⟨φ, rfl⟩ := hcong
    have hcard : (Y.image (φ : ℂ → ℂ)).card = Y.card :=
      Finset.card_image_of_injective _ φ.injective
    rcases eq_or_ne Y.card 0 with h0 | h0
    · rw [Finset.card_eq_zero.mp h0, Finset.image_empty]
    · rcases eq_or_ne Y.card 1 with h1 | h1
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
        rw [Finset.image_singleton]
        rw [Finset.mem_powerset, Finset.singleton_subset_iff] at hY
        rw [Finset.mem_powerset] at hY'
        rw [marginal_singletonColoring_singleton hY,
            marginal_singletonColoring_singleton (hY' (by rw [Finset.image_singleton]; exact Finset.mem_singleton_self _))]
      · rw [marginal_singleton_eq_zero (by omega), marginal_singleton_eq_zero (by omega)]

/-! ### The congruences (`hcong`)

Each certificate pair `(Lfam i, Rfam i)` is a genuine ℂ-isometry image, established through the
plane congruence-extension lemma `congruent_of_dist_eq` (`PlaneIsometry.lean`). -/

/-- Squared distance of two base vertices, in the field `ℚ(√33)` (`P + 2Q√33`). -/
lemma baseVert_distSq (a1 a2 a3 a4 b1 b2 b3 b4 : ℚ) :
    ((baseVert a1 a2 a3 a4).re - (baseVert b1 b2 b3 b4).re) ^ 2
      + ((baseVert a1 a2 a3 a4).im - (baseVert b1 b2 b3 b4).im) ^ 2
    = (((a1 - b1) ^ 2 + 33 * (a2 - b2) ^ 2 + 3 * (a3 - b3) ^ 2 + 11 * (a4 - b4) ^ 2 : ℚ) : ℝ)
      + 2 * (((a1 - b1) * (a2 - b2) + (a3 - b3) * (a4 - b4) : ℚ) : ℝ) * Real.sqrt 33 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h311 : Real.sqrt 3 * Real.sqrt 11 = Real.sqrt 33 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  simp only [baseVert]
  push_cast
  linear_combination ((a2 : ℝ) - b2) ^ 2 * (Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num))
    + ((a3 : ℝ) - b3) ^ 2 * h3 + ((a4 : ℝ) - b4) ^ 2 * h11
    + 2 * ((a3 : ℝ) - b3) * ((a4 : ℝ) - b4) * h311

/-- Distance of two base vertices as `√(P + 2Q√33)`. -/
lemma dist_baseVert_eq (a1 a2 a3 a4 b1 b2 b3 b4 : ℚ) :
    dist (baseVert a1 a2 a3 a4) (baseVert b1 b2 b3 b4)
    = Real.sqrt ((((a1 - b1) ^ 2 + 33 * (a2 - b2) ^ 2 + 3 * (a3 - b3) ^ 2 + 11 * (a4 - b4) ^ 2 : ℚ) : ℝ)
      + 2 * (((a1 - b1) * (a2 - b2) + (a3 - b3) * (a4 - b4) : ℚ) : ℝ) * Real.sqrt 33) := by
  rw [Complex.dist_eq_re_im, baseVert_distSq]

/-- Sample base congruence `{v₂, v₃} ≅ {v₂, v₅}` (both at squared distance `1/3`), validating the
`congruent_of_dist_eq` + `dist_baseVert_eq` pipeline end-to-end. -/
example : Congruent ({vtx 2, vtx 3} : Finset ℂ) {vtx 2, vtx 5} := by
  have himg : ∀ z w : ℂ, ({z, w} : Finset ℂ) = Finset.image ![z, w] Finset.univ := by
    intro z w
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide, Finset.image_insert,
      Finset.image_singleton]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [himg (vtx 2) (vtx 3), himg (vtx 2) (vtx 5)]
  refine congruent_of_dist_eq ![vtx 2, vtx 3] ![vtx 2, vtx 5] ?_
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one] <;>
    first
      | rfl
      | (show dist (baseVert _ _ _ _) (baseVert _ _ _ _) = dist (baseVert _ _ _ _) (baseVert _ _ _ _)
         rw [dist_baseVert_eq, dist_baseVert_eq]; norm_num)

/-- Base-vertex parameters (dummy for `v₀,v₁`): `re = p1 + p2√33`, `im = p3√3 + p4√11`. -/
def bp1 : Array ℚ := #[(0 : ℚ), (0 : ℚ), (14/3 : ℚ), (9/2 : ℚ), (47/12 : ℚ), (19/4 : ℚ), (55/12 : ℚ), (67/12 : ℚ), (61/12 : ℚ), (59/12 : ℚ), (65/12 : ℚ), (59/12 : ℚ), (16/3 : ℚ), (17/3 : ℚ), (25/6 : ℚ), (31/6 : ℚ), (11/2 : ℚ), (5 : ℚ), (13/3 : ℚ), (29/6 : ℚ), (31/6 : ℚ), (61/12 : ℚ), (55/12 : ℚ), (67/12 : ℚ), (53/12 : ℚ), (65/12 : ℚ), (59/12 : ℚ), (71/12 : ℚ), (31/6 : ℚ)]
def bp2 : Array ℚ := #[(0 : ℚ), (0 : ℚ), (0 : ℚ), (0 : ℚ), (-1/12 : ℚ), (-1/12 : ℚ), (-1/12 : ℚ), (-1/12 : ℚ), (-1/12 : ℚ), (-1/12 : ℚ), (-1/12 : ℚ), (-1/12 : ℚ), (-1/6 : ℚ), (-1/6 : ℚ), (-1/6 : ℚ), (-1/6 : ℚ), (-1/6 : ℚ), (-1/6 : ℚ), (-1/6 : ℚ), (-1/6 : ℚ), (-1/6 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), (-1/4 : ℚ), (-1/3 : ℚ)]
def bp3 : Array ℚ := #[(0 : ℚ), (0 : ℚ), (2 : ℚ), (2 : ℚ), (23/12 : ℚ), (23/12 : ℚ), (23/12 : ℚ), (23/12 : ℚ), (29/12 : ℚ), (17/12 : ℚ), (23/12 : ℚ), (29/12 : ℚ), (7/3 : ℚ), (11/6 : ℚ), (7/3 : ℚ), (7/3 : ℚ), (11/6 : ℚ), (7/3 : ℚ), (11/6 : ℚ), (7/3 : ℚ), (11/6 : ℚ), (5/4 : ℚ), (7/4 : ℚ), (7/4 : ℚ), (7/4 : ℚ), (7/4 : ℚ), (9/4 : ℚ), (9/4 : ℚ), (13/6 : ℚ)]
def bp4 : Array ℚ := #[(0 : ℚ), (0 : ℚ), (1/3 : ℚ), (1/2 : ℚ), (1/12 : ℚ), (1/4 : ℚ), (5/12 : ℚ), (5/12 : ℚ), (5/12 : ℚ), (7/12 : ℚ), (7/12 : ℚ), (7/12 : ℚ), (1/6 : ℚ), (1/3 : ℚ), (1/3 : ℚ), (1/3 : ℚ), (1/2 : ℚ), (1/2 : ℚ), (2/3 : ℚ), (2/3 : ℚ), (5/6 : ℚ), (5/12 : ℚ), (5/12 : ℚ), (5/12 : ℚ), (7/12 : ℚ), (7/12 : ℚ), (7/12 : ℚ), (7/12 : ℚ), (1/3 : ℚ)]

set_option maxHeartbeats 1000000 in
/-- Every base vertex `p ≥ 2` is `baseVert` of its stored parameters. -/
lemma vtx_base (p : Fin 29) (hp : 2 ≤ p.val) :
    vtx p = baseVert (bp1[p.val]!) (bp2[p.val]!) (bp3[p.val]!) (bp4[p.val]!) := by
  fin_cases p <;> first | (exact absurd hp (by decide)) | rfl

/-- Rational `P` in `dist²(vtx p)(vtx q) = P + 2Q√33` (base vertices). -/
def Pmat (p q : Fin 29) : ℚ :=
  (bp1[p.val]! - bp1[q.val]!) ^ 2 + 33 * (bp2[p.val]! - bp2[q.val]!) ^ 2
    + 3 * (bp3[p.val]! - bp3[q.val]!) ^ 2 + 11 * (bp4[p.val]! - bp4[q.val]!) ^ 2

/-- Rational `Q` in `dist²(vtx p)(vtx q) = P + 2Q√33` (base vertices). -/
def Qmat (p q : Fin 29) : ℚ :=
  (bp1[p.val]! - bp1[q.val]!) * (bp2[p.val]! - bp2[q.val]!)
    + (bp3[p.val]! - bp3[q.val]!) * (bp4[p.val]! - bp4[q.val]!)

/-- **Base-vertex distance in closed form**, uniform in `p, q`. -/
lemma dist_vtx_base (p q : Fin 29) (hp : 2 ≤ p.val) (hq : 2 ≤ q.val) :
    dist (vtx p) (vtx q) = Real.sqrt ((Pmat p q : ℝ) + 2 * (Qmat p q : ℝ) * Real.sqrt 33) := by
  rw [vtx_base p hp, vtx_base q hq, dist_baseVert_eq]
  simp only [Pmat, Qmat]

/-- **Base distances agree when their rational `(P, Q)` agree** — the bridge from a decidable
combinatorial check to the geometric distance equality needed by `congruent_of_dist_eq`. -/
lemma dist_vtx_eq {p q r s : Fin 29} (hp : 2 ≤ p.val) (hq : 2 ≤ q.val) (hr : 2 ≤ r.val)
    (hs : 2 ≤ s.val) (hP : Pmat p q = Pmat r s) (hQ : Qmat p q = Qmat r s) :
    dist (vtx p) (vtx q) = dist (vtx r) (vtx s) := by
  rw [dist_vtx_base p q hp hq, dist_vtx_base r s hr hs, hP, hQ]

/-! ### Positional congruence data (padded to length 12) and the uniform check -/

def amatArr : Array ℕ := (Certificate.amatStr.splitOn " ").toArray.map String.toNat!
def bmatArr : Array ℕ := (Certificate.bmatStr.splitOn " ").toArray.map String.toNat!

/-- `j`-th vertex of the `i`-th congruence's (padded) left list. -/
def amatFN (i j : ℕ) : Fin 29 := ⟨amatArr[i * 12 + j]! % 29, Nat.mod_lt _ (by norm_num)⟩
def bmatFN (i j : ℕ) : Fin 29 := ⟨bmatArr[i * 12 + j]! % 29, Nat.mod_lt _ (by norm_num)⟩
def amatF (i : ℕ) : Fin 12 → Fin 29 := fun j => amatFN i j.val
def bmatF (i : ℕ) : Fin 12 → Fin 29 := fun j => bmatFN i j.val

/-- Bulk check for all congruences except the 2 genuine `v₀/v₁` multi-congruences (`16609`,`16840`):
the padded lists realize the bitmask sets, and each pair of positions is either constant on both
sides or a matched pair of base vertices with equal `(P, Q)`. -/
def congOk : Bool := (List.range numCong).all (fun i =>
  (i == 16609 || i == 16840) ||
  (decide (Finset.image (amatF i) Finset.univ = bitsToFinset (congLArr[i]!).toNat) &&
   decide (Finset.image (bmatF i) Finset.univ = bitsToFinset (congRArr[i]!).toNat) &&
   (List.range 12).all (fun j => (List.range 12).all (fun k =>
     ((amatFN i j == amatFN i k) && (bmatFN i j == bmatFN i k)) ||
     (decide (2 ≤ (amatFN i j).val) && decide (2 ≤ (amatFN i k).val) &&
       decide (2 ≤ (bmatFN i j).val) && decide (2 ≤ (bmatFN i k).val) &&
      decide (Pmat (amatFN i j) (amatFN i k) = Pmat (bmatFN i j) (bmatFN i k)) &&
       decide (Qmat (amatFN i j) (amatFN i k) = Qmat (bmatFN i j) (bmatFN i k)))))))

lemma congOk_true : congOk = true := by native_decide

/-- Distance equality covering both the degenerate (constant) and base-vertex cases — the per-pair
obligation of `congruent_of_dist_eq`, matching the `congOk` disjunction. -/
lemma dist_vtx_eq2 {p q r s : Fin 29}
    (h : (p = q ∧ r = s) ∨
      (2 ≤ p.val ∧ 2 ≤ q.val ∧ 2 ≤ r.val ∧ 2 ≤ s.val ∧ Pmat p q = Pmat r s ∧ Qmat p q = Qmat r s)) :
    dist (vtx p) (vtx q) = dist (vtx r) (vtx s) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hp, hq, hr, hs, hP, hQ⟩
  · rw [dist_self, dist_self]
  · exact dist_vtx_eq hp hq hr hs hP hQ

/-- Pair set `{z, w}` as the image of a `Fin 2` family. -/
lemma pair_eq_image (z w : ℂ) : ({z, w} : Finset ℂ) = Finset.image ![z, w] Finset.univ := by
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from by decide, Finset.image_insert,
    Finset.image_singleton]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]

/-- `dist²(v₁, v₂₅) = 4` (nested-radical vertex `v₁`). -/
lemma distSq_v1_v25 :
    ((vtx 1).re - (vtx 25).re) ^ 2 + ((vtx 1).im - (vtx 25).im) ^ 2 = 4 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h33e : Real.sqrt 33 = Real.sqrt 3 * Real.sqrt 11 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hN : v1Radical ^ 2 = 415 / 8 + 79 * (Real.sqrt 3 * Real.sqrt 11) / 8 := by rw [hNsq, h33e]
  have e1re : (vtx 1).re = (103/24 : ℝ) + (-1/6) * Real.sqrt 33 + (1/96) * (v1Radical * Real.sqrt 3) + (-1/32) * (v1Radical * Real.sqrt 11) := rfl
  have e1im : (vtx 1).im = (3/32) * v1Radical + (-1/96) * (v1Radical * Real.sqrt 33) + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3 := rfl
  have e25 : vtx 25 = baseVert (65/12) (-1/4) (7/4) (7/12) := rfl
  rw [e1re, e1im, e25]
  simp only [baseVert, h33e]
  push_cast
  linear_combination ((Real.sqrt 11)^2*(Real.sqrt 3)^2/9216 + (Real.sqrt 11)^2/1024 - (Real.sqrt 11)*(Real.sqrt 3)/384 + (Real.sqrt 3)^2/9216 + 9/1024) * hN + (v1Radical*(Real.sqrt 11)/256 + 79*(Real.sqrt 11)^3*(Real.sqrt 3)/73728 - 323*(Real.sqrt 11)^2/24576 + 79*(Real.sqrt 11)*(Real.sqrt 3)/73728 + 135/8192) * h3 + (v1Radical*(Real.sqrt 3)/256 + 79*(Real.sqrt 11)*(Real.sqrt 3)/6144 + 415/2048) * h11

/-- `dist²(v₀, v₁₂) = 17/6 + √33/6` (degree-8 vertex `v₀`). -/
lemma distSq_v0_v12 :
    ((vtx 0).re - (vtx 12).re) ^ 2 + ((vtx 0).im - (vtx 12).im) ^ 2
    = 17/6 + (1/6) * Real.sqrt 33 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h33e : Real.sqrt 33 = Real.sqrt 3 * Real.sqrt 11 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h15e : Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h165e : Real.sqrt 165 = Real.sqrt 3 * Real.sqrt 5 * Real.sqrt 11 := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by norm_num)]; norm_num
  have e0re : (vtx 0).re = (25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165 := rfl
  have e0im : (vtx 0).im = (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3 := rfl
  have e12 : vtx 12 = baseVert (16/3) (-1/6) (7/3) (1/6) := rfl
  rw [e0re, e0im, e12]
  simp only [baseVert, h33e, h15e, h165e]
  push_cast
  linear_combination ((Real.sqrt 11)^2*(Real.sqrt 5)^2/2304 + (Real.sqrt 5)^2/36 - 7*(Real.sqrt 5)/48 + 49/256) * h3 + ((Real.sqrt 5)^2/768 + 49/2304) * h11 + ((Real.sqrt 11)*(Real.sqrt 3)/128 + 17/128) * h5

/-- The 2 genuine `v₀/v₁` multi-congruences, handled by explicit algebraic distance identities. -/
lemma hcong_special (i : Fin numCong) (h : i.val = 16609 ∨ i.val = 16840) :
    Congruent (Lfam i) (Rfam i) := by
  rcases h with h | h
  · have hL : Lfam i = {vtx 4, vtx 7} := by
      rw [Lfam, h, show bitsToFinset (congLArr[16609]!).toNat = ({4, 7} : Finset (Fin 29)) from by
        native_decide, Finset.image_insert, Finset.image_singleton]
    have hR : Rfam i = {vtx 1, vtx 25} := by
      rw [Rfam, h, show bitsToFinset (congRArr[16609]!).toNat = ({1, 25} : Finset (Fin 29)) from by
        native_decide, Finset.image_insert, Finset.image_singleton]
    rw [hL, hR, pair_eq_image (vtx 4) (vtx 7), pair_eq_image (vtx 1) (vtx 25)]
    refine congruent_of_dist_eq ![vtx 4, vtx 7] ![vtx 1, vtx 25] (fun a b => ?_)
    have key : dist (vtx 4) (vtx 7) = dist (vtx 1) (vtx 25) := by
      rw [dist_vtx_base 4 7 (by decide) (by decide), Complex.dist_eq_re_im, distSq_v1_v25,
        show Pmat 4 7 = 4 from by native_decide, show Qmat 4 7 = 0 from by native_decide]
      congr 1; push_cast; ring
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one]
    · rw [dist_self, dist_self]
    · exact key
    · rw [dist_comm (vtx 7) (vtx 4), dist_comm (vtx 25) (vtx 1)]; exact key
    · rw [dist_self, dist_self]
  · have hL : Lfam i = {vtx 7, vtx 14} := by
      rw [Lfam, h, show bitsToFinset (congLArr[16840]!).toNat = ({7, 14} : Finset (Fin 29)) from by
        native_decide, Finset.image_insert, Finset.image_singleton]
    have hR : Rfam i = {vtx 0, vtx 12} := by
      rw [Rfam, h, show bitsToFinset (congRArr[16840]!).toNat = ({0, 12} : Finset (Fin 29)) from by
        native_decide, Finset.image_insert, Finset.image_singleton]
    rw [hL, hR, pair_eq_image (vtx 7) (vtx 14), pair_eq_image (vtx 0) (vtx 12)]
    refine congruent_of_dist_eq ![vtx 7, vtx 14] ![vtx 0, vtx 12] (fun a b => ?_)
    have key : dist (vtx 7) (vtx 14) = dist (vtx 0) (vtx 12) := by
      rw [dist_vtx_base 7 14 (by decide) (by decide), Complex.dist_eq_re_im, distSq_v0_v12,
        show Pmat 7 14 = 17/6 from by native_decide, show Qmat 7 14 = 1/12 from by native_decide]
      congr 1; push_cast; ring
    fin_cases a <;> fin_cases b <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.mk_zero, Fin.mk_one]
    · rw [dist_self, dist_self]
    · exact key
    · rw [dist_comm (vtx 14) (vtx 7), dist_comm (vtx 12) (vtx 0)]; exact key
    · rw [dist_self, dist_self]

/-- **The 16859 congruences are genuine.** -/
lemma hcong_all (i : Fin numCong) : Congruent (Lfam i) (Rfam i) := by
  by_cases hsp : i.val = 16609 ∨ i.val = 16840
  · exact hcong_special i hsp
  · push Not at hsp
    obtain ⟨hs1, hs2⟩ := hsp
    have hi := (List.all_eq_true.mp congOk_true) i.val (List.mem_range.mpr i.isLt)
    have e1 : (i.val == 16609) = false := by rw [beq_eq_false_iff_ne]; exact hs1
    have e2 : (i.val == 16840) = false := by rw [beq_eq_false_iff_ne]; exact hs2
    rw [e1, e2, Bool.false_or, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true,
      decide_eq_true_eq, decide_eq_true_eq] at hi
    obtain ⟨⟨himL, himR⟩, hpair⟩ := hi
    have hLf : Lfam i = Finset.image (vtx ∘ amatF i.val) Finset.univ := by
      rw [Lfam, ← himL, Finset.image_image]
    have hRf : Rfam i = Finset.image (vtx ∘ bmatF i.val) Finset.univ := by
      rw [Rfam, ← himR, Finset.image_image]
    rw [hLf, hRf]
    refine congruent_of_dist_eq _ _ (fun j k => ?_)
    have hjk := (List.all_eq_true.mp ((List.all_eq_true.mp hpair) j.val
      (List.mem_range.mpr j.isLt))) k.val (List.mem_range.mpr k.isLt)
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hjk
    exact dist_vtx_eq2 (by
      rcases hjk with ⟨ha, hb⟩ | ⟨⟨⟨⟨⟨h2p, h2q⟩, h2r⟩, h2s⟩, hP⟩, hQ⟩
      · exact Or.inl ⟨ha, hb⟩
      · exact Or.inr ⟨h2p, h2q, h2r, h2s, hP, hQ⟩)

/-! ### The feasibility bridge (`hfeas`)

The integer dual inequality at an enumerated independent set `T : Finset (Fin 29)`, in the same
`Fin numCong`-indexed form as the abstract dual, cleared of the common denominator `certDen`. -/

/-- Integer dual slack numerator at `T`: `∑ᵢ yᵢ · ([Lᵢ ⊆ T] − [Rᵢ ⊆ T])`. -/
noncomputable def certIntSum (T : Finset (Fin 29)) : ℤ :=
  ∑ i : Fin numCong, yArr[i.val]! *
    ((if bitsToFinset (congLArr[i.val]!).toNat ⊆ T then (1 : ℤ) else 0)
      - (if bitsToFinset (congRArr[i.val]!).toNat ⊆ T then 1 else 0))

/-- Aggregate dual weight of a vertex set `T'`: `∑_{Lᵢ = T'} yᵢ − ∑_{Rᵢ = T'} yᵢ` (the `w[·]`
of the certificate). -/
noncomputable def wF (T' : Finset (Fin 29)) : ℤ :=
  ∑ i : Fin numCong, yArr[i.val]! *
    ((if bitsToFinset (congLArr[i.val]!).toNat = T' then (1 : ℤ) else 0)
      - (if bitsToFinset (congRArr[i.val]!).toNat = T' then 1 else 0))

/-- **Reindexing to a submask sum.** The abstract dual slack `certIntSum T` (a `16859`-term sum)
equals `∑_{T' ⊆ T} wF T'` — the compact submask form the certificate actually checks. This is the
mathematical step that makes the per-atom check tractable (submasks of `T`, not all congruences). -/
lemma certIntSum_eq_powerset (T : Finset (Fin 29)) :
    certIntSum T = ∑ T' ∈ T.powerset, wF T' := by
  simp only [certIntSum, wF]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp only [Finset.mem_powerset]

/-! ### Efficient per-atom certificate feasibility

The abstract dual slack `certIntSum T = ∑_{T'⊆T} wF T'` (`certIntSum_eq_powerset`) must be verified
nonnegative at every independent set of `G₂₉`. A brute-force `native_decide` (16859 congruences ×
498168 atoms) is too slow, and `native_decide` over `indepEnum H` is infeasible (`Finset.union`
dedup). So we mirror the enumeration on `ℕ` bitmasks (`indepEnumBM`, no dedup), cache the aggregate
weights in a `Std.HashMap` (`wMap`/`wLookup`), and reduce the per-atom slack to a submask sum
(`effSum`, via `psum`). Four bounded `native_decide`s (`wLookup_keys_ok`, `wKeys_complete`,
`cong_lt`, `feasBM`) validate the cache and check the feasibility; the
`indepEnumBM_corr` correspondence transfers the result to the abstract `cert_per_atom`.

Each `native_decide` call introduces one `*._native.native_decide.ax_*` trust axiom; all arithmetic is exact `Int`.
`feasBM` is the load-bearing atom-feasibility check (it supersedes the removed standalone
`Certificate.cert_feasible`). -/

/-- Encode a vertex set as a `ℕ` bitmask. -/
def encode (T : Finset (Fin 29)) : ℕ := ∑ k ∈ T, 2 ^ (k : ℕ)

lemma encode_eq_image (T : Finset (Fin 29)) : encode T = ∑ i ∈ T.image (Fin.val), 2 ^ i := by
  rw [encode, Finset.sum_image]; intro a _ b _ h; exact Fin.val_injective h

lemma mem_bitsToFinset {m : ℕ} {k : Fin 29} : k ∈ bitsToFinset m ↔ m.testBit k.val = true := by
  simp [bitsToFinset]

lemma testBit_encode (T : Finset (Fin 29)) (j : ℕ) :
    (encode T).testBit j = true ↔ ∃ k ∈ T, k.val = j := by
  rw [encode_eq_image, ← Nat.mem_bitIndices, ← List.mem_toFinset,
      Finset.toFinset_bitIndices_sum_two_pow, Finset.mem_image]

lemma bitsToFinset_encode (T : Finset (Fin 29)) : bitsToFinset (encode T) = T := by
  ext k
  rw [mem_bitsToFinset, testBit_encode]
  constructor
  · rintro ⟨k', hk', hval⟩; exact (Fin.val_injective hval) ▸ hk'
  · intro h; exact ⟨k, h, rfl⟩

/-- Setting bit `v` in a mask corresponds to inserting `v` into the vertex set. -/
lemma bitsToFinset_or_two_pow (v : Fin 29) (m : ℕ) :
    bitsToFinset (m ||| 2 ^ v.val) = insert v (bitsToFinset m) := by
  ext k
  rw [mem_bitsToFinset, Nat.testBit_or, Finset.mem_insert, mem_bitsToFinset,
      Nat.testBit_two_pow]
  rw [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl (Fin.val_injective h.symm)
  · rintro (rfl | h)
    · exact Or.inr rfl
    · exact Or.inl h

/-- The neighbour mask of `v` in `H` (computable, for `native_decide`). -/
def nbrMask (v : Fin 29) : ℕ :=
  (List.finRange 29).foldl (fun acc w => if adjB v.val w.val then acc ||| 2 ^ w.val else acc) 0

/-- Bit `w` of `nbrMask v` records `H`-adjacency (checked over the finite domain). -/
lemma nbrMask_testBit (v w : Fin 29) : (nbrMask v).testBit w.val = adjB v.val w.val := by
  revert v w; decide

/-- `nbrMask v` fits in `29` bits. -/
lemma nbrMask_lt (v : Fin 29) : nbrMask v < 2 ^ 29 := by revert v; decide

lemma nbrMask_testBit_high (v : Fin 29) {i : ℕ} (hi : 29 ≤ i) :
    (nbrMask v).testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (nbrMask_lt v) (Nat.pow_le_pow_right (by norm_num) hi))

/-- The bitmask filter condition matches graph non-adjacency to the current vertex set. -/
lemma and_nbrMask_eq_zero_iff (v : Fin 29) (m : ℕ) :
    m &&& nbrMask v = 0 ↔ ∀ w ∈ bitsToFinset m, ¬ H.Adj v w := by
  constructor
  · intro h w hw hadj
    have hmw : m.testBit w.val = true := mem_bitsToFinset.mp hw
    have hnw : (nbrMask v).testBit w.val = true := by
      rw [nbrMask_testBit]; exact hadj
    have : (m &&& nbrMask v).testBit w.val = true := by
      rw [Nat.testBit_and, hmw, hnw]; rfl
    rw [h, Nat.zero_testBit] at this; exact Bool.noConfusion this
  · intro h
    apply Nat.zero_of_testBit_eq_false
    intro i
    rw [Nat.testBit_and]
    by_cases hi : i < 29
    · by_cases hm : m.testBit i = true
      · have hw : (⟨i, hi⟩ : Fin 29) ∈ bitsToFinset m := mem_bitsToFinset.mpr hm
        have hadj : ¬ H.Adj v ⟨i, hi⟩ := h _ hw
        have hf : adjB v.val i = false := by
          have hne : adjB v.val i ≠ true := hadj
          simpa using hne
        rw [show (nbrMask v).testBit i = adjB v.val i from nbrMask_testBit v ⟨i, hi⟩,
            hf, Bool.and_false]
      · rw [Bool.not_eq_true] at hm; rw [hm, Bool.false_and]
    · rw [nbrMask_testBit_high v (not_lt.mp hi), Bool.and_false]

/-- List-based bitmask mirror of `indepEnum H` — no `Finset.union` dedup, so `native_decide`-fast. -/
def indepEnumBM : List (Fin 29) → List ℕ
  | [] => [0]
  | v :: vs =>
      let p := indepEnumBM vs
      p ++ (p.filter (fun m => m &&& nbrMask v == 0)).map (fun m => m ||| 2 ^ v.val)

/-- **Enumeration correspondence.** Every independent set enumerated by `indepEnum H l` is
`bitsToFinset` of some bitmask in `indepEnumBM l`, and conversely. -/
lemma indepEnumBM_corr (l : List (Fin 29)) (S : Finset (Fin 29)) :
    S ∈ indepEnum H l ↔ ∃ m ∈ indepEnumBM l, bitsToFinset m = S := by
  induction l generalizing S with
  | nil =>
    simp only [indepEnum, indepEnumBM, Finset.mem_singleton, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨0, rfl, by simp [bitsToFinset]⟩
    · rintro ⟨m, rfl, hm⟩; rw [← hm]; simp [bitsToFinset]
  | cons v vs ih =>
    rw [indepEnum]
    simp only [indepEnumBM, List.mem_append, List.mem_map, List.mem_filter,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter, beq_iff_eq]
    constructor
    · rintro (hS | ⟨T, ⟨hT, hTadj⟩, rfl⟩)
      · obtain ⟨m, hm, rfl⟩ := (ih S).mp hS
        exact ⟨m, Or.inl hm, rfl⟩
      · obtain ⟨m, hm, rfl⟩ := (ih T).mp hT
        refine ⟨m ||| 2 ^ v.val, Or.inr ⟨m, ⟨hm, ?_⟩, rfl⟩, ?_⟩
        · exact (and_nbrMask_eq_zero_iff v m).mpr hTadj
        · rw [bitsToFinset_or_two_pow]
    · rintro ⟨m, (hm | ⟨m', ⟨hm', hcond⟩, rfl⟩), rfl⟩
      · exact Or.inl ((ih _).mpr ⟨m, hm, rfl⟩)
      · refine Or.inr ⟨bitsToFinset m', ⟨(ih _).mpr ⟨m', hm', rfl⟩, ?_⟩, ?_⟩
        · exact (and_nbrMask_eq_zero_iff v m').mp hcond
        · rw [bitsToFinset_or_two_pow]

/-- Shared index array (built once), so the weight recompute does not rebuild a list per call. -/
def idxCong : Array ℕ := Array.range numCong

/-- Aggregated dual weight of a bitmask (fast recompute; the bitmask analogue of `wF`). -/
def wFbm (m : ℕ) : ℤ :=
  idxCong.foldl
    (fun (acc : ℤ) (i : ℕ) =>
      acc + ((if (congLArr[i]!).toNat = m then (yArr[i]! : ℤ) else 0)
          - (if (congRArr[i]!).toNat = m then (yArr[i]! : ℤ) else 0))) 0

/-- Weight cache as a hash map (`O(1)` lookup), built once from the certificate arrays. -/
def wMap : Std.HashMap ℕ ℤ := Id.run do
  let mut hm : Std.HashMap ℕ ℤ := {}
  for i in [0:congLArr.size] do
    let l := (congLArr[i]!).toNat
    let r := (congRArr[i]!).toNat
    hm := hm.insert l (hm.getD l 0 + yArr[i]!)
    hm := hm.insert r (hm.getD r 0 - yArr[i]!)
  return hm

/-- Weight lookup: hash-map read, returning `0` for masks that are not congruence keys. -/
def wLookup (m : ℕ) : ℤ := wMap.getD m 0

/-- Per-key validation: on every cached key the lookup returns the true aggregate. -/
theorem wLookup_keys_ok :
    wMap.keys.all (fun k => wLookup k == wFbm k) = true := by
  native_decide

/-- Completeness: every congruence mask is a cache key. -/
theorem wKeys_complete :
    (List.range numCong).all (fun i =>
      wMap.contains (congLArr[i]!).toNat && wMap.contains (congRArr[i]!).toNat) = true := by
  native_decide

/-- Congruence masks fit in 29 bits. -/
theorem cong_lt :
    (List.range numCong).all (fun i =>
      (congLArr[i]!).toNat < 2 ^ 29 && (congRArr[i]!).toNat < 2 ^ 29) = true := by
  native_decide

lemma foldl_range_eq_sum (n : ℕ) (g : ℕ → ℤ) :
    (List.range n).foldl (fun acc i => acc + g i) 0 = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp

lemma wFbm_eq_sum (m : ℕ) :
    wFbm m = ∑ i ∈ Finset.range numCong,
      ((if (congLArr[i]!).toNat = m then (yArr[i]! : ℤ) else 0)
        - (if (congRArr[i]!).toNat = m then (yArr[i]! : ℤ) else 0)) := by
  rw [wFbm, idxCong, ← Array.foldl_toList, Array.toList_range]
  exact foldl_range_eq_sum numCong _

/-- `bitsToFinset` is injective on masks below `2^29`. -/
lemma bitsToFinset_inj {a b : ℕ} (ha : a < 2 ^ 29) (hb : b < 2 ^ 29)
    (h : bitsToFinset a = bitsToFinset b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 29
  · have hc := congrArg (fun s => (⟨j, hj⟩ : Fin 29) ∈ s) h
    simp only [mem_bitsToFinset] at hc
    simpa using hc
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)))]

lemma congL_lt {j : ℕ} (hj : j < numCong) : (congLArr[j]!).toNat < 2 ^ 29 := by
  have h := List.all_eq_true.mp cong_lt j (List.mem_range.mpr hj)
  simpa using Bool.and_elim_left h

lemma congR_lt {j : ℕ} (hj : j < numCong) : (congRArr[j]!).toNat < 2 ^ 29 := by
  have h := List.all_eq_true.mp cong_lt j (List.mem_range.mpr hj)
  simpa using Bool.and_elim_right h

lemma bitsToFinset_inj_iff {a b : ℕ} (ha : a < 2 ^ 29) (hb : b < 2 ^ 29) :
    bitsToFinset a = bitsToFinset b ↔ a = b :=
  ⟨bitsToFinset_inj ha hb, fun h => h ▸ rfl⟩

/-- The bitmask weight equals the `Finset` weight `wF` at the corresponding vertex set. -/
lemma wFbm_eq_wF {m : ℕ} (hm : m < 2 ^ 29) : wFbm m = wF (bitsToFinset m) := by
  rw [wFbm_eq_sum, wF, Fin.sum_univ_eq_sum_range
      (fun j => yArr[j]! * ((if bitsToFinset (congLArr[j]!).toNat = bitsToFinset m then (1 : ℤ) else 0)
        - (if bitsToFinset (congRArr[j]!).toNat = bitsToFinset m then 1 else 0))) numCong]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  simp only [bitsToFinset_inj_iff (congL_lt hj) hm, bitsToFinset_inj_iff (congR_lt hj) hm]
  split_ifs <;> ring

/-- **Cache correctness.** The hash-map lookup equals the true aggregate weight. -/
lemma wLookup_eq (m : ℕ) : wLookup m = wFbm m := by
  by_cases hmem : wMap.contains m = true
  · have hkeys : m ∈ wMap.keys := Std.HashMap.mem_keys.mpr hmem
    have hall := List.all_eq_true.mp wLookup_keys_ok m hkeys
    exact beq_iff_eq.mp hall
  · rw [Bool.not_eq_true] at hmem
    have hlk : wLookup m = 0 := Std.HashMap.getD_eq_fallback_of_contains_eq_false hmem
    have hwf : wFbm m = 0 := by
      rw [wFbm_eq_sum]
      apply Finset.sum_eq_zero
      intro j hj
      rw [Finset.mem_range] at hj
      have hcompl := List.all_eq_true.mp wKeys_complete j (List.mem_range.mpr hj)
      have hL : wMap.contains (congLArr[j]!).toNat = true := Bool.and_elim_left hcompl
      have hR : wMap.contains (congRArr[j]!).toNat = true := Bool.and_elim_right hcompl
      rw [if_neg (fun (h : (congLArr[j]!).toNat = m) => by rw [h] at hL; rw [hL] at hmem; exact absurd hmem (by decide)),
          if_neg (fun (h : (congRArr[j]!).toNat = m) => by rw [h] at hR; rw [hR] at hmem; exact absurd hmem (by decide))]
      ring
    rw [hlk, hwf]

lemma encode_lt (T : Finset (Fin 29)) : encode T < 2 ^ 29 := by
  have h1 : encode T ≤ encode Finset.univ := Finset.sum_le_sum_of_subset (Finset.subset_univ T)
  have h2 : encode (Finset.univ : Finset (Fin 29)) = 2 ^ 29 - 1 := by decide
  rw [h2] at h1
  have h3 : (2 : ℕ) ^ 29 = 536870912 := by norm_num
  omega

lemma wLookup_encode_eq_wF (T : Finset (Fin 29)) : wLookup (encode T) = wF T := by
  rw [wLookup_eq, wFbm_eq_wF (encode_lt T), bitsToFinset_encode]

/-- Inserting `a` into a vertex set sets bit `a` in its encoding. -/
lemma encode_insert (a : Fin 29) (T' : Finset (Fin 29)) :
    encode (insert a T') = 2 ^ a.val ||| encode T' := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, decide_eq_true_eq, testBit_encode]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases Finset.mem_insert.mp hk with rfl | hk'
    · exact Or.inl rfl
    · exact Or.inr ⟨k, hk', rfl⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨a, Finset.mem_insert_self _ _, rfl⟩
    · exact ⟨k, Finset.mem_insert_of_mem hk, rfl⟩

/-- Precomputed powers of two (so the hot recursion does an array read, not `Nat.pow`). -/
def pow2Arr : Array ℕ := (Array.range 29).map (fun k => 2 ^ k)

def pow2 (k : ℕ) : ℕ := pow2Arr[k]!

lemma pow2_eq {k : ℕ} (hk : k < 29) : pow2 k = 2 ^ k := by
  have h : pow2Arr[k]? = some (2 ^ k) := by
    simp only [pow2Arr, Array.getElem?_map, Array.getElem?_range]
    simp [hk]
  simp only [pow2, getElem!_def, h]

/-- Submask sum of cached weights over subsets of a bit-list, offset by `acc` (no `Finset`, so
`native_decide`-fast). -/
def psum : List (Fin 29) → ℕ → ℤ
  | [], acc => wLookup acc
  | a :: rest, acc => psum rest acc + psum rest (acc ||| pow2 a.val)

lemma psum_eq : ∀ (L : List (Fin 29)), L.Nodup → ∀ (acc : ℕ),
    psum L acc = ∑ T' ∈ L.toFinset.powerset, wLookup (acc ||| encode T')
  | [], _, acc => by simp [psum, encode]
  | a :: rest, hL, acc => by
    rw [List.nodup_cons] at hL
    obtain ⟨ha, hrest⟩ := hL
    have hafin : a ∉ rest.toFinset := by simpa using ha
    rw [psum, psum_eq rest hrest acc, psum_eq rest hrest (acc ||| pow2 a.val),
        List.toFinset_cons, Finset.powerset_insert,
        Finset.sum_union (by
          rw [Finset.disjoint_left]
          intro x hx hx2
          rw [Finset.mem_image] at hx2
          obtain ⟨y, hy, rfl⟩ := hx2
          rw [Finset.mem_powerset] at hx
          exact hafin (hx (Finset.mem_insert_self a y))),
        Finset.sum_image (by
          intro x hx y hy hxy
          simp only [Finset.mem_coe, Finset.mem_powerset] at hx hy
          have hax : a ∉ x := fun h => hafin (hx h)
          have hay : a ∉ y := fun h => hafin (hy h)
          rw [← Finset.erase_insert hax, ← Finset.erase_insert hay, hxy])]
    congr 1
    apply Finset.sum_congr rfl
    intro T' _
    rw [pow2_eq a.isLt, encode_insert, Nat.lor_assoc]

/-- Computable list of the set bits of `m` (as `Fin 29`). -/
def bitList (m : ℕ) : List (Fin 29) := (List.finRange 29).filter (fun k => m.testBit k.val)

lemma bitList_nodup (m : ℕ) : (bitList m).Nodup :=
  (List.nodup_finRange 29).filter _

lemma bitList_toFinset (m : ℕ) : (bitList m).toFinset = bitsToFinset m := by
  ext k
  simp only [bitList, List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and,
    mem_bitsToFinset]

/-- Fast per-atom dual slack: submask sum of cached weights. -/
def effSum (m : ℕ) : ℤ := psum (bitList m) 0

lemma effSum_eq_certIntSum (m : ℕ) : effSum m = certIntSum (bitsToFinset m) := by
  rw [effSum, psum_eq _ (bitList_nodup _) 0, bitList_toFinset, certIntSum_eq_powerset]
  apply Finset.sum_congr rfl
  intro T' _
  rw [Nat.zero_or, wLookup_encode_eq_wF]

/-- **Per-atom feasibility, over the fast bitmask enumeration.** -/
theorem feasBM :
    (indepEnumBM (List.finRange 29)).all
      (fun m => decide ((Certificate.certNum : ℤ) * (if m.testBit 0 then 1 else 0)
        ≤ effSum m + Certificate.certDen)) = true := by
  native_decide

lemma cert_per_atom (T : Finset (Fin 29)) (hT : T ∈ indepEnum H (List.finRange 29)) :
    (Certificate.certNum : ℤ) * (if (0 : Fin 29) ∈ T then 1 else 0)
      ≤ certIntSum T + Certificate.certDen := by
  obtain ⟨m, hm, rfl⟩ := (indepEnumBM_corr (List.finRange 29) T).mp hT
  have hb := List.all_eq_true.mp feasBM m hm
  rw [decide_eq_true_eq, effSum_eq_certIntSum] at hb
  have h0 : (if (0 : Fin 29) ∈ bitsToFinset m then (1 : ℤ) else 0)
      = (if m.testBit 0 then 1 else 0) := by
    simp only [mem_bitsToFinset, Fin.val_zero]
  rw [h0]; exact hb

private lemma certDen_posR : (0 : ℝ) < (Certificate.certDen : ℝ) := by
  rw [Certificate.certDen]; norm_num

/-- **Dual feasibility at every independent set of `G₂₉`** — the `hfeas` hypothesis, obtained by
transporting the per-atom certificate check through `indepSets_eq_image_indepEnum`. -/
lemma hfeas : ∀ S ∈ indepSets G29,
    ((Certificate.certNum : ℝ) / Certificate.certDen) * (if vtx 0 ∈ S then (1 : ℝ) else 0)
      ≤ (∑ i : Fin numCong, yfam i *
          ((if Lfam i ⊆ S then (1 : ℝ) else 0) - (if Rfam i ⊆ S then 1 else 0))) + 1 := by
  intro S hS
  rw [indepSets_eq_image_indepEnum G29 vtx H vtx_injective G29_eq_map_toFinset H_adj_iff,
      Finset.mem_image] at hS
  obtain ⟨T, hT, rfl⟩ := hS
  have hmem : (vtx 0 ∈ Finset.image vtx T) ↔ ((0 : Fin 29) ∈ T) := by
    rw [Finset.mem_image]
    exact ⟨fun ⟨a, ha, hva⟩ => vtx_injective hva ▸ ha, fun h => ⟨0, h, rfl⟩⟩
  have hLsub : ∀ i : Fin numCong,
      (Lfam i ⊆ Finset.image vtx T) ↔ (bitsToFinset (congLArr[i.val]!).toNat ⊆ T) := fun i => by
    rw [Lfam, Finset.image_subset_image_iff vtx_injective]
  have hRsub : ∀ i : Fin numCong,
      (Rfam i ⊆ Finset.image vtx T) ↔ (bitsToFinset (congRArr[i.val]!).toNat ⊆ T) := fun i => by
    rw [Rfam, Finset.image_subset_image_iff vtx_injective]
  simp only [hmem, hLsub, hRsub]
  have hsum : (∑ i : Fin numCong, yfam i *
        ((if bitsToFinset (congLArr[i.val]!).toNat ⊆ T then (1 : ℝ) else 0)
          - (if bitsToFinset (congRArr[i.val]!).toNat ⊆ T then 1 else 0)))
      = (certIntSum T : ℝ) / (Certificate.certDen : ℝ) := by
    rw [certIntSum]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [yfam]
    split_ifs <;> ring
  rw [hsum]
  have key := cert_per_atom T hT
  have e_eq : (if (0 : Fin 29) ∈ T then (1 : ℝ) else 0)
      = ((if (0 : Fin 29) ∈ T then (1 : ℤ) else 0 : ℤ) : ℝ) := by split_ifs <;> simp
  have keyR : (Certificate.certNum : ℝ) * ((if (0 : Fin 29) ∈ T then (1 : ℤ) else 0 : ℤ) : ℝ)
      ≤ (certIntSum T : ℝ) + (Certificate.certDen : ℝ) := by exact_mod_cast key
  rw [e_eq, div_mul_eq_mul_div, div_add_one certDen_posR.ne', div_le_div_iff_of_pos_right certDen_posR]
  linarith [keyR]

/-- **[DV26] Lemma 1.** The geometric fractional chromatic number of `G₂₉` exceeds `4`.
(The paper proves the sharper `> 4.0007`; the weaker `> 4` is all that is needed to drive the
blow-up argument, and is what we consume in `Main`.) -/
theorem chi_gf_G29_gt : (4 : ℝ) < χ_gf G29 := by
  have hv0 : vtx 0 ∈ G29 := by
    rw [← image_vtx_eq_G29]; exact Finset.mem_image_of_mem vtx (Finset.mem_univ 0)
  have hc : (0 : ℝ) ≤ (Certificate.certNum : ℝ) / (Certificate.certDen : ℝ) :=
    div_nonneg (by rw [Certificate.certNum]; norm_num) (le_of_lt certDen_posR)
  have hle : ((Certificate.certNum : ℝ) / Certificate.certDen) ≤ χ_gf G29 :=
    geomFractionalChromaticNumber_ge_of_dual hv0 Lfam_subset Rfam_subset hcong_all hc
      exists_geomColoring hfeas
  have h4 : (4 : ℝ) < (Certificate.certNum : ℝ) / Certificate.certDen := by
    rw [lt_div_iff₀ certDen_posR]; exact_mod_cast Certificate.cert_value_gt_four
  linarith

end UnitDistanceGraphs
