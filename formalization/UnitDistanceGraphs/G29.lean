/-
The graph `G₂₉` and its geometric toolkit ([DV26] Lemma 1's stage).

`G₂₉` is the 29-vertex unit-distance graph obtained by adding two vertices `v₀`, `v₁` to the
27-vertex graph `G₂₇` of Matolcsi–Ruzsa–Varga–Zsámboki (2023). The certified bound
`4 < χ_gf G₂₉` is established downstream (`CertificateVerification.lean`) via an explicit
rational dual solution to the geometric fractional coloring LP; see the supplementary data and
verification script at https://users.renyi.hu/~akos/ep1070/.

Vertices are given by their exact algebraic coordinates (ported from `verts_sym.npy`): the 27 base
vertices `v2..v28` lie in `ℚ(√3, √11, √33)`; the two added vertices `v0` (with `√5`) and `v1`
(with nested radicals) complete `G₂₉`.
-/

import UnitDistanceGraphs.Definitions

namespace UnitDistanceGraphs

open Classical

/-! ### The graph `G₂₉` (exact algebraic coordinates) -/

/-- The 29-vertex unit-distance graph `G₂₉` of [DV26], as an explicit finite set of points in `ℂ`
(exact algebraic coordinates from the supplementary data `verts_sym.npy`). -/
noncomputable def G29 : UnitDistanceGraph :=
  {
  (⟨((25 / 6 : ℝ) + ((-3 / 16 : ℝ) * Real.sqrt (5)) + ((-1 / 6 : ℝ) * Real.sqrt (33)) + ((-1 / 48 : ℝ) * Real.sqrt (165))),
    (((1 / 6 : ℝ) * Real.sqrt (15)) + ((1 / 48 : ℝ) * Real.sqrt (11)) + ((91 / 48 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((103 / 24 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33)) + ((-1 / 128 : ℝ) * Real.sqrt ((9130 + (1738 * Real.sqrt (33))))) + ((1 / 384 : ℝ) * Real.sqrt ((2490 + (474 * Real.sqrt (33)))))),
    (((-1 / 384 : ℝ) * Real.sqrt ((27390 + (5214 * Real.sqrt (33))))) + ((3 / 128 : ℝ) * Real.sqrt ((830 + (158 * Real.sqrt (33))))) + ((7 / 48 : ℝ) * Real.sqrt (11)) + ((79 / 48 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨(14 / 3 : ℝ),
    ((2 * Real.sqrt (3)) + ((1 / 3 : ℝ) * Real.sqrt (11)))⟩ : ℂ),
  (⟨(9 / 2 : ℝ),
    (((1 / 2 : ℝ) * Real.sqrt (11)) + (2 * Real.sqrt (3)))⟩ : ℂ),
  (⟨((47 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),
    (((1 / 12 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((19 / 4 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),
    (((1 / 4 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((55 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),
    (((5 / 12 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((67 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),
    (((5 / 12 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((61 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),
    (((5 / 12 : ℝ) * Real.sqrt (11)) + ((29 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((59 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),
    (((7 / 12 : ℝ) * Real.sqrt (11)) + ((17 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((65 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),
    (((7 / 12 : ℝ) * Real.sqrt (11)) + ((23 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((59 / 12 : ℝ) + ((-1 / 12 : ℝ) * Real.sqrt (33))),
    (((7 / 12 : ℝ) * Real.sqrt (11)) + ((29 / 12 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((16 / 3 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((1 / 6 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((17 / 3 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((1 / 3 : ℝ) * Real.sqrt (11)) + ((11 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((25 / 6 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((1 / 3 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((31 / 6 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((1 / 3 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((11 / 2 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((1 / 2 : ℝ) * Real.sqrt (11)) + ((11 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨(5 + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((1 / 2 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((13 / 3 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((2 / 3 : ℝ) * Real.sqrt (11)) + ((11 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((29 / 6 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((2 / 3 : ℝ) * Real.sqrt (11)) + ((7 / 3 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((31 / 6 : ℝ) + ((-1 / 6 : ℝ) * Real.sqrt (33))),
    (((5 / 6 : ℝ) * Real.sqrt (11)) + ((11 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((61 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),
    (((5 / 4 : ℝ) * Real.sqrt (3)) + ((5 / 12 : ℝ) * Real.sqrt (11)))⟩ : ℂ),
  (⟨((55 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),
    (((5 / 12 : ℝ) * Real.sqrt (11)) + ((7 / 4 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((67 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),
    (((5 / 12 : ℝ) * Real.sqrt (11)) + ((7 / 4 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((53 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),
    (((7 / 4 : ℝ) * Real.sqrt (3)) + ((7 / 12 : ℝ) * Real.sqrt (11)))⟩ : ℂ),
  (⟨((65 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),
    (((7 / 4 : ℝ) * Real.sqrt (3)) + ((7 / 12 : ℝ) * Real.sqrt (11)))⟩ : ℂ),
  (⟨((59 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),
    (((7 / 12 : ℝ) * Real.sqrt (11)) + ((9 / 4 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((71 / 12 : ℝ) + ((-1 / 4 : ℝ) * Real.sqrt (33))),
    (((7 / 12 : ℝ) * Real.sqrt (11)) + ((9 / 4 : ℝ) * Real.sqrt (3)))⟩ : ℂ),
  (⟨((31 / 6 : ℝ) + ((-1 / 3 : ℝ) * Real.sqrt (33))),
    (((1 / 3 : ℝ) * Real.sqrt (11)) + ((13 / 6 : ℝ) * Real.sqrt (3)))⟩ : ℂ)
  }

/-! ### Geometric bridge: adjacency criterion (base sublattice)

The independent sets of `G₂₉` are determined by which vertex pairs are at distance `1`. The 27 base
vertices have coordinates `re = rr + r33·√33`, `im = i3·√3 + i11·√11` with `rr, r33, i3, i11 ∈ ℚ`.
Since `√3·√11 = √33`, every base squared distance lies in `ℚ(√33)`: `dist² = P + Q·√33` with `P, Q`
rational, so by irrationality of `√33`, `dist = 1 ↔ P = 1 ∧ Q = 0` — a *purely rational* condition.
Hence **every** base-sublattice adjacency (edge or non-edge) is decided by `norm_num` via the single
criterion `dist_baseVert_eq_one_iff` below. Only the two added vertices `v₀, v₁` (nested radicals)
fall outside this base kind. -/

/-- A base-sublattice vertex `(rr + r33·√33) + (i3·√3 + i11·√11)·I`, coordinates in `ℚ(√3,√11,√33)`. -/
noncomputable def baseVert (rr r33 i3 i11 : ℚ) : ℂ :=
  ⟨(rr : ℝ) + (r33 : ℝ) * Real.sqrt 33, (i3 : ℝ) * Real.sqrt 3 + (i11 : ℝ) * Real.sqrt 11⟩

/-- Distance-one criterion via real/imaginary parts. -/
lemma dist_eq_one_of_sq {z w : ℂ} (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 1) :
    dist z w = 1 := by
  rw [Complex.dist_eq_re_im, h, Real.sqrt_one]

/-- `p + 2q√33 = 1` (for rational `p, q`) iff `p = 1 ∧ q = 0` — by irrationality of `√33`. -/
private lemma rat_add_mul_sqrt33_eq_one (p q : ℚ) :
    (p : ℝ) + 2 * (q : ℝ) * Real.sqrt 33 = 1 ↔ p = 1 ∧ q = 0 := by
  have irr33 : Irrational (Real.sqrt 33) := by norm_num
  constructor
  · intro h
    by_cases hq : q = 0
    · subst hq; simp only [Rat.cast_zero, mul_zero, zero_mul, add_zero] at h
      exact ⟨by exact_mod_cast h, rfl⟩
    · exfalso
      have h2q : (2 * q) ≠ 0 := by simpa using hq
      have hirr : Irrational (((2 * q : ℚ) : ℝ) * Real.sqrt 33) := irr33.ratCast_mul h2q
      have key : ((2 * q : ℚ) : ℝ) * Real.sqrt 33 = 1 - (p : ℝ) := by push_cast; linarith [h]
      have hcast : ((1 - p : ℚ) : ℝ) = 1 - (p : ℝ) := by push_cast; ring
      rw [key, ← hcast] at hirr
      exact Rat.not_irrational _ hirr
  · rintro ⟨rfl, rfl⟩; norm_num

/-- **Base-sublattice adjacency criterion.** Two base vertices are at unit distance iff a pair of
*rational* equations holds — so every base adjacency is decided by `norm_num`. -/
lemma dist_baseVert_eq_one_iff (a1 a2 a3 a4 b1 b2 b3 b4 : ℚ) :
    dist (baseVert a1 a2 a3 a4) (baseVert b1 b2 b3 b4) = 1 ↔
      ((a1 - b1) ^ 2 + 33 * (a2 - b2) ^ 2 + 3 * (a3 - b3) ^ 2 + 11 * (a4 - b4) ^ 2 = 1 ∧
       (a1 - b1) * (a2 - b2) + (a3 - b3) * (a4 - b4) = 0) := by
  rw [Complex.dist_eq_re_im, Real.sqrt_eq_one]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h33 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  have h311 : Real.sqrt 3 * Real.sqrt 11 = Real.sqrt 33 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hid : ((baseVert a1 a2 a3 a4).re - (baseVert b1 b2 b3 b4).re) ^ 2
      + ((baseVert a1 a2 a3 a4).im - (baseVert b1 b2 b3 b4).im) ^ 2
      = (((a1 - b1) ^ 2 + 33 * (a2 - b2) ^ 2 + 3 * (a3 - b3) ^ 2 + 11 * (a4 - b4) ^ 2 : ℚ) : ℝ)
        + 2 * (((a1 - b1) * (a2 - b2) + (a3 - b3) * (a4 - b4) : ℚ) : ℝ) * Real.sqrt 33 := by
    simp only [baseVert]
    push_cast
    linear_combination ((a2 : ℝ) - b2) ^ 2 * h33 + ((a3 : ℝ) - b3) ^ 2 * h3
      + ((a4 : ℝ) - b4) ^ 2 * h11 + 2 * ((a3 : ℝ) - b3) * ((a4 : ℝ) - b4) * h311
  rw [hid, rat_add_mul_sqrt33_eq_one]

/-- Base edge `v₂ ~ v₈` — now decided by pure rational arithmetic. -/
example : dist (baseVert (14/3) 0 2 (1/3)) (baseVert (61/12) (-1/12) (29/12) (5/12)) = 1 := by
  rw [dist_baseVert_eq_one_iff]; norm_num

/-- Base non-edge `v₂ ≁ v₃` (squared distance `1/3 ≠ 1`). -/
example : dist (baseVert (14/3) 0 2 (1/3)) (baseVert (9/2) 0 2 (1/2)) ≠ 1 := by
  intro h; rw [dist_baseVert_eq_one_iff] at h; norm_num at h

/-! ### Geometric bridge: the two added vertices `v₀, v₁`

The only edges of `G₂₉` touching the two added vertices are `v₀ ~ v₄` and `v₁ ~ v₄` (`v₄` is a base
vertex). `v₀` lives in the flat degree-8 field `ℚ(√3,√5,√11)`; `v₁` uses the genuinely *nested*
radical `√(415/8 + 79√33/8)`. Both distances are still algebraic identities: rewriting composite
roots to generators (and, for `v₁`, treating the nested radical `N` as a variable with
`N² = 415/8 + 79√3√11/8`), the squared distance minus `1` lies in the ideal of the defining
relations, so `linear_combination` closes it. This shows the *entire* adjacency of `G₂₉` is provable
in Lean — the nested-radical vertices are not an obstruction. -/

/-- The nested radical appearing in `v₁`'s coordinates: `N = √(415/8 + 79√33/8)`. -/
noncomputable def v1Radical : ℝ := Real.sqrt (415 / 8 + 79 * Real.sqrt 33 / 8)

/-- Edge `v₀ ~ v₄` of `G₂₉` (with `v₀ ∈ ℚ(√3,√5,√11)`), at unit distance. -/
lemma dist_v0_v4 : dist
    (⟨(25/6 : ℝ) + (-3/16) * Real.sqrt 5 + (-1/6) * Real.sqrt 33 + (-1/48) * Real.sqrt 165,
      (1/6) * Real.sqrt 15 + (1/48) * Real.sqrt 11 + (91/48) * Real.sqrt 3⟩ : ℂ)
    (⟨(47/12 : ℝ) + (-1/12) * Real.sqrt 33, (1/12) * Real.sqrt 11 + (23/12) * Real.sqrt 3⟩ : ℂ)
    = 1 := by
  apply dist_eq_one_of_sq
  have h15 : Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h33 : Real.sqrt 33 = Real.sqrt 3 * Real.sqrt 11 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h165 : Real.sqrt 165 = Real.sqrt 3 * Real.sqrt 5 * Real.sqrt 11 := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by norm_num)]; norm_num
  rw [h15, h33, h165]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  linear_combination
    (Real.sqrt 11^2 * Real.sqrt 5^2/2304 + Real.sqrt 11^2 * Real.sqrt 5/288 + Real.sqrt 11^2/144
      + Real.sqrt 5^2/36 - Real.sqrt 5/144 + 1/2304) * h3
    + (Real.sqrt 11^2/768 + Real.sqrt 11 * Real.sqrt 3/128 + 91/768) * h5
    + (Real.sqrt 5/96 + 1/32) * h11

/-- Edge `v₁ ~ v₄` of `G₂₉` (with `v₁` using the nested radical `v1Radical`), at unit distance. -/
lemma dist_v1_v4 : dist
    (⟨(103/24 : ℝ) + (-1/6) * Real.sqrt 33
        + (-1/8) * v1Radical * ((-1/12) * Real.sqrt 3 + (1/4) * Real.sqrt 11),
      (1/8) * v1Radical * ((3/4) + (-1/12) * Real.sqrt 33)
        + (7/48) * Real.sqrt 11 + (79/48) * Real.sqrt 3⟩ : ℂ)
    (⟨(47/12 : ℝ) + (-1/12) * Real.sqrt 33, (1/12) * Real.sqrt 11 + (23/12) * Real.sqrt 3⟩ : ℂ)
    = 1 := by
  apply dist_eq_one_of_sq
  have h33 : Real.sqrt 33 = Real.sqrt 3 * Real.sqrt 11 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have hN : v1Radical ^ 2 = 415/8 + 79 * Real.sqrt 3 * Real.sqrt 11 / 8 := by
    rw [v1Radical, Real.sq_sqrt (by positivity), h33]; ring
  rw [h33]
  linear_combination
    (v1Radical^2 * Real.sqrt 11^2/9216 + v1Radical^2/9216 + v1Radical * Real.sqrt 11/256
      - 173 * Real.sqrt 11^2/9216 + 169/2304) * h3
    + (v1Radical^2/768 + v1Radical * Real.sqrt 3/256 - 161/3072) * h11
    + (-Real.sqrt 11 * Real.sqrt 3/384 + 3/128) * hN


/-- **Interval-arithmetic injectivity.** A family of points in `ℂ` is injective if each lies in a
rational box and the boxes are pairwise separated in the real or imaginary coordinate. This turns
`Injective vtx` (the 406 vertex-distinctness facts) into: 29 box-membership bounds (from √-bounds)
plus one *decidable* rational separation check `hsep`. -/
lemma injective_of_boxes {n : ℕ} (f : Fin n → ℂ) (reLo reHi imLo imHi : Fin n → ℚ)
    (hval : ∀ i, (reLo i : ℝ) ≤ (f i).re ∧ (f i).re ≤ (reHi i : ℝ) ∧
                 (imLo i : ℝ) ≤ (f i).im ∧ (f i).im ≤ (imHi i : ℝ))
    (hsep : ∀ i j, i ≠ j →
        reHi i < reLo j ∨ reHi j < reLo i ∨ imHi i < imLo j ∨ imHi j < imLo i) :
    Function.Injective f := by
  intro i j hij
  by_contra hne
  have hre : (f i).re = (f j).re := by rw [hij]
  have him : (f i).im = (f j).im := by rw [hij]
  obtain ⟨ri1, ri2, ii1, ii2⟩ := hval i
  obtain ⟨rj1, rj2, ij1, ij2⟩ := hval j
  rcases hsep i j hne with h | h | h | h
  · have : (reHi i : ℝ) < (reLo j : ℝ) := by exact_mod_cast h
    linarith
  · have : (reHi j : ℝ) < (reLo i : ℝ) := by exact_mod_cast h
    linarith
  · have : (imHi i : ℝ) < (imLo j : ℝ) := by exact_mod_cast h
    linarith
  · have : (imHi j : ℝ) < (imLo i : ℝ) := by exact_mod_cast h
    linarith

open scoped BigOperators

end UnitDistanceGraphs
