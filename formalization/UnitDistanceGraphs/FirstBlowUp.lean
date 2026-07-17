/-
[M23] Theorem 1: amenability of the Euclidean isometry group / first blow-up.

Matolcsi–Ruzsa–Varga–Zsámboki (2023) prove that the geometric and (finitary) fractional chromatic
numbers of the plane coincide, by exploiting amenability of the group of Euclidean
transformations of `ℝ²`. In their proof (Theorem 1, around their eq. (15)) a finite set `T` of
Euclidean transformations — mapping the shapes of a finite graph `H` to congruent shapes —
generates a countable **solvable**, hence **amenable**, group `K`; amenability yields the
**Følner property**, i.e. finite sets `Rₖ ⊆ K` with `|Rₖ·T △ Rₖ| / |Rₖ| → 0`. A fractional
coloring is then symmetrized by averaging its pullbacks over `Rₖ`:
`γ₀ = (1/|Rₖ|) · ∑_{σ ∈ Rₖ} σ⁻¹(γ̄|_{σH})`. (This is special to the plane: for `d ≥ 3` the Følner property fails for the Euclidean group,
and [M23] remark that the higher-dimensional analogue of their theorem is open.)

We follow [M23]'s **actual** argument (abstract amenability), not a constructive word-set
strengthening. The amenability of `ℂ ≃ᵢ ℂ` — and hence the existence of the Følner set `R` — is
supplied by:

* `Folner.lean` — `solvable + FolnerCond` theory formalized from scratch: closure under group
  extensions, the abelian/cyclic base cases, `folnerCond_of_isSolvable`.
* this file — `IsSolvable (ℂ ≃ᵢ ℂ)` (the plane isometry group `ℝ² ⋊ O(2)` is solvable), then
  `exists_folner_set` (for a finite set of isometries and `ε > 0`, a single nonempty finite
  `ε`-invariant `R` — no polynomial growth, no word-sets), then the averaging argument it feeds.

A word-set (polynomial-growth) route is *avoided on purpose*: for `G₂₉` the congruence group is
**not** crystallographic — it contains an irrational-angle rotation (e.g. `cong553`, whose linear
part has minimal polynomial `3x⁴+3x³+4x²+3x+3`, not a root of unity), so it has **exponential**
growth and its word-balls are not Følner. Amenability instead comes from solvability of the ambient
group `ℂ ≃ᵢ ℂ = ℝ² ⋊ O(2)` — and `O(2)` is solvable while for `d ≥ 3` the isometry group contains
free subgroups and is not amenable (as a discrete group), which is why the argument is special to
the plane.

## Decomposition

The component `exists_chi_f_gt` is proved through three layers (top to bottom):

1. `exists_chi_f_gt`     — real proof from `exists_blowup_close`.
2. `exists_blowup_close` — averaging: a fractional coloring of a large enough blow-up of `V`
                            symmetrizes to a geometric coloring of `V`, so `χ_gf V ≤ χ_f (blow-up) + ε`.
3. `exists_folner_set`   — the amenability input, from `IsSolvable (ℂ ≃ᵢ ℂ)`.
-/

import UnitDistanceGraphs.Definitions
import UnitDistanceGraphs.PlaneColoring
import UnitDistanceGraphs.Folner

namespace UnitDistanceGraphs

open Classical Filter Topology

/-! ### Solvability of the plane isometry group `ℂ ≃ᵢ ℂ`

The congruence group of `G₂₉` is a subgroup of `Isom(ℝ²) = ℂ ≃ᵢ ℂ`, which is **solvable**
(`ℝ² ⋊ O(2)`). This is the group-theoretic input that lets `Folner.folnerCond_of_isSolvable`
supply arbitrarily invariant finite sets for the congruence group (a polynomial-growth/word-ball
route is impossible here; see below).

We build it in two levels:
* `O(2) = ℂ ≃ₗᵢ[ℝ] ℂ` is solvable — a determinant hom to the abelian `ℝˣ` with kernel the
  (abelian) rotations, via Mathlib's classification `linear_isometry_complex`.
* `ℂ ≃ᵢ ℂ` is solvable — the linear-part hom (Mazur–Ulam) to `O(2)` with abelian translation kernel. -/

section
open Complex

/-! #### Level 1: `O(2) = ℂ ≃ₗᵢ[ℝ] ℂ` is solvable -/

/-- The determinant of a linear isometry of `ℂ`, as a homomorphism to the abelian group `ℝˣ`. -/
noncomputable def detHom : (ℂ ≃ₗᵢ[ℝ] ℂ) →* ℝˣ where
  toFun f := LinearEquiv.det f.toLinearEquiv
  map_one' := by rw [show (1 : ℂ ≃ₗᵢ[ℝ] ℂ).toLinearEquiv = 1 from rfl, map_one]
  map_mul' f g := by
    rw [show (f * g).toLinearEquiv = f.toLinearEquiv * g.toLinearEquiv from rfl, map_mul]

/-- `O(2) = ℂ ≃ₗᵢ[ℝ] ℂ` is solvable: the determinant hom to the abelian `ℝˣ` has kernel the
rotations (`range rotation`, abelian), so `solvable_of_ker_le_range` applies. -/
instance isSolvable_linearIsometryEquiv : IsSolvable (ℂ ≃ₗᵢ[ℝ] ℂ) := by
  haveI : IsSolvable Circle := isSolvable_of_comm mul_comm
  haveI : IsSolvable ℝˣ := isSolvable_of_comm mul_comm
  refine solvable_of_ker_le_range rotation detHom fun f hf => ?_
  rw [MonoidHom.mem_ker] at hf
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex f
  · exact ⟨a, ha.symm⟩
  · exfalso
    have h1 : detHom conjLIE = -1 := linearEquiv_det_conjLIE
    have h2 : detHom (rotation a) = 1 := linearEquiv_det_rotation a
    have hdet : detHom f = -1 := by
      rw [ha, show conjLIE.trans (rotation a) = rotation a * conjLIE from rfl, map_mul, h1, h2,
        one_mul]
    rw [hdet] at hf
    norm_num [Units.ext_iff] at hf

/-! #### Level 2: `ℂ ≃ᵢ ℂ` is solvable -/

/-- The linear part of a plane isometry acts by `v ↦ f v - f 0` (Mazur–Ulam: `f` is affine). -/
theorem linearPart_apply (f : ℂ ≃ᵢ ℂ) (v : ℂ) :
    f.toRealAffineIsometryEquiv.linearIsometryEquiv v = f v - f 0 := by
  have h := AffineIsometryEquiv.map_vsub f.toRealAffineIsometryEquiv v 0
  simpa [IsometryEquiv.coeFn_toRealAffineIsometryEquiv, vsub_eq_sub] using h

/-- The **linear-part homomorphism** `ℂ ≃ᵢ ℂ →* ℂ ≃ₗᵢ[ℝ] ℂ` (via Mazur–Ulam). Its `map_mul` is the
fact that the linear part of a composition is the composition of linear parts. -/
noncomputable def linHom : (ℂ ≃ᵢ ℂ) →* (ℂ ≃ₗᵢ[ℝ] ℂ) where
  toFun f := f.toRealAffineIsometryEquiv.linearIsometryEquiv
  map_one' := by
    refine LinearIsometryEquiv.ext fun v => ?_
    rw [linearPart_apply]
    show (1 : ℂ ≃ᵢ ℂ) v - (1 : ℂ ≃ᵢ ℂ) 0 = (1 : ℂ ≃ₗᵢ[ℝ] ℂ) v
    simp
  map_mul' f g := by
    refine LinearIsometryEquiv.ext fun v => ?_
    have hmul : (f.toRealAffineIsometryEquiv.linearIsometryEquiv
          * g.toRealAffineIsometryEquiv.linearIsometryEquiv) v
        = f.toRealAffineIsometryEquiv.linearIsometryEquiv
            (g.toRealAffineIsometryEquiv.linearIsometryEquiv v) :=
      LinearIsometryEquiv.trans_apply _ _ _
    rw [hmul, linearPart_apply g, map_sub, linearPart_apply f, linearPart_apply f,
      linearPart_apply (f * g)]
    show f (g v) - f (g 0) = f (g v) - f 0 - (f (g 0) - f 0)
    ring

/-- Translations of `ℂ` as a homomorphism from the (abelian) additive group of `ℂ`. -/
noncomputable def transHom : Multiplicative ℂ →* (ℂ ≃ᵢ ℂ) where
  toFun t := IsometryEquiv.constVAdd (Multiplicative.toAdd t)
  map_one' := IsometryEquiv.ext fun z => by
    simp [IsometryEquiv.constVAdd_apply]
  map_mul' s t := IsometryEquiv.ext fun z => by
    show IsometryEquiv.constVAdd (Multiplicative.toAdd (s * t)) z
      = IsometryEquiv.constVAdd (Multiplicative.toAdd s)
          (IsometryEquiv.constVAdd (Multiplicative.toAdd t) z)
    simp only [toAdd_mul, IsometryEquiv.constVAdd_apply, vadd_eq_add]
    ring

/-- **The plane isometry group `ℂ ≃ᵢ ℂ` is solvable** (`ℝ² ⋊ O(2)`): the linear-part hom to the
solvable `O(2)` has abelian translation kernel, so `solvable_of_ker_le_range` applies. -/
instance isSolvable_isometryEquiv : IsSolvable (ℂ ≃ᵢ ℂ) := by
  haveI : IsSolvable (Multiplicative ℂ) := isSolvable_of_comm mul_comm
  refine solvable_of_ker_le_range transHom linHom fun f hf => ?_
  rw [MonoidHom.mem_ker] at hf
  have key : ∀ z, f z = f 0 + z := by
    intro z
    have h1 : f.toRealAffineIsometryEquiv.linearIsometryEquiv z = z := by
      have h2 : linHom f z = z := by rw [hf]; rfl
      exact h2
    rw [linearPart_apply] at h1
    linear_combination h1
  refine ⟨Multiplicative.ofAdd (f 0), IsometryEquiv.ext fun z => ?_⟩
  show IsometryEquiv.constVAdd (f 0) z = f z
  rw [IsometryEquiv.constVAdd_apply, vadd_eq_add]
  exact (key z).symm
end

/-! ### The Følner set the averaging needs, from solvability of `ℂ ≃ᵢ ℂ`

Bridges `Folner.folnerCond_of_isSolvable` (applied to the solvable group `ℂ ≃ᵢ ℂ`) to the concrete
input of the averaging argument below: a single nonempty finite set `R` that is right-`ε`-invariant
(two-sided symmetric-difference ratio `< ε`) under every isometry in a given finite set `T` of
congruence realizers. No polynomial-growth / word-set hypothesis is used. -/

section
open UnitDistanceGraphs.Folner
open scoped Pointwise

/-- **Amenability input for the plane averaging.** For any finite set `T` of plane isometries and
`ε > 0`, there is a nonempty finite `R ⊆ ℂ ≃ᵢ ℂ` whose two-sided symmetric-difference ratio under
right translation by each `τ ∈ T` is `< ε`. Proved from solvability of `ℂ ≃ᵢ ℂ`
(`folnerCond_of_isSolvable`) via the left→right bridge `ratio_inv`. -/
lemma exists_folner_set (T : Finset (ℂ ≃ᵢ ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : Finset (ℂ ≃ᵢ ℂ), R.Nonempty ∧ ∀ τ ∈ T,
      (((R \ R.image (· * τ)).card + (R.image (· * τ) \ R).card : ℝ)) / R.card < ε := by
  obtain ⟨F, hFne, hF⟩ :=
    folnerCond_of_isSolvable (G := ℂ ≃ᵢ ℂ) (T.image (·⁻¹)) (show (0 : ℝ) < ε / 2 by linarith)
  refine ⟨F⁻¹, by rw [Finset.inv_def]; exact hFne.image _, fun τ hτ => ?_⟩
  have h1 : ratio τ F⁻¹ < ε / 2 := by
    rw [ratio_inv]
    exact hF τ⁻¹ (Finset.mem_image.mpr ⟨τ, hτ, rfl⟩)
  rw [twoSided_eq]
  linarith

end

noncomputable section

/-! ### Blow-ups and word-sets -/

/-- The **blow-up** of a finite unit-distance graph `V` by a finite set `T` of plane isometries:
the union of the congruent copies `g(V)` for `g ∈ T`. -/
def blowup (T : Finset (ℂ ≃ᵢ ℂ)) (V : UnitDistanceGraph) : UnitDistanceGraph :=
  T.biUnion (fun g => V.image (g : ℂ → ℂ))

/-- The weight of a fractional coloring is nonnegative. -/
lemma weight_nonneg {V : UnitDistanceGraph} {γ : Finset ℂ → ℝ}
    (h : IsFractionalColoring V γ) : 0 ≤ weight V γ :=
  Finset.sum_nonneg (fun S hS => h.nonneg S hS)

/-- `weight` is continuous in the coloring (product topology on `Finset ℂ → ℝ`). -/
lemma continuous_weight (V : UnitDistanceGraph) :
    Continuous (fun γ : Finset ℂ → ℝ => weight V γ) := by
  unfold weight; fun_prop

/-- `marginal … Y` is continuous in the coloring. -/
lemma continuous_marginal (V : UnitDistanceGraph) (Y : Finset ℂ) :
    Continuous (fun γ : Finset ℂ → ℝ => marginal V γ Y) := by
  unfold marginal; fun_prop

/-- **[M23] eq. (7): weight stability.** If a fractional coloring of `V` has marginals that are
`δ`-close on congruent subsets, then its weight exceeds `χ_gf V - ε`. The geometric LP optimum
`χ_gf` is approached continuously as the congruence-invariance defect shrinks: a sequence of
colorings whose defect `→ 0` lives in a compact box, and a convergent subsequence has an *exactly*
geometric limit, which cannot beat the infimum `χ_gf`. -/
theorem weight_stability (V : UnitDistanceGraph) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ γ : Finset ℂ → ℝ, IsFractionalColoring V γ →
      (∀ Y ∈ V.powerset, ∀ Y' ∈ V.powerset, Congruent Y Y' →
        |marginal V γ Y - marginal V γ Y'| < δ) →
      χ_gf V - ε < weight V γ := by
  by_contra hcon
  push Not at hcon
  set M : ℝ := χ_gf V - ε with hM
  -- `M ≥ 0`, using any one witness coloring.
  obtain ⟨γ₁, hcol₁, -, hw₁⟩ := hcon 1 one_pos
  have hM0 : 0 ≤ M := le_trans (weight_nonneg hcol₁) hw₁
  -- A sequence of colorings with `1/(n+1)`-invariant marginals and weight `≤ M`.
  have hseq : ∀ n : ℕ, ∃ γ : Finset ℂ → ℝ, IsFractionalColoring V γ ∧
      (∀ Y ∈ V.powerset, ∀ Y' ∈ V.powerset, Congruent Y Y' →
        |marginal V γ Y - marginal V γ Y'| < (1 : ℝ) / ((n : ℝ) + 1)) ∧
      weight V γ ≤ M := fun n => hcon _ (by positivity)
  choose γseq hcolseq hinvseq hwseq using hseq
  -- Truncate each coloring to its independent-set support (does not change weight/marginals).
  set γ' : ℕ → Finset ℂ → ℝ := fun n S => if S ∈ indepSets V then γseq n S else 0 with hγ'def
  have hmargeq : ∀ n Y, marginal V (γ' n) Y = marginal V (γseq n) Y := by
    intro n Y
    unfold marginal
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [Finset.mem_filter] at hS
    simp only [hγ'def]; rw [if_pos hS.1]
  have hweighteq : ∀ n, weight V (γ' n) = weight V (γseq n) := by
    intro n
    unfold weight
    refine Finset.sum_congr rfl (fun S hS => ?_)
    simp only [hγ'def]; rw [if_pos hS]
  have hcol'seq : ∀ n, IsFractionalColoring V (γ' n) := by
    intro n
    refine ⟨fun S hS => ?_, fun v hv => ?_⟩
    · simp only [hγ'def]; rw [if_pos hS]; exact (hcolseq n).nonneg S hS
    · rw [hmargeq]; exact (hcolseq n).covers v hv
  -- The truncated colorings, restricted to `indepSets V`, live in a compact box.
  set ι := {S : Finset ℂ // S ∈ indepSets V} with hιdef
  set B : Set (ι → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) M) with hBdef
  have hBcompact : IsCompact B := isCompact_univ_pi (fun _ => isCompact_Icc)
  set xseq : ℕ → ι → ℝ := fun n i => γ' n i.1 with hxdef
  have hmem : ∀ n, xseq n ∈ B := by
    intro n
    rw [hBdef, Set.mem_univ_pi]
    intro i
    have hSi : i.1 ∈ indepSets V := i.2
    have hval : xseq n i = γseq n i.1 := by
      simp only [hxdef, hγ'def]; rw [if_pos hSi]
    rw [hval]
    refine ⟨(hcolseq n).nonneg i.1 hSi, ?_⟩
    calc γseq n i.1 ≤ weight V (γseq n) :=
          Finset.single_le_sum (fun j hj => (hcolseq n).nonneg j hj) hSi
      _ ≤ M := hwseq n
  obtain ⟨a, ha, φ, hφmono, hφtend⟩ := hBcompact.tendsto_subseq hmem
  -- The limit coloring.
  set γstar : Finset ℂ → ℝ := fun S => if h : S ∈ indepSets V then a ⟨S, h⟩ else 0 with hstardef
  -- Subsequence converges to `γstar` in the product topology.
  have hconv : Tendsto (fun n => γ' (φ n)) atTop (𝓝 γstar) := by
    rw [tendsto_pi_nhds]
    intro S
    by_cases hS : S ∈ indepSets V
    · have key := (tendsto_pi_nhds.mp hφtend) ⟨S, hS⟩
      simp only [hxdef, Function.comp_apply] at key
      simp only [hstardef, dif_pos hS]
      exact key
    · simp only [hγ'def, hstardef, if_neg hS, dif_neg hS]
      exact tendsto_const_nhds
  -- `γstar` has weight `≤ M`.
  have hwstar : weight V γstar ≤ M := by
    have ht : Tendsto (fun n => weight V (γ' (φ n))) atTop (𝓝 (weight V γstar)) :=
      ((continuous_weight V).tendsto γstar).comp hconv
    refine le_of_tendsto ht (Filter.Eventually.of_forall (fun n => ?_))
    rw [hweighteq]; exact hwseq (φ n)
  -- `γstar` is a fractional coloring.
  have hnonneg_star : ∀ S ∈ indepSets V, 0 ≤ γstar S := by
    intro S hS
    have hai : a ⟨S, hS⟩ ∈ Set.Icc (0 : ℝ) M := (Set.mem_univ_pi.mp ha) ⟨S, hS⟩
    simp only [hstardef, dif_pos hS]; exact hai.1
  have hcovers_star : ∀ v ∈ V, 1 ≤ marginal V γstar {v} := by
    intro v hv
    have ht : Tendsto (fun n => marginal V (γ' (φ n)) {v}) atTop (𝓝 (marginal V γstar {v})) :=
      ((continuous_marginal V {v}).tendsto γstar).comp hconv
    refine ge_of_tendsto ht (Filter.Eventually.of_forall (fun n => ?_))
    rw [hmargeq]; exact (hcolseq (φ n)).covers v hv
  -- `γstar` is exactly geometric: the defect vanishes in the limit.
  have hgeom_star : ∀ Y ∈ V.powerset, ∀ Y' ∈ V.powerset, Congruent Y Y' →
      marginal V γstar Y = marginal V γstar Y' := by
    intro Y hY Y' hY' hcong
    have htd : Tendsto (fun n => marginal V (γ' (φ n)) Y - marginal V (γ' (φ n)) Y') atTop
        (𝓝 (marginal V γstar Y - marginal V γstar Y')) :=
      (((continuous_marginal V Y).tendsto γstar).comp hconv).sub
        (((continuous_marginal V Y').tendsto γstar).comp hconv)
    have hφat : Tendsto φ atTop atTop := hφmono.tendsto_atTop
    have htend0 : Tendsto (fun n => (1 : ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφat
    have hd0 : Tendsto (fun n => marginal V (γ' (φ n)) Y - marginal V (γ' (φ n)) Y') atTop (𝓝 0) :=
      squeeze_zero_norm
        (fun n => by
          rw [Real.norm_eq_abs, hmargeq, hmargeq]
          exact le_of_lt (hinvseq (φ n) Y hY Y' hY' hcong)) htend0
    exact sub_eq_zero.mp (tendsto_nhds_unique htd hd0)
  -- Contradiction: the geometric limit cannot beat the infimum `χ_gf`.
  have hgcol : IsGeometricFractionalColoring V γstar :=
    { nonneg := hnonneg_star, covers := hcovers_star, geometric := hgeom_star }
  have hbdd : BddBelow (geomColoringWeights V) :=
    ⟨0, fun w hw => by obtain ⟨γ, hγ, rfl⟩ := hw; exact weight_nonneg hγ.toIsFractionalColoring⟩
  have hle : χ_gf V ≤ weight V γstar := csInf_le hbdd ⟨γstar, hgcol, rfl⟩
  linarith

/-! ### Attainment of `χ_f` (an optimal coloring exists) -/

/-- Truncate a coloring to its independent-set support. -/
def truncate (G : UnitDistanceGraph) (γ : Finset ℂ → ℝ) : Finset ℂ → ℝ :=
  fun S => if S ∈ indepSets G then γ S else 0

@[simp] lemma truncate_apply (G : UnitDistanceGraph) (γ : Finset ℂ → ℝ) (S : Finset ℂ) :
    truncate G γ S = if S ∈ indepSets G then γ S else 0 := rfl

lemma weight_truncate (G : UnitDistanceGraph) (γ : Finset ℂ → ℝ) :
    weight G (truncate G γ) = weight G γ := by
  unfold weight
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [truncate_apply, if_pos hS]

lemma marginal_truncate (G : UnitDistanceGraph) (γ : Finset ℂ → ℝ) (Y : Finset ℂ) :
    marginal G (truncate G γ) Y = marginal G γ Y := by
  unfold marginal
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.mem_filter] at hS
  rw [truncate_apply, if_pos hS.1]

lemma isFractionalColoring_truncate (G : UnitDistanceGraph) (γ : Finset ℂ → ℝ)
    (h : IsFractionalColoring G γ) : IsFractionalColoring G (truncate G γ) :=
  ⟨fun S hS => by rw [truncate_apply, if_pos hS]; exact h.nonneg S hS,
   fun v hv => by rw [marginal_truncate]; exact h.covers v hv⟩

/-- **Attainment.** The fractional chromatic number of a finite unit-distance graph is attained
by some fractional coloring. Proof by compactness: the truncated colorings valued in `[0, W₀]`
form a Tychonoff-compact box, the feasible set is closed, and `weight` is continuous, so its
minimum over feasible colorings is attained; that minimum equals `χ_f G`. -/
theorem exists_optimal_coloring (G : UnitDistanceGraph) :
    ∃ γ : Finset ℂ → ℝ, IsFractionalColoring G γ ∧ weight G γ = χ_f G := by
  -- A feasible "singleton" coloring, giving nonemptiness and a weight bound.
  set γsing : Finset ℂ → ℝ := fun S => if ∃ v, v ∈ G ∧ S = {v} then 1 else 0 with hsingdef
  have hsing01 : ∀ S, γsing S = 0 ∨ γsing S = 1 := by
    intro S; simp only [hsingdef]; split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hsingnonneg : ∀ S, 0 ≤ γsing S := fun S =>
    (hsing01 S).elim (fun h => by rw [h]) (fun h => by rw [h]; norm_num)
  have hsingle1 : ∀ S, γsing S ≤ 1 := fun S =>
    (hsing01 S).elim (fun h => by rw [h]; norm_num) (fun h => by rw [h])
  have hsingoff : ∀ S, S ∉ indepSets G → γsing S = 0 := by
    intro S hS; simp only [hsingdef]; rw [if_neg]
    rintro ⟨v, hv, rfl⟩; exact hS (singleton_mem_indepSets hv)
  have hsingval : ∀ v ∈ G, γsing {v} = 1 := by
    intro v hv; simp only [hsingdef]; rw [if_pos ⟨v, hv, rfl⟩]
  have hsingcol : IsFractionalColoring G γsing := by
    refine ⟨fun S _ => hsingnonneg S, fun v hv => ?_⟩
    have hmemf : ({v} : Finset ℂ) ∈ (indepSets G).filter (fun S => {v} ⊆ S) :=
      Finset.mem_filter.mpr ⟨singleton_mem_indepSets hv, Finset.Subset.refl _⟩
    calc (1 : ℝ) = γsing {v} := (hsingval v hv).symm
      _ ≤ marginal G γsing {v} := Finset.single_le_sum (fun S _ => hsingnonneg S) hmemf
  -- The weight bound and compact box.
  set W₀ : ℝ := weight G γsing + 1 with hW₀def
  have hsingleW₀ : ∀ S, γsing S ≤ W₀ := fun S => by
    have := hsingle1 S; have := weight_nonneg hsingcol; rw [hW₀def]; linarith
  set box : Set (Finset ℂ → ℝ) :=
    Set.univ.pi (fun S => if S ∈ indepSets G then Set.Icc (0 : ℝ) W₀ else {(0 : ℝ)}) with hboxdef
  have hboxcompact : IsCompact box := by
    rw [hboxdef]
    exact isCompact_univ_pi (fun S => by split_ifs; exacts [isCompact_Icc, isCompact_singleton])
  have hFclosed : IsClosed {γ : Finset ℂ → ℝ | IsFractionalColoring G γ} := by
    have hset : {γ : Finset ℂ → ℝ | IsFractionalColoring G γ}
        = (⋂ S ∈ indepSets G, {γ : Finset ℂ → ℝ | 0 ≤ γ S})
          ∩ (⋂ v ∈ G, {γ : Finset ℂ → ℝ | 1 ≤ marginal G γ {v}}) := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact ⟨fun h => ⟨fun S hS => h.nonneg S hS, fun v hv => h.covers v hv⟩,
        fun h => ⟨fun S hS => h.1 S hS, fun v hv => h.2 v hv⟩⟩
    rw [hset]
    exact IsClosed.inter
      (isClosed_biInter (fun S _ => isClosed_le continuous_const (continuous_apply S)))
      (isClosed_biInter (fun v _ => isClosed_le continuous_const (continuous_marginal G {v})))
  -- The singleton coloring lies in the compact feasible box.
  have hsingK : γsing ∈ box ∩ {γ | IsFractionalColoring G γ} := by
    refine ⟨?_, hsingcol⟩
    rw [hboxdef, Set.mem_univ_pi]
    intro S
    by_cases hS : S ∈ indepSets G
    · rw [if_pos hS]; exact ⟨hsingnonneg S, hsingleW₀ S⟩
    · rw [if_neg hS, Set.mem_singleton_iff]; exact hsingoff S hS
  have hKcompact : IsCompact (box ∩ {γ | IsFractionalColoring G γ}) :=
    hboxcompact.inter_right hFclosed
  -- Minimize the (continuous) weight over the compact feasible box.
  obtain ⟨γstar, hγstarmem, hγstarmin⟩ :=
    hKcompact.exists_isMinOn ⟨γsing, hsingK⟩ (continuous_weight G).continuousOn
  have hmin := isMinOn_iff.mp hγstarmin
  have hbdd : BddBelow {w | ∃ γ, IsFractionalColoring G γ ∧ weight G γ = w} :=
    ⟨0, fun w hw => by obtain ⟨γ, hγ, rfl⟩ := hw; exact weight_nonneg hγ⟩
  have hstarleW₀ : weight G γstar ≤ W₀ := by
    have := hmin γsing hsingK; rw [hW₀def]; linarith
  refine ⟨γstar, hγstarmem.2, le_antisymm ?_ (csInf_le hbdd ⟨γstar, hγstarmem.2, rfl⟩)⟩
  -- `weight γstar` is a lower bound for all feasible weights.
  refine le_csInf ⟨weight G γsing, γsing, hsingcol, rfl⟩ ?_
  rintro w ⟨γ, hγfeas, rfl⟩
  by_cases hw : weight G γ ≤ W₀
  · have htruncK : truncate G γ ∈ box ∩ {γ | IsFractionalColoring G γ} := by
      refine ⟨?_, isFractionalColoring_truncate G γ hγfeas⟩
      rw [hboxdef, Set.mem_univ_pi]
      intro S
      by_cases hS : S ∈ indepSets G
      · rw [if_pos hS, truncate_apply, if_pos hS]
        refine ⟨hγfeas.nonneg S hS, ?_⟩
        calc γ S ≤ weight G γ := Finset.single_le_sum (fun j hj => hγfeas.nonneg j hj) hS
          _ ≤ W₀ := hw
      · rw [if_neg hS, Set.mem_singleton_iff, truncate_apply, if_neg hS]
    have h1 := hmin (truncate G γ) htruncK
    rwa [weight_truncate] at h1
  · push Not at hw; linarith [hstarleW₀]

/-! ### Isometries preserve independence

The pullback/averaging construction moves colorings between congruent copies via plane isometries.
Since isometries preserve distances, they preserve unit-distance adjacency, hence independence. -/

/-- A plane isometry preserves unit-distance adjacency. -/
lemma isometry_adj (σ : ℂ ≃ᵢ ℂ) (x y : ℂ) :
    planeGraph.Adj (σ x) (σ y) ↔ planeGraph.Adj x y := by
  show dist (σ x) (σ y) = 1 ↔ dist x y = 1
  rw [σ.dist_eq]

/-- A plane isometry maps independent sets to independent sets. -/
lemma isometry_isIndepSet (σ : ℂ ≃ᵢ ℂ) (s : Finset ℂ) :
    planeGraph.IsIndepSet (↑(s.image (σ : ℂ → ℂ))) ↔ planeGraph.IsIndepSet (↑s) := by
  simp only [SimpleGraph.isIndepSet_iff, Finset.coe_image]
  rw [(σ.injective.injOn).pairwise_image]
  have hpred : (Function.onFun (fun v w : ℂ => ¬ planeGraph.Adj v w) (σ : ℂ → ℂ))
      = (fun v w : ℂ => ¬ planeGraph.Adj v w) := by
    funext a b; exact propext (not_congr (isometry_adj σ a b))
  rw [hpred]

/-! ### Pullback of a coloring onto a congruent copy

Given a coloring `γ` of the blow-up `G` and `σ ∈ R_k`, we push `γ` onto `V` by marginalising each
independent set `I` of `G` onto the copy `σV` and pulling back via `σ⁻¹`. This is `σ⁻¹(γ̄|_{σV})`
of [M23]. The projection `proj σ V I = σ⁻¹(I ∩ σV)` sends `I` to an independent set of `V`. -/

/-- Project an independent set `I` of the blow-up onto the copy `σV`, pulled back to `V`. -/
def proj (σ : ℂ ≃ᵢ ℂ) (V : UnitDistanceGraph) (I : Finset ℂ) : Finset ℂ :=
  (I ∩ V.image (σ : ℂ → ℂ)).image (σ.symm : ℂ → ℂ)

lemma proj_subset (σ : ℂ ≃ᵢ ℂ) (V : UnitDistanceGraph) (I : Finset ℂ) : proj σ V I ⊆ V := by
  intro x hx
  rw [proj, Finset.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  rw [Finset.mem_inter, Finset.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz.2
  rw [σ.symm_apply_apply]
  exact hw

lemma proj_isIndepSet (σ : ℂ ≃ᵢ ℂ) (V : UnitDistanceGraph) {I : Finset ℂ}
    (hI : planeGraph.IsIndepSet (↑I)) : planeGraph.IsIndepSet (↑(proj σ V I)) := by
  rw [proj, isometry_isIndepSet]
  exact Set.Pairwise.mono (Finset.coe_subset.mpr Finset.inter_subset_left) hI

lemma proj_mem_indepSets (σ : ℂ ≃ᵢ ℂ) (V : UnitDistanceGraph) {I : Finset ℂ}
    (hI : planeGraph.IsIndepSet (↑I)) : proj σ V I ∈ indepSets V := by
  unfold indepSets
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨proj_subset σ V I, proj_isIndepSet σ V hI⟩

/-- `Y ⊆ σ⁻¹(I ∩ σV)` iff `σY ⊆ I`, for `Y ⊆ V`. -/
lemma subset_proj_iff (σ : ℂ ≃ᵢ ℂ) (V : UnitDistanceGraph) {Y I : Finset ℂ} (hY : Y ⊆ V) :
    Y ⊆ proj σ V I ↔ Y.image (σ : ℂ → ℂ) ⊆ I := by
  rw [proj]
  constructor
  · intro h x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hyY, rfl⟩ := hx
    have hy := h hyY
    rw [Finset.mem_image] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : (σ : ℂ → ℂ) y = z := by rw [← hzy, σ.apply_symm_apply]
    rw [this]
    exact (Finset.mem_inter.mp hz).1
  · intro h y hyY
    rw [Finset.mem_image]
    refine ⟨(σ : ℂ → ℂ) y, ?_, σ.symm_apply_apply y⟩
    exact Finset.mem_inter.mpr ⟨h (Finset.mem_image.mpr ⟨y, hyY, rfl⟩),
      Finset.mem_image.mpr ⟨y, hY hyY, rfl⟩⟩

/-- The pullback coloring `σ⁻¹(γ̄|_{σV})` on `V`: the weight `γ` gives an independent set `T ⊆ V`
is the total `γ`-weight of blow-up independent sets projecting to `T`. -/
def pullback (σ : ℂ ≃ᵢ ℂ) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ) : Finset ℂ → ℝ :=
  fun T => ∑ I ∈ indepSets G, if proj σ V I = T then γ I else 0

/-- **[M23] eq. (11): the pullback preserves total weight.** -/
lemma weight_pullback (σ : ℂ ≃ᵢ ℂ) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ) :
    weight V (pullback σ G V γ) = weight G γ := by
  unfold weight pullback
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun I hI => ?_)
  have hIi : planeGraph.IsIndepSet (↑I) := (Finset.mem_filter.mp hI).2
  rw [Finset.sum_ite_eq, if_pos (proj_mem_indepSets σ V hIi)]

/-- The pullback marginal at `Y ⊆ V` equals the blow-up marginal at `σY`. -/
lemma marginal_pullback (σ : ℂ ≃ᵢ ℂ) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ)
    {Y : Finset ℂ} (hY : Y ⊆ V) :
    marginal V (pullback σ G V γ) Y = marginal G γ (Y.image (σ : ℂ → ℂ)) := by
  have hL : marginal V (pullback σ G V γ) Y
      = ∑ I ∈ indepSets G, if Y.image (σ : ℂ → ℂ) ⊆ I then γ I else 0 := by
    unfold marginal pullback
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun I hI => ?_)
    have hIi : planeGraph.IsIndepSet (↑I) := (Finset.mem_filter.mp hI).2
    rw [Finset.sum_ite_eq]
    by_cases hsub : Y.image (σ : ℂ → ℂ) ⊆ I
    · rw [if_pos hsub, if_pos (Finset.mem_filter.mpr
        ⟨proj_mem_indepSets σ V hIi, (subset_proj_iff σ V hY).mpr hsub⟩)]
    · rw [if_neg hsub, if_neg (fun hmem =>
        hsub ((subset_proj_iff σ V hY).mp (Finset.mem_filter.mp hmem).2))]
  rw [hL]
  unfold marginal
  rw [Finset.sum_filter]

/-- The pullback of a fractional coloring of the blow-up is a fractional coloring of `V`. -/
lemma isFractionalColoring_pullback (σ : ℂ ≃ᵢ ℂ) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ)
    (hσ : V.image (σ : ℂ → ℂ) ⊆ G) (hγ : IsFractionalColoring G γ) :
    IsFractionalColoring V (pullback σ G V γ) := by
  refine ⟨fun T _ => ?_, fun v hv => ?_⟩
  · apply Finset.sum_nonneg
    intro I hI
    split_ifs with h
    · exact hγ.nonneg I hI
    · exact le_rfl
  · rw [marginal_pullback σ G V γ (Finset.singleton_subset_iff.mpr hv), Finset.image_singleton]
    exact hγ.covers (σ v) (hσ (Finset.mem_image.mpr ⟨v, hv, rfl⟩))

/-! ### Averaging the pullbacks over `R_k` -/

/-- The average of the pullbacks of `γ` over `R`: `γ₀ = (1/|R|) ∑_{σ∈R} σ⁻¹(γ̄|_{σV})`. -/
def avgColoring (R : Finset (ℂ ≃ᵢ ℂ)) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ) :
    Finset ℂ → ℝ :=
  fun T => (∑ σ ∈ R, pullback σ G V γ T) / R.card

lemma weight_avgColoring (R : Finset (ℂ ≃ᵢ ℂ)) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ) :
    weight V (avgColoring R G V γ) = (∑ σ ∈ R, weight V (pullback σ G V γ)) / R.card := by
  unfold weight avgColoring
  rw [← Finset.sum_div, Finset.sum_comm]

lemma marginal_avgColoring (R : Finset (ℂ ≃ᵢ ℂ)) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ)
    (Y : Finset ℂ) :
    marginal V (avgColoring R G V γ) Y = (∑ σ ∈ R, marginal V (pullback σ G V γ) Y) / R.card := by
  unfold marginal avgColoring
  rw [← Finset.sum_div, Finset.sum_comm]

/-- **[M23] eq. (11) after averaging: the average preserves total weight.** -/
lemma weight_avgColoring_eq (R : Finset (ℂ ≃ᵢ ℂ)) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ)
    (hR : R.Nonempty) : weight V (avgColoring R G V γ) = weight G γ := by
  have hcard : (R.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hR).ne'
  rw [weight_avgColoring]
  simp only [weight_pullback, Finset.sum_const, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hcard]

/-- The average of pullbacks of a fractional coloring of the blow-up is a fractional coloring. -/
lemma isFractionalColoring_avgColoring (R : Finset (ℂ ≃ᵢ ℂ)) (G V : UnitDistanceGraph)
    (γ : Finset ℂ → ℝ) (hR : R.Nonempty) (hσ : ∀ σ ∈ R, V.image (σ : ℂ → ℂ) ⊆ G)
    (hγ : IsFractionalColoring G γ) : IsFractionalColoring V (avgColoring R G V γ) := by
  have hcardpos : (0 : ℝ) < R.card := by exact_mod_cast Finset.card_pos.mpr hR
  refine ⟨fun T _ => ?_, fun v hv => ?_⟩
  · unfold avgColoring
    refine div_nonneg (Finset.sum_nonneg (fun σ hσR => ?_)) (le_of_lt hcardpos)
    exact (isFractionalColoring_pullback σ G V γ (hσ σ hσR) hγ).nonneg T ‹_›
  · rw [marginal_avgColoring, le_div_iff₀ hcardpos, one_mul]
    calc (R.card : ℝ) = ∑ _σ ∈ R, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ σ ∈ R, marginal V (pullback σ G V γ) {v} :=
          Finset.sum_le_sum (fun σ hσR =>
            (isFractionalColoring_pullback σ G V γ (hσ σ hσR) hγ).covers v hv)

/-! ### The eq-20 defect bound (algebraic reduction) -/

/-- Any marginal of a nonnegative coloring is bounded by its total weight. -/
lemma abs_marginal_le_weight {G : UnitDistanceGraph} {γ : Finset ℂ → ℝ}
    (hγ : ∀ S ∈ indepSets G, 0 ≤ γ S) (Z : Finset ℂ) : |marginal G γ Z| ≤ weight G γ := by
  have hnn : 0 ≤ marginal G γ Z :=
    Finset.sum_nonneg (fun I hI => hγ I (Finset.mem_filter.mp hI).1)
  rw [abs_of_nonneg hnn]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun I hI _ => hγ I hI)

/-- **[M23] eq. (20): the averaged marginal defect is controlled by a symmetric difference.**
For congruent `Y, Y' = τY ⊆ V`, the difference of averaged marginals is bounded by the total
weight times the (right-)Følner ratio of `R` under `τ`. -/
lemma avgColoring_marginal_diff_le
    (R : Finset (ℂ ≃ᵢ ℂ)) (G V : UnitDistanceGraph) (γ : Finset ℂ → ℝ)
    (hγ : ∀ S ∈ indepSets G, 0 ≤ γ S)
    (τ : ℂ ≃ᵢ ℂ) {Y : Finset ℂ} (hY : Y ⊆ V) (hY' : Y.image (τ : ℂ → ℂ) ⊆ V) :
    |marginal V (avgColoring R G V γ) Y
        - marginal V (avgColoring R G V γ) (Y.image (τ : ℂ → ℂ))|
      ≤ weight G γ
        * (((R \ R.image (· * τ)).card + (R.image (· * τ) \ R).card : ℝ)) / R.card := by
  set h : (ℂ ≃ᵢ ℂ) → ℝ := fun ρ => marginal G γ (Y.image (ρ : ℂ → ℂ)) with hh
  have hbound : ∀ ρ, |h ρ| ≤ weight G γ := fun ρ => by rw [hh]; exact abs_marginal_le_weight hγ _
  have hmY : marginal V (avgColoring R G V γ) Y = (∑ σ ∈ R, h σ) / R.card := by
    rw [marginal_avgColoring]; congr 1
    exact Finset.sum_congr rfl (fun σ _ => marginal_pullback σ G V γ hY)
  have hmY' : marginal V (avgColoring R G V γ) (Y.image (τ : ℂ → ℂ))
      = (∑ σ ∈ R, h (σ * τ)) / R.card := by
    rw [marginal_avgColoring]; congr 1
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [marginal_pullback σ G V γ hY', hh]
    congr 1
    rw [Finset.image_image, IsometryEquiv.coe_mul]
  have hreindex : ∑ σ ∈ R, h (σ * τ) = ∑ ρ ∈ R.image (· * τ), h ρ :=
    (Finset.sum_image (fun x _ y _ hxy => mul_left_injective τ hxy)).symm
  have hsplit : ∀ s t : Finset (ℂ ≃ᵢ ℂ), ∑ x ∈ s, h x = ∑ x ∈ s \ t, h x + ∑ x ∈ s ∩ t, h x := by
    intro s t
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter s t), Finset.sdiff_union_inter]
  have e1 := hsplit R (R.image (· * τ))
  have e2 := hsplit (R.image (· * τ)) R
  rw [Finset.inter_comm] at e2
  have hX : ∑ σ ∈ R, h σ - ∑ ρ ∈ R.image (· * τ), h ρ
      = ∑ σ ∈ R \ R.image (· * τ), h σ - ∑ ρ ∈ R.image (· * τ) \ R, h ρ := by linarith [e1, e2]
  have hnum : |∑ σ ∈ R, h σ - ∑ ρ ∈ R.image (· * τ), h ρ|
      ≤ weight G γ * ((R \ R.image (· * τ)).card + (R.image (· * τ) \ R).card) := by
    rw [hX]
    calc |∑ σ ∈ R \ R.image (· * τ), h σ - ∑ ρ ∈ R.image (· * τ) \ R, h ρ|
        ≤ |∑ σ ∈ R \ R.image (· * τ), h σ| + |∑ ρ ∈ R.image (· * τ) \ R, h ρ| := abs_sub _ _
      _ ≤ (∑ _σ ∈ R \ R.image (· * τ), weight G γ)
            + (∑ _ρ ∈ R.image (· * τ) \ R, weight G γ) := by
          gcongr
          · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ρ _ => hbound ρ))
          · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun ρ _ => hbound ρ))
      _ = weight G γ * ((R \ R.image (· * τ)).card + (R.image (· * τ) \ R).card) := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
  rw [hmY, hmY', div_sub_div_same, hreindex, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (R.card : ℝ))]
  gcongr

/-- A **finite set of congruence realizers**: for every congruent pair `Y, Y' ⊆ V` there is an
isometry `τ ∈ T` with `Y' = τ(Y)`. (Realizers come directly from `Congruent`; no generating set or
finitely-generated group is needed.) -/
theorem exists_congruence_realizer_finset (V : UnitDistanceGraph) :
    ∃ T : Finset (ℂ ≃ᵢ ℂ), ∀ Y ∈ V.powerset, ∀ Y' ∈ V.powerset, Congruent Y Y' →
      ∃ τ ∈ T, Y' = Y.image (τ : ℂ → ℂ) := by
  classical
  set realizer : Finset ℂ × Finset ℂ → (ℂ ≃ᵢ ℂ) := fun p =>
    if h : Congruent p.1 p.2 then Classical.choose h else 1 with hrealizer
  refine ⟨(V.powerset ×ˢ V.powerset).image realizer, fun Y hY Y' hY' hc => ?_⟩
  refine ⟨realizer (Y, Y'),
    Finset.mem_image.mpr ⟨(Y, Y'), Finset.mem_product.mpr ⟨hY, hY'⟩, rfl⟩, ?_⟩
  simp only [hrealizer, dif_pos hc]
  exact Classical.choose_spec hc

theorem exists_averaged_coloring (V : UnitDistanceGraph) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (R : Finset (ℂ ≃ᵢ ℂ)), ∃ γ₀ : Finset ℂ → ℝ, IsFractionalColoring V γ₀ ∧
      weight V γ₀ = χ_f (blowup R V) ∧
      (∀ Y ∈ V.powerset, ∀ Y' ∈ V.powerset, Congruent Y Y' →
        |marginal V γ₀ Y - marginal V γ₀ Y'| < δ) := by
  obtain ⟨T, hT⟩ := exists_congruence_realizer_finset V
  obtain ⟨R, hRne, hR⟩ := exists_folner_set T (show (0 : ℝ) < δ / (9 + 1) by positivity)
  have hσ : ∀ σ ∈ R, V.image (σ : ℂ → ℂ) ⊆ blowup R V := by
    intro σ hσR x hx
    rw [blowup, Finset.mem_biUnion]
    exact ⟨σ, hσR, hx⟩
  obtain ⟨γ, hγcol, hγwt⟩ := exists_optimal_coloring (blowup R V)
  refine ⟨R, avgColoring R (blowup R V) V γ, ?_, ?_, ?_⟩
  · exact isFractionalColoring_avgColoring _ _ V γ hRne hσ hγcol
  · rw [weight_avgColoring_eq _ _ V γ hRne]; exact hγwt
  · intro Y hY Y' hY' hcong
    obtain ⟨τ, hτT, hτeq⟩ := hT Y hY Y' hY' hcong
    subst hτeq
    have hdiff := avgColoring_marginal_diff_le R (blowup R V) V γ
      hγcol.nonneg τ (Finset.mem_powerset.mp hY) (Finset.mem_powerset.mp hY')
    rw [mul_div_assoc] at hdiff
    set r : ℝ := ((R \ R.image (· * τ)).card
      + (R.image (· * τ) \ R).card : ℝ) / R.card with hr
    have hrnn : 0 ≤ r := by rw [hr]; positivity
    have hwle : weight (blowup R V) γ ≤ 9 := hγwt ▸ chi_f_le_nine _
    have hwnn : 0 ≤ weight (blowup R V) γ := weight_nonneg hγcol
    have hkr : r * (9 + 1) < δ := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 9 + 1)).mp (hR τ hτT)
    have hbound : weight (blowup R V) γ * r < δ := by nlinarith [hrnn, hkr, hwle, hwnn]
    calc |marginal V (avgColoring R (blowup R V) V γ) Y
            - marginal V (avgColoring R (blowup R V) V γ) (Y.image (τ : ℂ → ℂ))|
        ≤ weight (blowup R V) γ * r := hdiff
      _ < δ := hbound

/-- **Averaging / first blow-up.** For every `ε > 0` there is a finite blow-up `V'` of `V` whose
fractional chromatic number is within `ε` of the geometric fractional chromatic number of `V`:
`χ_gf V ≤ χ_f V' + ε`. The averaging is over a Følner set of the plane isometry group, which exists
because `ℂ ≃ᵢ ℂ` is solvable, hence amenable (`exists_folner_set`) — no polynomial-growth hypothesis. -/
theorem exists_blowup_close (V : UnitDistanceGraph) {ε : ℝ} (hε : 0 < ε) :
    ∃ V' : UnitDistanceGraph, χ_gf V ≤ χ_f V' + ε := by
  obtain ⟨δ, hδ, hstab⟩ := weight_stability V hε
  obtain ⟨R, γ₀, hcol, hwt, hinv⟩ := exists_averaged_coloring V hδ
  refine ⟨blowup R V, ?_⟩
  have hlt : χ_gf V - ε < weight V γ₀ := hstab γ₀ hcol hinv
  rw [hwt] at hlt
  linarith

/-! ### The packaged statement used by `Main` -/

/-- **[M23] Theorem 1 (consequence used here).** For every `c < χ_gf V` there is a finite
unit-distance graph `V'` with `c < χ_f V'`. This is the form consumed in `Main`. -/
theorem exists_chi_f_gt (V : UnitDistanceGraph) {c : ℝ} (hc : c < χ_gf V) :
    ∃ V' : UnitDistanceGraph, c < χ_f V' := by
  obtain ⟨V', hV'⟩ := exists_blowup_close V (half_pos (sub_pos.mpr hc))
  exact ⟨V', by linarith⟩

end

end UnitDistanceGraphs
