/-
Main theorem (Theorem 1 of Dúcz–Varga (2026)):
there exists a finite unit-distance graph in the plane with independence ratio below `1/4`.

The proof combines the three components:
* `chi_gf_G29_gt`              — [DV26] Lemma 1:   `4 < χ_gf G₂₉`
* `exists_chi_f_gt`            — [M23]  Theorem 1: blow up to `V'` with `4 < χ_f V'`
* `exists_low_independence_ratio` — [M23] Theorem 2: blow up to `H` with ratio `< 1/4`
-/

import UnitDistanceGraphs.FirstBlowUp
import UnitDistanceGraphs.G29
import UnitDistanceGraphs.CertificateVerification
import UnitDistanceGraphs.SecondBlowUp

namespace UnitDistanceGraphs

/-- **Theorem 1 of Dúcz–Varga (2026).** There exists a nonempty finite unit-distance graph `H`
in the plane whose independence ratio `α(H)/|V(H)|` is strictly smaller than `1/4`, answering
the particular question of Erdős problem 1070 (is `f(n) ≥ n/4`?) in the negative.
(The nonemptiness conjunct rules out the vacuous witness `H = ∅`, whose independence ratio is
`0/0 = 0` under Lean's division convention.) -/
theorem exists_independenceRatio_lt_quarter :
    ∃ H : UnitDistanceGraph, H.Nonempty ∧ independenceRatio H < 1 / 4 := by
  obtain ⟨V', hV'⟩ := exists_chi_f_gt G29 chi_gf_G29_gt
  exact exists_low_independence_ratio V' hV'

end UnitDistanceGraphs
