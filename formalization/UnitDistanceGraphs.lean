/-
Lean 4 formalization of Theorem 1 of Dúcz–Varga (2026) — a finite unit-distance graph in the
plane with independence ratio below 1/4 — answering a question of Erdős (problem #1070) in the
negative. This root module is the build manifest: `lake build` checks exactly
the modules imported (transitively) here, and `import UnitDistanceGraphs` gives
downstream users the whole development.
-/

-- Foundations: core definitions, χ_gf lower-bound API, independent-set enumeration
import UnitDistanceGraphs.Definitions

-- Component 1 ([M23] Thm 1): the first blow-up, via amenability
import UnitDistanceGraphs.PlaneColoring
import UnitDistanceGraphs.Folner
import UnitDistanceGraphs.FirstBlowUp

-- Component 2 ([DV26] Lemma 1): the certified graph G₂₉ and the LP certificate
import UnitDistanceGraphs.G29
import UnitDistanceGraphs.G29Vertices
import UnitDistanceGraphs.PlaneIsometry
import UnitDistanceGraphs.CertificateData
import UnitDistanceGraphs.CertificateVerification

-- Component 3 ([M23] Thm 2): the second blow-up
import UnitDistanceGraphs.SecondBlowUp

-- Theorem 1 of [DV26]
import UnitDistanceGraphs.Main
