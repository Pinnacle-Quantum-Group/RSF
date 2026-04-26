/-
  RSF — Density Convergence (Axiom 9)
  Pinnacle Quantum Group — April 2026

  Proves consequences of RSF Axiom 9: every well-defined recursive
  structure has a convergent fractal density function.
  Reference: RSF README §Additional Axiom, RSSN LEMMA_DERIVATIONS.md
-/
import Mathlib

noncomputable section
open Filter Topology

namespace RSF.DensityConvergence

/-! ## 1. Density Sequence -/

structure DensitySeq where
  val : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ val n
  bounded : ∀ n, val n ≤ 1

/-! ## 2. Monotone Density Converges -/

theorem monotone_decreasing_density_converges (d : DensitySeq)
    (hmono : Antitone d.val) :
    ∃ L : ℝ, Tendsto d.val atTop (nhds L) ∧ 0 ≤ L ∧ L ≤ 1 := by
  -- ℝ is ConditionallyCompleteLattice, not CompleteLattice — use the c-versions.
  have hbdd : BddBelow (Set.range d.val) := ⟨0, by rintro _ ⟨n, rfl⟩; exact d.nonneg n⟩
  refine ⟨iInf d.val, tendsto_atTop_ciInf hmono hbdd, ?_, ?_⟩
  · exact le_ciInf fun n => d.nonneg n
  · exact ciInf_le_of_le hbdd 0 (d.bounded 0)

theorem monotone_increasing_density_converges (d : DensitySeq)
    (hmono : Monotone d.val) :
    ∃ L : ℝ, Tendsto d.val atTop (nhds L) ∧ 0 ≤ L ∧ L ≤ 1 := by
  have hbdd : BddAbove (Set.range d.val) := ⟨1, by rintro _ ⟨n, rfl⟩; exact d.bounded n⟩
  refine ⟨iSup d.val, tendsto_atTop_ciSup hmono hbdd, ?_, ?_⟩
  · exact le_csSup_of_le hbdd ⟨0, rfl⟩ (d.nonneg 0)
  · exact ciSup_le fun n => d.bounded n

/-! ## 3. Cauchy Density Converges -/

theorem cauchy_density_converges (d : DensitySeq)
    (hcauchy : CauchySeq d.val) :
    ∃ L : ℝ, Tendsto d.val atTop (nhds L) :=
  -- ℝ is a CompleteSpace; CauchySeq directly converges
  cauchySeq_tendsto_of_complete hcauchy

/-! ## 4. Limit Inherits Bounds -/

theorem density_limit_nonneg (d : DensitySeq) (L : ℝ)
    (hL : Tendsto d.val atTop (nhds L)) : 0 ≤ L :=
  ge_of_tendsto hL (eventually_atTop.mpr ⟨0, fun n _ => d.nonneg n⟩)

theorem density_limit_le_one (d : DensitySeq) (L : ℝ)
    (hL : Tendsto d.val atTop (nhds L)) : L ≤ 1 :=
  le_of_tendsto hL (eventually_atTop.mpr ⟨0, fun n _ => d.bounded n⟩)

theorem density_limit_bounded (d : DensitySeq) (L : ℝ)
    (hL : Tendsto d.val atTop (nhds L)) : 0 ≤ L ∧ L ≤ 1 :=
  ⟨density_limit_nonneg d L hL, density_limit_le_one d L hL⟩

/-! ## 5. Density Substitution Preserves Convergence -/

theorem substitution_preserves_convergence (d : DensitySeq) (P : ℝ → ℝ)
    (hP : Continuous P) (L : ℝ) (hL : Tendsto d.val atTop (nhds L)) :
    Tendsto (P ∘ d.val) atTop (nhds (P L)) :=
  (hP.tendsto L).comp hL

/-! ## 6. Paired Density -/

def pairedDensity (d₁ d₂ : DensitySeq) (n : ℕ) : ℝ :=
  (d₁.val n + d₂.val n) / 2

theorem paired_density_bounded (d₁ d₂ : DensitySeq) (n : ℕ) :
    0 ≤ pairedDensity d₁ d₂ n ∧ pairedDensity d₁ d₂ n ≤ 1 := by
  unfold pairedDensity
  constructor
  · linarith [d₁.nonneg n, d₂.nonneg n]
  · linarith [d₁.bounded n, d₂.bounded n]

theorem paired_density_converges (d₁ d₂ : DensitySeq) (L₁ L₂ : ℝ)
    (hL₁ : Tendsto d₁.val atTop (nhds L₁))
    (hL₂ : Tendsto d₂.val atTop (nhds L₂)) :
    Tendsto (pairedDensity d₁ d₂) atTop (nhds ((L₁ + L₂) / 2)) := by
  unfold pairedDensity
  exact (hL₁.add hL₂).div_const 2

/-! ## 7. Constant Density -/

theorem constant_density_converges (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Tendsto (fun _ : ℕ => c) atTop (nhds c) :=
  tendsto_const_nhds

end RSF.DensityConvergence
