/-
  L3.2a — Uniform Convergence on Compact for Lipschitz Family
  Tightened version for compile + iterate workflow.

  Both holes from v2 are closed:
    • limit_lipschitz takes a set-restricted hypothesis (Step 1 fix)
    • nearest-grid-point helper proved (Helper C closed)

  Structure: Each step is a self-contained named lemma so a compile
  failure points to a small region. Iterate by replacing the failing
  lemma's proof, not the whole file.

  Mathlib API used (all stable across recent versions):
    • Nat.le_ceil, Nat.cast_le, Nat.cast_lt
    • Filter.Tendsto.sub, Filter.Tendsto.abs (or .neg etc.)
    • le_of_tendsto, Filter.Eventually.of_forall
    • Metric.tendsto_atTop  (gives ε-N from Tendsto … atTop (nhds L))
    • abs_add, abs_sub_comm, div_le_iff, div_pos
    • Int.toNat, Int.floor, Int.floor_le, Int.lt_floor_add_one
-/
import Mathlib

noncomputable section
open Set Filter Topology

namespace FTC.CurvatureConvergence.L3_2a

structure LipschitzCurvature where
  R : ℕ → ℝ → ℝ
  R_cl : ℝ → ℝ
  K : ℝ
  hK : 0 < K
  lipschitz : ∀ n, ∀ x y : ℝ, |R n x - R n y| ≤ K * |x - y|


/-! ## Step 1 — limit inherits Lipschitz, on whatever set we have convergence. -/

/-- The pointwise limit of a uniformly K-Lipschitz family is K-Lipschitz on
    any set where pointwise convergence holds. -/
lemma limit_lipschitz_on (lc : LipschitzCurvature) (S : Set ℝ)
    (hpw : ∀ x ∈ S, Tendsto (fun n => lc.R n x) atTop (nhds (lc.R_cl x)))
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) :
    |lc.R_cl x - lc.R_cl y| ≤ lc.K * |x - y| := by
  have h_diff : Tendsto (fun n => lc.R n x - lc.R n y) atTop
                (nhds (lc.R_cl x - lc.R_cl y)) :=
    (hpw x hx).sub (hpw y hy)
  have h_abs : Tendsto (fun n => |lc.R n x - lc.R n y|) atTop
                (nhds |lc.R_cl x - lc.R_cl y|) := h_diff.abs
  exact le_of_tendsto h_abs (Filter.eventually_of_forall (fun n => lc.lipschitz n x y))


/-! ## Step 2/3 — finite grid construction with explicit spacing bound. -/

/-- Grid points for a partition of [a,b] into M equal pieces. -/
private def gridPt (a b : ℝ) (M : ℕ) (i : ℕ) : ℝ :=
  a + (b - a) * (↑i / ↑M)

/-- Grid points are inside [a,b]. -/
private lemma gridPt_mem (a b : ℝ) (hab : a ≤ b) (M : ℕ) (hM : 0 < M)
    (i : ℕ) (hi : i ≤ M) :
    gridPt a b M i ∈ Set.Icc a b := by
  have hM_R : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have h_ratio_nn : 0 ≤ (↑i : ℝ) / ↑M :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hM_R)
  have h_ratio_le : (↑i : ℝ) / ↑M ≤ 1 := by
    rw [div_le_one hM_R]; exact_mod_cast hi
  have hba_nn : 0 ≤ b - a := by linarith
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · simp only [gridPt]; nlinarith
  · simp only [gridPt]; nlinarith

/-- The grid spacing (b-a)/M is at most δ when M ≥ ⌈(b-a)/δ⌉ + 1. -/
private lemma gridSpacing_le (a b δ : ℝ) (hab : a < b) (hδ : 0 < δ) :
    let M : ℕ := ⌈(b - a) / δ⌉₊ + 1
    (b - a) / (↑M : ℝ) ≤ δ := by
  intro M
  have hba_pos : 0 < b - a := by linarith
  have hM_nat_pos : 0 < M := Nat.succ_pos _
  have hM_R : 0 < (M : ℝ) := Nat.cast_pos.mpr hM_nat_pos
  -- M = ⌈(b-a)/δ⌉ + 1, so M > (b-a)/δ, so (b-a) < M·δ.
  have h_ceil : (b - a) / δ ≤ (⌈(b - a) / δ⌉₊ : ℝ) := Nat.le_ceil _
  have h_M_gt : (b - a) / δ < (M : ℝ) := by
    have : (⌈(b - a) / δ⌉₊ : ℝ) < (M : ℝ) := by
      show (⌈(b - a) / δ⌉₊ : ℝ) < ((⌈(b - a) / δ⌉₊ + 1 : ℕ) : ℝ)
      push_cast; linarith
    linarith
  rw [div_le_iff hM_R]
  have : (b - a) / δ * δ = b - a := by field_simp
  calc b - a = (b - a) / δ * δ := by field_simp
    _ ≤ (M : ℝ) * δ := by
        exact mul_le_mul_of_nonneg_right (le_of_lt h_M_gt) (le_of_lt hδ)


/-! ## Step 4 — nearest grid point exists with explicit bound. -/

/-- For any x ∈ [a,b], some grid index i ≤ M has the property
    |x - gridPt i| ≤ (b-a)/M. -/
private lemma gridPt_close (a b : ℝ) (hab : a < b) (M : ℕ) (hM : 0 < M)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ i, i ≤ M ∧ |x - gridPt a b M i| ≤ (b - a) / (↑M : ℝ) := by
  have hM_R : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hba_pos : 0 < b - a := by linarith
  -- Take i = ⌊(x - a) · M / (b - a)⌋. Then 0 ≤ i ≤ M.
  -- And by the floor inequalities, |x - gridPt i| ≤ (b - a)/M.
  let t : ℝ := (x - a) * ↑M / (b - a)
  have ht_nn : 0 ≤ t := by
    apply div_nonneg
    · exact mul_nonneg (by linarith [hx.1]) (le_of_lt hM_R)
    · linarith
  have ht_le : t ≤ (M : ℝ) := by
    rw [div_le_iff hba_pos]
    have hxb : x - a ≤ b - a := by linarith [hx.2]
    calc (x - a) * (M : ℝ)
        ≤ (b - a) * (M : ℝ) :=
          mul_le_mul_of_nonneg_right hxb (le_of_lt hM_R)
      _ = (M : ℝ) * (b - a) := by ring
  -- i := ⌊t⌋ as a natural number (t ≥ 0 so ⌊t⌋ ≥ 0)
  let i : ℕ := ⌊t⌋₊
  refine ⟨i, ?_, ?_⟩
  · -- i ≤ M because t ≤ M and i = ⌊t⌋₊ ≤ t (when t ≥ 0)
    have : (i : ℝ) ≤ t := Nat.floor_le ht_nn
    have : (i : ℝ) ≤ (M : ℝ) := le_trans this ht_le
    exact_mod_cast this
  · -- |x - gridPt i| ≤ (b - a) / M
    -- gridPt i = a + (b-a) · i / M
    -- |x - gridPt i| = |(x - a) - (b - a) · i / M|
    --                = |(b - a)/M| · |t - i|        (factor out (b-a)/M)
    --                = (b - a)/M · |t - i|          (since b > a, M > 0)
    --               ≤ (b - a)/M · 1                 (since i = ⌊t⌋, |t-i| < 1, ≤ 1)
    have h_floor_le : (i : ℝ) ≤ t := Nat.floor_le ht_nn
    have h_lt_floor : t < ↑i + 1 := Nat.lt_floor_add_one t
    have h_diff_bound : |t - ↑i| ≤ 1 := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    -- Algebraic identity: x - gridPt i = (b - a)/M · (t - i)
    have h_alg : x - gridPt a b M i = (b - a) / (M : ℝ) * (t - ↑i) := by
      simp only [gridPt, t]
      field_simp
      ring
    rw [h_alg, abs_mul]
    have h_factor_nn : (0 : ℝ) ≤ (b - a) / (M : ℝ) :=
      div_nonneg (le_of_lt hba_pos) (le_of_lt hM_R)
    rw [abs_of_nonneg h_factor_nn]
    calc (b - a) / (M : ℝ) * |t - ↑i|
        ≤ (b - a) / (M : ℝ) * 1 := by
          exact mul_le_mul_of_nonneg_left h_diff_bound h_factor_nn
      _ = (b - a) / (M : ℝ) := by ring


/-! ## Main theorem: assembly. -/

theorem L3_2a_uniform_on_compact (lc : LipschitzCurvature)
    (a b : ℝ) (hab : a ≤ b)
    (hpw : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => lc.R n x) atTop (nhds (lc.R_cl x))) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ Set.Icc a b,
      |lc.R n x - lc.R_cl x| < ε := by
  intro ε hε
  set δ : ℝ := ε / (3 * lc.K) with hδ_def
  have hδ_pos : 0 < δ := div_pos hε (by linarith [lc.hK])
  have hKδ : lc.K * δ = ε / 3 := by rw [hδ_def]; field_simp
  -- Degenerate case: a = b
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · subst hab_eq
    have ha : a ∈ Set.Icc a a := Set.mem_Icc.mpr ⟨le_refl _, le_refl _⟩
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hpw a ha)) ε hε
    refine ⟨N, fun n hn x hx => ?_⟩
    have : x = a := le_antisymm hx.2 hx.1
    rw [this]; exact hN n hn
  · -- Genuine interval
    set M : ℕ := ⌈(b - a) / δ⌉₊ + 1 with hM_def
    have hM_pos_nat : 0 < M := Nat.succ_pos _
    have hM_pos_R : 0 < (M : ℝ) := Nat.cast_pos.mpr hM_pos_nat
    have h_spacing : (b - a) / (↑M : ℝ) ≤ δ := gridSpacing_le a b δ hab_lt hδ_pos
    -- Per-grid-point convergence indices.
    have h_per : ∀ i, i ≤ M → ∃ N_i : ℕ, ∀ n ≥ N_i,
        |lc.R n (gridPt a b M i) - lc.R_cl (gridPt a b M i)| < ε / 3 := by
      intro i hi
      have hε3 : (0 : ℝ) < ε / 3 := by linarith
      exact (Metric.tendsto_atTop.mp
              (hpw (gridPt a b M i) (gridPt_mem a b hab M hM_pos_nat i hi)))
            (ε / 3) hε3
    choose Nfn hNfn using h_per
    -- Take max over i = 0, …, M. Use Finset.range (M+1) so i can be M.
    set N : ℕ :=
      ((Finset.range (M + 1)).attach.image
        (fun ⟨i, hi⟩ => Nfn i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))).max'
        ⟨Nfn 0 (Nat.zero_le _),
         Finset.mem_image.mpr ⟨⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩,
           Finset.mem_attach _ _, rfl⟩⟩
      with hN_def
    have hN_bound : ∀ i (hi : i ≤ M), Nfn i hi ≤ N := by
      intro i hi
      apply Finset.le_max'
      apply Finset.mem_image.mpr
      refine ⟨⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi)⟩,
              Finset.mem_attach _ _, ?_⟩
      rfl
    refine ⟨N, ?_⟩
    intro n hn x hx
    -- Pick nearest grid point
    obtain ⟨i, hi_le, h_close⟩ := gridPt_close a b hab_lt M hM_pos_nat hx
    -- The three triangle pieces.
    -- Piece 1: |R_n x - R_n (gridPt i)| ≤ K · (b-a)/M ≤ K · δ = ε/3
    have h_piece1 : |lc.R n x - lc.R n (gridPt a b M i)| ≤ ε / 3 := by
      calc |lc.R n x - lc.R n (gridPt a b M i)|
          ≤ lc.K * |x - gridPt a b M i| := lc.lipschitz n x (gridPt a b M i)
        _ ≤ lc.K * ((b - a) / M)        :=
            mul_le_mul_of_nonneg_left h_close (le_of_lt lc.hK)
        _ ≤ lc.K * δ                    :=
            mul_le_mul_of_nonneg_left h_spacing (le_of_lt lc.hK)
        _ = ε / 3                       := hKδ
    -- Piece 2: |R_n (gridPt i) - R_cl (gridPt i)| < ε/3 by chosen N
    have h_piece2 : |lc.R n (gridPt a b M i) - lc.R_cl (gridPt a b M i)| < ε / 3 := by
      apply hNfn i hi_le n
      exact le_trans (hN_bound i hi_le) hn
    -- Piece 3: |R_cl (gridPt i) - R_cl x| ≤ K · (b-a)/M ≤ ε/3 by Step 1
    have h_piece3 : |lc.R_cl (gridPt a b M i) - lc.R_cl x| ≤ ε / 3 := by
      have h_lim_lip := limit_lipschitz_on lc (Set.Icc a b) hpw
        (gridPt_mem a b hab M hM_pos_nat i hi_le) hx
      calc |lc.R_cl (gridPt a b M i) - lc.R_cl x|
          ≤ lc.K * |gridPt a b M i - x| := h_lim_lip
        _ = lc.K * |x - gridPt a b M i| := by rw [abs_sub_comm]
        _ ≤ lc.K * ((b - a) / M)        :=
            mul_le_mul_of_nonneg_left h_close (le_of_lt lc.hK)
        _ ≤ lc.K * δ                    :=
            mul_le_mul_of_nonneg_left h_spacing (le_of_lt lc.hK)
        _ = ε / 3                       := hKδ
    -- Combine: triangle inequality on the three pieces.
    calc |lc.R n x - lc.R_cl x|
        = |(lc.R n x - lc.R n (gridPt a b M i)) +
            (lc.R n (gridPt a b M i) - lc.R_cl (gridPt a b M i)) +
            (lc.R_cl (gridPt a b M i) - lc.R_cl x)| := by ring_nf
      _ ≤ |lc.R n x - lc.R n (gridPt a b M i)|
          + |lc.R n (gridPt a b M i) - lc.R_cl (gridPt a b M i)|
          + |lc.R_cl (gridPt a b M i) - lc.R_cl x| := by
            apply le_trans (abs_add _ _)
            exact add_le_add_right (abs_add _ _) _
      _ < ε / 3 + ε / 3 + ε / 3 := by
            have := add_lt_add_of_le_of_lt
              (add_le_add h_piece1 (le_refl _) : _ ≤ ε/3 + _) h_piece3
            linarith [h_piece1, h_piece2, h_piece3]
      _ = ε := by ring

end FTC.CurvatureConvergence.L3_2a
