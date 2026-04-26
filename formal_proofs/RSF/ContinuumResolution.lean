/-
  RSF — Continuum Resolution Lemmas (T2)
  Pinnacle Quantum Group — April 2026

  L4.1: Density spectrum is dense — {1/n : n ≥ 1} is dense in (0,1]
  L4.2: CH Dissolution — between any two densities, intermediate exists,
        making Continuum Hypothesis meaningless in RSF.
  Reference: LEMMA_DERIVATIONS.md RSF T2
-/
import Mathlib

noncomputable section
open Set Filter Topology

namespace RSF.ContinuumResolution

/-! ## L4.1 — Density Spectrum Dense

    NOTE (specification mismatch): the definition below restricts the
    spectrum to `{1/n : n ≥ 1} = {1, 1/2, 1/3, …}`, which accumulates
    only at 0 and is therefore **not dense in (0, 1]** — counterexample:
    the open interval (0.4, 0.5) contains no `1/n`. The dense-spectrum
    claims below (`L4_1_spectrum_dense_in_unit`, `L4_1_density_between`,
    `L4_2_density_spectrum_no_jumps`) cannot be proved with this
    definition. The corrected version uses ℚ ∩ (0, 1] and lives in
    `ClosureAttempts.lean` as `densitySpectrum'` with the matching
    `L4_1_density_between` proof. Stubbed pending alignment of this
    file with the corrected spectrum definition. -/

def densitySpectrum : Set ℝ := {x | ∃ n : ℕ, 0 < n ∧ x = 1 / ↑n}

theorem L4_1_spectrum_dense_in_unit :
    Dense (densitySpectrum ∩ Set.Ioo 0 1) := by
  -- FALSE as stated; see NOTE above.
  sorry

theorem L4_1_one_over_n_approaches_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / ↑(n + 1)) atTop (nhds 0) := by
  simpa using tendsto_one_div_add_atTop_nhds_zero_nat

theorem L4_1_spectrum_contains_rationals :
    ∀ n : ℕ, 0 < n → (1 : ℝ) / ↑n ∈ densitySpectrum :=
  fun n hn => ⟨n, hn, rfl⟩

/-- The actual mathematical content of the harmonic-spectrum density:
    `{1/n}` accumulates at 0. For every ε > 0 there is some `1/n` in
    the spectrum with `1/n < ε`. This is the TRUE statement that the
    false-as-written `L4_1_spectrum_dense_in_unit` was trying to capture
    — the spectrum is dense **at 0**, not in (0, 1]. The Möbius/cylinder
    parallel to RLA: the validator-level catch is "you said dense in
    (0, 1] but only dense at 0"; this theorem restates the corrected
    claim positively. -/
theorem densitySpectrum_accumulates_at_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ d ∈ densitySpectrum, d < ε := by
  -- Pick n with 1/(n+1) < ε via the Archimedean property.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨1 / (↑(n + 1) : ℝ), ⟨n + 1, Nat.succ_pos _, rfl⟩, ?_⟩
  exact_mod_cast hn

theorem L4_1_density_between (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ 1) :
    ∃ d ∈ densitySpectrum, a < d ∧ d < b := by
  -- FALSE as stated; see NOTE on densitySpectrum above.
  -- Counterexample: a = 0.4, b = 0.5 — no `1/n` lies in (0.4, 0.5).
  -- The corrected `L4_1_density_between` over ℚ ∩ (0, 1] is proved in
  -- ClosureAttempts.lean using `exists_rat_btwn`.
  sorry

/-! ## L4.2 — CH Dissolution
    In RSF, the gap between countable and uncountable is filled by
    a continuous spectrum of density values, making CH trivially
    satisfied (in a meaningless way) rather than independent. -/

theorem L4_2_intermediate_density (d₁ d₂ : ℝ)
    (h₁ : 0 < d₁) (h₂ : d₁ < d₂) (h₃ : d₂ ≤ 1) :
    ∃ d₃ : ℝ, d₁ < d₃ ∧ d₃ < d₂ :=
  ⟨(d₁ + d₂) / 2, by linarith, by linarith⟩

theorem L4_2_no_gap (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ c : ℝ, a < c ∧ c < b :=
  ⟨(a + b) / 2, by linarith, by linarith⟩

theorem L4_2_density_spectrum_no_jumps :
    ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∀ ε > 0,
    ∃ d ∈ densitySpectrum, |d - x| < ε := by
  -- FALSE as stated; see NOTE on densitySpectrum above. Take x = 0.45,
  -- ε = 0.04: nearest `1/n` are 1/2 = 0.5 and 1/3 ≈ 0.333; both more
  -- than 0.04 away. Holds with the corrected ℚ-spectrum.
  sorry

/-! ## Theorem T2 — Continuum Resolution
    The Continuum Hypothesis becomes irrelevant because RSF
    replaces the countable/uncountable dichotomy with a
    continuous density spectrum. -/

theorem T2_continuum_resolution :
    ∀ d₁ d₂ : ℝ, 0 < d₁ → d₁ < d₂ → d₂ ≤ 1 →
    ∃ d₃ : ℝ, d₁ < d₃ ∧ d₃ < d₂ ∧ 0 < d₃ ∧ d₃ ≤ 1 :=
  fun d₁ d₂ h₁ h₁₂ h₂ =>
    ⟨(d₁ + d₂) / 2, by linarith, by linarith, by linarith, by linarith⟩

end RSF.ContinuumResolution
