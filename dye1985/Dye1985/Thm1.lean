/-!
# Dye (1985) Theorem 1 in Lean 4

This file presents definitions and  the theorem from Dye (1985) formalized in Lean 4.

```bash
lake lean Dye1985/Thm1.lean`
-/


import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option linter.unusedVariables false
set_option linter.style.emptyLine false

open Real
open Set
open scoped Real
open MeasureTheory

-- First, define the conditional expectation function
noncomputable def conditional_expectation (f : ℝ → ℝ) (x_val : ℝ) : ℝ :=
  if _ : ∫ t in (0)..x_val, f t = 0 then 0
  else (∫ t in (0)..x_val, t * f t) / (∫ t in (0)..x_val, f t)

-- Basic lemmas about conditional_expectation
lemma conditional_expectation_at_zero (f : ℝ → ℝ) :
    conditional_expectation f 0 = 0 := by
  unfold conditional_expectation
  simp

lemma conditional_expectation_at_x_bar (x_bar μ : ℝ) (f : ℝ → ℝ)
    (h_total_mass : ∫ x in (0)..x_bar, f x = 1)
    (h_mu_def : μ = ∫ x in (0)..x_bar, x * f x) :
    conditional_expectation f x_bar = μ := by
  unfold conditional_expectation
  have h_not_zero : ¬(∫ t in (0)..x_bar, f t = 0) := by
    intro h
    rw [h] at h_total_mass
    linarith
  rw [dif_neg h_not_zero, h_total_mass, div_one]
  exact h_mu_def.symm

-- Structure for the distribution assumptions
structure DistributionAssumptions (x_bar : ℝ) (f : ℝ → ℝ) where
  hx_bar_pos : 0 < x_bar
  pdf_nonneg : ∀ x, 0 ≤ f x
  pdf_continuous : ContinuousOn f (Set.Icc 0 x_bar)
  pdf_integrable : IntervalIntegrable f volume 0 x_bar
  pdf_total_mass_one : ∫ x in (0)..x_bar, f x = 1
  pdf_pos_on_support : ∀ x, 0 < x → x < x_bar → 0 < f x
  -- We assume the conditional expectation is continuous
  h_cont_conditional_expectation : ContinuousOn (conditional_expectation f) (Set.Icc 0 x_bar)

-- The unconditional expected value (μ) should equal the integral of x*f(x)
axiom mu_definition (μ : ℝ) (x_bar : ℝ) (f : ℝ → ℝ) : μ = ∫ x in (0)..x_bar, x * f x

-- The key equation from Theorem 1: pμ + (1-p)E[x̃|x̃ ∈ [0,x]] = x
def key_equation (p μ : ℝ) (f : ℝ → ℝ) (x_val : ℝ) : Prop :=
  p * μ + (1 - p) * conditional_expectation f x_val = x_val

-- Theorem 1: Existence of non-degenerate equilibrium
theorem equilibrium_exists (p μ x_bar : ℝ) (f : ℝ → ℝ)
    (dist_assump : DistributionAssumptions x_bar f)
    (hp : 0 < p) (hp_lt_one : p < 1)
    (hμ_pos : 0 < μ) (hμ_lt_x_bar : μ < x_bar)
    (mu_def : μ = ∫ x in (0)..x_bar, x * f x) :
    ∃ x, 0 < x ∧ x < x_bar ∧ key_equation p μ f x := by
  -- Unpack distribution assumptions
  have hx_bar_pos := dist_assump.hx_bar_pos
  have pdf_total_mass_one := dist_assump.pdf_total_mass_one
  have h_cont_conditional := dist_assump.h_cont_conditional_expectation

  -- Define the function g(x) = pμ + (1-p)E[x̃|x̃ ∈ [0,x]] - x
  let g : ℝ → ℝ := fun x => p * μ + (1 - p) * conditional_expectation f x - x

  -- Show g is continuous on [0, x_bar] using the assumed continuity
  have g_cont : ContinuousOn g (Set.Icc 0 x_bar) := by
    have h_const : ContinuousOn (fun _ : ℝ => p * μ) (Set.Icc 0 x_bar) :=
      continuous_const.continuousOn
    have h_cond_smul :
        ContinuousOn (fun x => (1 - p) * conditional_expectation f x) (Set.Icc 0 x_bar) :=
      ContinuousOn.const_smul h_cont_conditional (1 - p)
    have h_add :
        ContinuousOn (fun x => p * μ + (1 - p) * conditional_expectation f x)
        (Set.Icc 0 x_bar) :=
      h_const.add h_cond_smul
    have h_id : ContinuousOn (fun x : ℝ => x) (Set.Icc 0 x_bar) :=
      continuous_id.continuousOn
    exact h_add.sub h_id

  -- Evaluate g at endpoints
  have g0 : g 0 = p * μ := by
    simp [g, conditional_expectation_at_zero]

  have g0_pos : 0 < g 0 := by
    rw [g0]
    exact mul_pos hp hμ_pos

  have g_x_bar : g x_bar = μ - x_bar := by
    simp [g, conditional_expectation_at_x_bar x_bar μ f pdf_total_mass_one mu_def]
    ring

  have g_x_bar_neg : g x_bar < 0 := by
    rw [g_x_bar]
    linarith

  -- Apply Intermediate Value Theorem
  have h_ivt : ∃ x ∈ Set.Ioo (0 : ℝ) x_bar, g x = 0 := by
    have h4 : 0 ≤ x_bar := by linarith
    have hδ : 0 ∈ Set.Icc (g x_bar) (g 0) := ⟨by linarith, by linarith⟩
    rcases intermediate_value_Icc' h4 g_cont hδ with ⟨x, hx, hgx⟩
    rcases hx with ⟨hx_left, hx_right⟩
    have hx_left' : 0 < x := by
      by_contra! H  -- H: x ≤ 0
      have : x = 0 := by linarith
      rw [this] at hgx
      linarith
    have hx_right' : x < x_bar := by
      by_contra! H  -- H: x ≥ x_bar
      have : x = x_bar := by linarith
      rw [this] at hgx
      linarith
    exact ⟨x, ⟨hx_left', hx_right'⟩, hgx⟩

  rcases h_ivt with ⟨x, ⟨hx_left, hx_right⟩, hgx⟩
  refine ⟨x, hx_left, hx_right, ?_⟩
  unfold key_equation
  linarith

-- No complete disclosure equilibrium (x = 0)
theorem no_complete_disclosure (p μ : ℝ) (f : ℝ → ℝ)
    (hp : 0 < p) (hp_lt_one : p < 1) (hμ_pos : 0 < μ) :
    ¬ key_equation p μ f 0 := by
  intro h
  unfold key_equation at h
  rw [conditional_expectation_at_zero] at h
  have h_pos : p * μ > 0 := mul_pos hp hμ_pos
  linarith
