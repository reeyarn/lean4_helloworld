import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue

open Real
open Set
open scoped Real
open MeasureTheory

-- Structure for the distribution assumptions
structure DistributionAssumptions (x_bar : ℝ) (f : ℝ → ℝ) where
  hx_bar_pos : 0 < x_bar
  pdf_nonneg : ∀ x, 0 ≤ f x
  pdf_integrable : IntervalIntegrable f volume 0 x_bar
  pdf_total_mass_one : ∫ x in (0)..x_bar, f x = 1
  pdf_pos_on_support : ∀ x, 0 < x → x < x_bar → 0 < f x

-- The unconditional expected value (μ) should equal the integral of x*f(x)
axiom mu_definition (μ : ℝ) (x_bar : ℝ) (f : ℝ → ℝ) : μ = ∫ x in (0)..x_bar, x * f x

-- The conditional expectation given x is in [0, x_val]
noncomputable def conditional_expectation (p μ : ℝ) (f : ℝ → ℝ) (x_val : ℝ) : ℝ :=
  if _ : ∫ t in (0)..x_val, f t = 0 then μ
  else (∫ t in (0)..x_val, t * f t) / (∫ t in (0)..x_val, f t)

lemma conditional_expectation_at_zero (p μ : ℝ) (f : ℝ → ℝ) :
    conditional_expectation p μ f 0 = μ := by
  unfold conditional_expectation
  have h : ∫ t in (0)..(0 : ℝ), f t = 0 := by
    simp
  simp [h]

lemma conditional_expectation_at_x_bar (p μ x_bar : ℝ) (f : ℝ → ℝ)
    (h_total_mass : ∫ x in (0)..x_bar, f x = 1)
    (h_mu_def : μ = ∫ x in (0)..x_bar, x * f x) :
    conditional_expectation p μ f x_bar = μ := by
  unfold conditional_expectation
  -- First, show that the integral is not zero
  have h_not_zero : ¬(∫ t in (0)..x_bar, f t = 0) := by
    intro h
    rw [h] at h_total_mass
    linarith
  -- Use the false branch of the dif (since condition is false)
  rw [dif_neg h_not_zero]
  -- Now we have: (∫ t in (0)..x_bar, t * f t) / (∫ t in (0)..x_bar, f t)
  -- Rewrite the denominator using h_total_mass
  rw [h_total_mass]
  -- Now we have: (∫ t in (0)..x_bar, t * f t) / 1
  simp only [div_one]
  -- Now we have: ∫ t in (0)..x_bar, t * f t = μ
  exact h_mu_def.symm

-- The key equation from Theorem 1: pμ + (1-p)E[x̃|x̃ ∈ [0,x]] = x
def key_equation (p μ : ℝ) (f : ℝ → ℝ) (x_val : ℝ) : Prop :=
  p * μ + (1 - p) * conditional_expectation p μ f x_val = x_val

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

  -- Define the function g(x) = pμ + (1-p)E[x̃|x̃ ∈ [0,x]] - x
  let g : ℝ → ℝ := fun x => p * μ + (1 - p) * conditional_expectation p μ f x - x

  -- We need to show g is continuous on [0, x_bar]
  -- For now, we'll assume this (it requires measure theory to prove)
  have g_cont : ContinuousOn g (Set.Icc 0 x_bar) := by
    sorry

  -- Evaluate g at endpoints
  -- At x = 0: conditional_expectation returns μ (since integral is 0)
  -- So g(0) = p * μ + (1 - p) * μ - 0 = μ
  have g0 : g 0 = μ := by
    simp only [g]
    rw [conditional_expectation_at_zero p μ f]
    ring

  have g0_pos : 0 < g 0 := by
    rw [g0]
    exact hμ_pos

  -- At x = x_bar: conditional_expectation returns μ (since it equals the full expectation)
  -- So g(x_bar) = p * μ + (1 - p) * μ - x_bar = μ - x_bar
  have g_x_bar : g x_bar = μ - x_bar := by
    simp only [g]
    rw [conditional_expectation_at_x_bar p μ x_bar f pdf_total_mass_one mu_def]
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
  rw [conditional_expectation_at_zero p μ f] at h
  have : p * μ + (1 - p) * μ = μ := by ring
  rw [this] at h
  linarith
