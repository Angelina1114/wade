/-
Chapter 2: Sequences in R
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
-- import Mathlib.Topology.Basic
-- import Mathlib.Topology.Order.Real
-- import Mathlib.Tactic

-- open Filter
-- open scoped Topology

namespace WadeAnalysis

-- A sequence of real numbers
def sequence : Type := ℕ → ℝ

-- Definition 2.1: convergence of a sequence
def converges_to (x: sequence) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |x n - a| < ε

-- Example 2.2: convergence of the sequence 1/n to 0
example: converges_to (fun n : ℕ => 1 / (n : ℝ) ) 0 := by -- n: ℕ : 數列的第 n 項
  unfold converges_to -- 把 converges_to 的定義展開
  intro ε hε -- 給定任意 ε > 0
  use (Nat.ceil (1 / ε) + 1 : ℕ) -- 選擇 N = ⌈1/ε⌉ + 1
  intro n hn -- 現在要證明：當 n ≥ N 時，有 |1/(n+1) - 0| < ε
  rw [sub_zero]
  have hn_pos : 0 < n := by
    have hN_pos : 0 < (Nat.ceil (1 / ε) + 1 : ℕ) :=
      Nat.succ_pos _
    exact lt_of_lt_of_le hN_pos hn
  have hn_pos' : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos
  have h_inv_pos : 0 < (n : ℝ)⁻¹ := by
    exact inv_pos.mpr hn_pos'
  have h_inv_pos' : 0 < (1 : ℝ) / n := by
    rw [← one_div] at h_inv_pos
    exact h_inv_pos
  have h_abs : |(1 : ℝ) / n| = (1 : ℝ) / n := abs_of_pos h_inv_pos'
  rw [h_abs]
  have hn_real : (n : ℝ) ≥ (Nat.ceil (1 / ε) + 1 : ℕ) := by
    exact_mod_cast hn
  have h_lt : (1 / ε) < (n : ℝ) := by
    have hceil : (1 / ε) ≤ (Nat.ceil (1 / ε) : ℝ) := by
      exact_mod_cast Nat.le_ceil (1 / ε)
    have hceil' : (1 / ε) < (Nat.ceil (1 / ε) : ℝ) + 1 := by
      linarith -- 1 / ε ≤ Nat.ceil (1 / ε) < Nat.ceil (1 / ε) + 1
    have hceil'' : (Nat.ceil (1 / ε) : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have h_lt' : (1 / ε) < (n : ℝ) := by
    exact_mod_cast h_lt
  have h_inv : (n : ℝ)⁻¹ < ε := by
    have ε_pos : 0 < ε := hε
    have : 0 < (ε : ℝ)⁻¹ := inv_pos.mpr ε_pos
    rw [← one_div] at this
    have := one_div_lt_one_div_of_lt this h_lt'
    rw [one_div] at this
    have h_one_div_inv : (1 / (1 / ε) : ℝ) = ε := by
      calc
        (1 / (1 / ε) : ℝ)
            = ((1 / ε : ℝ)⁻¹) := by rw [one_div]
        _   = ((ε : ℝ)⁻¹)⁻¹ := by rw [one_div]
        _   = (ε : ℝ) := inv_inv ε
    rw [h_one_div_inv] at this
    exact this
  rw [← one_div] at h_inv
  exact h_inv


-- Remark 2.3: A sequence can have at most one limit
theorem limit_unique(x : sequence) (a b : ℝ) (ha : converges_to x a) (hb : converges_to x b) : a = b := by
  have : a - b = 0 := by
    apply (abs_lt_forall_iff_eq_zero).mp
