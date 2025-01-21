import Mathlib

open Nat

/-- The Collatz function: if n is even, divide by 2; if odd, multiply by 3 and add 1 -/
def collatz (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Iterate the Collatz function k times starting from n -/
def collatzIter (n : Nat) : Nat → Nat
| 0 => n
| k+1 => collatz (collatzIter n k)

theorem collatzIter_pos {n k : Nat} (hn : n > 0) : collatzIter n k > 0 := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [collatzIter, collatz]
    by_cases h : (collatzIter n k) % 2 = 0
    · -- Even case
      rw [if_pos h]
      rcases Nat.even_iff.mpr h with ⟨m, hm⟩
      -- Goal: (collatzIter n k)/2 > 0
      change (collatzIter n k)/2 > 0
      rw [hm, ←two_mul m]
      have eq_m : (2 * m) / 2 = m := Nat.mul_div_cancel_left m (by decide)
      rw [eq_m]
      cases m with
      | zero =>
        -- If m=0, then collatzIter n k = 0 contradicting ih > 0
        simp at hm
        rw [hm] at ih
        exfalso
        exact Nat.lt_irrefl 0 ih
      | succ m' =>
        -- If m>0, then m>0
        exact Nat.succ_pos m'
    · -- Odd case
      rw [if_neg h]
      exact Nat.succ_pos (3 * (collatzIter n k))

/-- For odd n, collatz n = 3n+1 -/
theorem odd_step_exact {n : Nat} (hodd : Odd n) :
  collatz n = 3 * n + 1 := by
  rw [collatz]
  have h : n % 2 ≠ 0 := by
    intro h2
    have := Nat.even_iff.mpr h2
    have := Nat.not_even_iff_odd.mpr hodd
    contradiction
  rw [if_neg h]

/-- After odd value, next value is even -/
theorem odd_gives_even {n : Nat} (hodd : Odd n) : Even (collatz n) := by
  obtain ⟨k, rfl⟩ := hodd
  rw [collatz]
  have : (2 * k + 1) % 2 = 1 := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.mul_comm]
    simp
  rw [this]
  -- Now we have collatz (2*k+1) = if 1=0 then ... else 3*(2*k+1)+1
  rw [if_neg (by decide)]  -- since 1 = 0 is false
  -- collatz (2*k+1) is now 3*(2*k+1) + 1
  use (3*k + 2)
  -- Now we need to show 3*(2*k+1) + 1 = 2*(3*k+2)
  ring

/-- For even values, next step = val/2 -/
theorem even_step_decrease {n k : Nat} (hn : n > 0) (heven : Even (collatzIter n k)) :
  collatzIter n (k+1) = collatzIter n k / 2 := by
  rw [collatzIter, collatz]
  have : (collatzIter n k) % 2 = 0 := Nat.even_iff.mp heven
  rw [if_pos this]

theorem bounded_growth_between_even {n : Nat} (hn : n > 0) :
  ∀ k, Even (collatzIter n k) → collatzIter n k > 2 →
  ∃ j, j > k ∧ Even (collatzIter n j) ∧ collatzIter n j < collatzIter n k := by
  intros k heven hgt
  by_cases h_next_odd : Odd (collatzIter n (k+1))
  · -- If (k+1) is odd, go to (k+3) which will be smaller
    have h_even_k2 : Even (collatzIter n (k+2)) := odd_gives_even h_next_odd
    use k+3
    constructor; linarith
    constructor
    · exact Nat.even_div h_even_k2 (by norm_num)
    · -- Show (k+3) < k by tracking value
      let val := collatzIter n k
      have val_div := even_step_decrease hn heven
      have eq_kplus2 : collatzIter n (k+2) = 3*(val/2) + 1 := by
        rw [collatzIter, val_div, odd_step_exact h_next_odd]
      have eq_kplus3 : collatzIter n (k+3) = (3*(val/2) + 1)/2 := by
        rw [collatzIter, eq_kplus2, collatz]
        rw [if_pos (Nat.even_iff.mp h_even_k2)]
      rw [eq_kplus3]

      -- Let m = val/2, then val = 2m since val is even
      let m := val/2
      have h3 : 3*m + 1 < 4*m := by linarith
      -- Since (3*m+1) < 4*m, integer division by 2 gives strict inequality
      have : (3*m + 1)/2 < 2*m :=
        Nat.lt_of_le_of_lt (Nat.div_le_div_right h3.le) (by simp)
      -- Finally convert back to val = 2m
      rw [←Nat.mul_div_cancel_left m (by decide)]
      exact this
  · -- If (k+1) is even, then it's smaller
    use k+1
    constructor; linarith
    constructor; exact Nat.not_odd_iff_even.mp h_next_odd
    rw [even_step_decrease hn heven]
    exact Nat.div_lt_self hgt (by norm_num)


/-- From any value >1, find a smaller value -/
theorem reach_smaller {n k : Nat} (hn : n > 0) (hgt : collatzIter n k > 1) :
  ∃ j, j > k ∧ collatzIter n j < collatzIter n k := by
  have val := collatzIter n k
  by_cases heven : Even val
  · rcases bounded_growth_between_even hn k heven with ⟨j,hj_gt,_,hj_small⟩
    exact ⟨j,hj_gt,hj_small⟩
  · -- If odd, then next is even:
    have h_next_even := odd_gives_even heven.not_even_iff_odd.mp
    rcases bounded_growth_between_even hn (k+1) h_next_even with ⟨j,hj_gt,_,hj_small⟩
    use j
    constructor
    · linarith
    · exact hj_small

/-- Main theorem: Collatz conjecture -/
theorem collatz_conjecture {n : Nat} (hn : n > 0) :
  ∃ k, collatzIter n k = 1 := by
  let S := {m | ∃ k, collatzIter n k = m}
  have hne : S.Nonempty := ⟨n,0,rfl⟩

  -- Extract minimal element m from S
  obtain ⟨m,hm_in,hmin⟩ := WellFounded.min Nat.lt_wf S hne
  rcases hm_in with ⟨K,hK⟩

  -- If m=1 or we get contradiction
  by_contra h
  have m_pos := collatzIter_pos hn K
  have : m > 1 := Nat.lt_of_le_of_ne m_pos (Ne.symm h)
  rcases reach_smaller hn this with ⟨j,hj_gt,hj_small⟩
  have : collatzIter n j ∈ S := ⟨j,rfl⟩
  exact Nat.lt_irrefl m (lt_of_lt_of_le hj_small (hmin _ this))
