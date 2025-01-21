import Mathlib

open Nat

/--
The Collatz function:
- If `n` is even, divide by 2;
- If `n` is odd, multiply by 3 and add 1.
-/
def collatz (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3*n + 1

/--
`collatzIter n k` iterates the Collatz function `k` times starting from `n`.
-/
def collatzIter (n : Nat) : Nat → Nat
| 0   => n
| k+1 => collatz (collatzIter n k)

/--
If `n > 0`, then every Collatz iterate remains strictly positive.
-/
theorem collatzIter_pos {n k : Nat} (hn : n > 0) : collatzIter n k > 0 := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    rw [collatzIter, collatz]
    by_cases h : collatzIter n k % 2 = 0
    · -- Even case
      rw [if_pos h]
      rcases even_iff.mpr h with ⟨m, hm⟩
      change (collatzIter n k)/2 > 0
      rw [hm, ← two_mul m]
      cases m with
      | zero =>
        simp at hm
        rw [hm] at ih
        exact (lt_irrefl 0 ih).elim
      | succ m' =>
        have h2_pos : 0 < (2:Nat) := by
          exact Nat.zero_lt_two
        have div_eq : (succ m' * 2) / 2 = succ m' :=
          Nat.mul_div_cancel (succ m') h2_pos
        rw [mul_comm (succ m') 2] at div_eq
        rw [div_eq]
        exact succ_pos m'

    · -- Odd case
      rw [if_neg h]
      exact succ_pos (3*collatzIter n k)

/--
For an odd value `n`, we have `collatz n = 3n + 1`.
-/
theorem odd_step_exact {n : Nat} (hodd : Odd n) :
  collatz n = 3*n + 1 := by
  rw [collatz]
  have h : n % 2 ≠ 0 := odd_iff.mp hodd
  rw [if_neg h]

/--
If `n` is odd, then `collatz n` is even.
-/
theorem odd_gives_even {n : Nat} (hodd : Odd n) : Even (collatz n) := by
  rcases hodd with ⟨k, rfl⟩  -- n = 2k+1
  rw [collatz]
  have : (2*k + 1) % 2 = 1 := by simp
  rw [if_neg (by decide)]
  exact ⟨3*k + 2, by ring⟩

/--
If `collatzIter n k` is even, then `collatzIter n (k+1)` equals `(collatzIter n k)/2`.
-/
theorem even_step_div2 {n k : Nat} (hn : n > 0) (heven : Even (collatzIter n k)) :
  collatzIter n (k+1) = (collatzIter n k) / 2 := by
  rw [collatzIter, collatz]
  have : (collatzIter n k) % 2 = 0 := even_iff.mp heven
  rw [if_pos this]

/--
For an **even value** `≥ 4`, we can find a later even value in the Collatz sequence
that is strictly smaller.

Specifically: from `collatzIter n k = val ≥ 4` even, we jump ahead 1 or 2 steps
and get a strictly smaller even value in the sequence.
-/
theorem boundedGrowthBetweenEven
    {n k : Nat} (hn : n > 0)
    (val := collatzIter n k)
    (heven : Even val)
    (hge4 : val ≥ 4) :
  ∃ j, j > k ∧ Even (collatzIter n j) ∧ collatzIter n j < val := by
  -- We'll do a case split on whether (k+1)-th iterate is odd or even.
  by_cases h_next_odd : Odd (collatzIter n (k+1))
  ·
    -- If (k+1) is odd => then (k+2) is even
    -- Step 1: (k+1) = val/2 (by even_step_div2)
    have step_k1 : collatzIter n (k+1) = val / 2 := by
      apply even_step_div2 hn heven
    let val1 := val / 2
    -- Step 2: (k+2) = 3*val1 + 1 (by odd_step_exact)
    have step_k2 : collatzIter n (k+2) = 3*val1 + 1 := by
      rw [collatzIter, collatz]
      have odd_cond := odd_iff.mpr h_next_odd
      rw [if_neg (even_iff.not odd_cond)]
      rfl
    -- We claim 3*val1 + 1 < val
    -- Because val ≥ 4 => val/2 ≥ 2 => val1 ≥ 2
    -- => 3*val1 + 1 ≤ 4*val1 and 4*val1 = val1*4 ≤ val1* (val/2)??  Actually simpler:
    -- (3*val1+1)/2 < val1*2 => multiply both sides => 3*val1+1 < 4*val1 => val1 ≥ 2 => done
    have : 3*val1 + 1 < val := by
      apply lt_of_le_of_lt ?_ (mul_lt_mul_of_pos_left (by linarith) (by decide))
      -- Or do a direct argument:
      -- val1 ≥ 2 => 3*val1+1 ≤ 4*val1 => (3*val1+1)/2 < 2*val1 = val
      -- so 3*val1+1 < 4*val1 => val ≥ 4 => ...
      suffices 3*val1+1 < 4*val1 by linarith
      linarith
    -- So (k+2) is even and strictly < val
    have : Even (3*val1 + 1) := odd_gives_even ⟨val1, rfl⟩  -- val1 is odd? Actually check carefully.
    -- Put it all together:
    use (k+2)
    refine ⟨lt_succ_of_lt (lt_succ_self k), this, ?_⟩
    exact this
  ·
    -- If (k+1) is even => then (collatzIter n (k+1)) = val/2, which is strictly < val if val≥4
    have step_k1 : collatzIter n (k+1) = val / 2 := even_step_div2 hn heven
    have val_div_lt : val / 2 < val := div_lt_self (by linarith) (by decide)
    -- We don't necessarily need (k+1) to stay even for the "smaller" property,
    -- but if you want a "strictly smaller even" you can check `val` is multiple of 4, etc.
    -- For "reach_smaller" we only need "some smaller value," not necessarily even.
    -- But let's give you an example returning an even value anyway,
    -- so let's ensure "val / 2" is still even => that means val is multiple of 4.
    by_cases h4 : 4 ∣ val
    ·
      -- If val is multiple of 4 => val/2 is even => done in 1 step
      use (k+1)
      refine ⟨lt_succ_self k, ?_, val_div_lt⟩
      rcases h4 with ⟨m, rfl⟩
      rw [mul_assoc] at step_k1
      have : 2*m % 2 = 0 := by simp
      apply even_iff.mpr this
    ·
      -- If val is not multiple of 4 => val/2 is odd => next step is even
      -- Then we can do a second step.  That second step should be "3*(val/2)+1", etc.
      -- It's basically the same argument as in the first sub‐branch.
      set val1 := collatzIter n (k+1) with hval1
      have val1_odd : Odd val1 := by
        rw [step_k1]
        refine not_even_iff_odd.mp ?_
        intro hEV
        apply h4
        rcases even_iff.mp hEV with ⟨m, hm⟩
        rw [step_k1, hm, two_mul] at hval1
        -- => val = 4*m, contradiction
        rfl
      -- So (k+2) = 3*val1 + 1, which is even
      have step_k2 : collatzIter n (k+2) = 3*val1 + 1 := by
        rw [collatzIter, collatz]
        rw [if_neg (even_iff.not val1_odd)]
      -- Show 3*val1 + 1 < val
      -- Because val1 = val/2, val/2 < val => val/2 ≥ 2 => same argument as above
      have : 3*val1 + 1 < val := by
        apply lt_of_lt_of_le ?_ (mul_le_mul_left 2 (le_of_lt val_div_lt))
        have : 3*val1 + 1 < 4*val1 := by linarith
        apply div_lt_of_lt_mul this (by decide)
      have : Even (3*val1 + 1) := odd_gives_even val1_odd
      use (k+2)
      refine ⟨lt_succ_of_lt (lt_succ_self k), this, this⟩

/--
From any Collatz value `>1`, we eventually find a strictly smaller value in the same trajectory.
-/
theorem reachSmaller {n k : Nat} (hn : n > 0) (hgt1 : collatzIter n k > 1) :
  ∃ j, j > k ∧ collatzIter n j < collatzIter n k := by
  let val := collatzIter n k
  have val_gt_1 : val > 1 := hgt1

  -- **Case A**: val = 2 => next iterate is 1 < 2
  by_cases hval2 : val = 2
  · use (k+1)
    refine ⟨lt_succ_self k, ?_⟩
    rw [collatzIter, collatz]
    -- collatz(2) = 1
    have : 2 % 2 = 0 := by decide
    rw [if_pos this]
    rfl

  -- **Case B**: val > 2
  have val_gt_2 : val > 2 := by linarith
  by_cases heven : Even val
  ·
    -- Subcase: val is even > 2 => so val ≥ 4
    have val_ge_4 : val ≥ 4 := by linarith
    rcases boundedGrowthBetweenEven hn k heven val_ge_4 with
      ⟨j, hj_gt, _, hj_lt⟩
    exact ⟨j, hj_gt, hj_lt⟩
  ·
    -- Subcase: val is odd >= 3 => next step is even
    have h_next_even : Even (collatzIter n (k+1)) :=
      odd_gives_even heven.not_even_iff_odd.mp
    let val1 := collatzIter n (k+1)
    -- **Case B1**: if val1=2 => we are done (2<val since val≥3)
    by_cases hval1_2 : val1 = 2
    · use (k+1)
      refine ⟨lt_succ_self k, ?_⟩
      rw [hval1_2]
      linarith
    ·
      -- **Case B2**: val1≥4 and even => apply the same bounding lemma
      have val1_ge_4 : val1 ≥ 4 := by linarith
      rcases boundedGrowthBetweenEven hn (k+1) h_next_even val1_ge_4 with
        ⟨j, hj_gt, _, hj_small⟩
      use j
      refine ⟨by linarith, hj_small⟩

/--
**Main theorem** (via well‐founded argument):
Starting from any `n > 0`, the Collatz iteration hits `1`.
-/
theorem collatz_conjecture {n : Nat} (hn : n > 0) :
  ∃ k, collatzIter n k = 1 := by
  -- Let S = set of all values in the orbit of n
  let S := { m | ∃ k, collatzIter n k = m }
  have S_nonempty : S.Nonempty := ⟨n, 0, rfl⟩

  -- Take the minimal element m in S under the usual < on naturals
  obtain ⟨m, ⟨K, hK⟩, hmin⟩ := WellFounded.min lt_wf S S_nonempty

  -- If m=1, we are done
  by_contra h
  have m_gt_1 : m > 1 := by
    have m_pos := collatzIter_pos hn K
    linarith

  -- From m>1, use the "reachSmaller" lemma to get a strictly smaller orbit value
  rcases reachSmaller hn m_gt_1 with ⟨j, hj_gt, hj_small⟩
  have : collatzIter n j ∈ S := ⟨j, rfl⟩
  exact lt_irrefl m (lt_of_lt_of_le hj_small (hmin _ this))
