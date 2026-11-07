module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic.FinCases
public import Lean.Elab.Tactic.Omega

/-!
# Small units and the eight repeated-family denominators

This proves PDF Lemma 4.1. For n≥4, the interval 1<k<n/3 contains no unit
modulo 2n exactly when n is one of 4,5,6,7,8,9,12,15.

The unbounded part is constructive. If n>15 and 3 does not divide n, use
k=3. Otherwise write n=3t. A shift t−d, chosen from d=1,2,3,4 according
to t modulo 6, is odd, avoids divisibility by 3, and is coprime to t.
Only the remaining bounded statements use kernel decision procedures.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- The denominator set S in PDF Theorem 1.1 and Lemma 4.1. -/
def repeatedDenominators : Finset ℕ := {4, 5, 6, 7, 8, 9, 12, 15}

/-- If a shift is coprime to 2 and 3, and the removed amount is coprime
to t, it is coprime to 6t. The last assertion uses gcd(t−d,t)=gcd(d,t). -/
theorem shifted_index_coprime (t d : ℕ) (hd : d ≤ t)
    (h2 : ¬2 ∣ t - d) (h3 : ¬3 ∣ t - d) (hdt : d.Coprime t) :
    (t - d).Coprime (2 * (3 * t)) := by
  have hk2 := (Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm
  have hk3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have hkt := (Nat.coprime_self_sub_left hd).mpr hdt
  exact hk2.mul_right (hk3.mul_right hkt)

/-- Every n>15 has a coprime index strictly between 1 and n/3.
For n=3t, residues t mod 6 of 0,1,2,3,4,5 use shifts 1,2,1,2,3,4.
Writing the upper bound as 3*k<n avoids truncated natural-number division. -/
theorem exists_small_unit_of_large (n : ℕ) (hn : 15 < n) :
    ∃ k : ℕ, 1 < k ∧ 3 * k < n ∧ k.Coprime (2 * n) := by
  by_cases h3 : 3 ∣ n
  · obtain ⟨t, rfl⟩ := h3
    have ht : 5 < t := by omega
    have hcases : t % 6 = 0 ∨ t % 6 = 1 ∨ t % 6 = 2 ∨
        t % 6 = 3 ∨ t % 6 = 4 ∨ t % 6 = 5 := by omega
    rcases hcases with hmod | hmod | hmod | hmod | hmod | hmod
    · refine ⟨t - 1, by omega, by omega, ?_⟩
      exact shifted_index_coprime t 1 (by omega) (by omega) (by omega) (by simp)
    · refine ⟨t - 2, by omega, by omega, ?_⟩
      exact shifted_index_coprime t 2 (by omega) (by omega) (by omega)
        (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
    · refine ⟨t - 1, by omega, by omega, ?_⟩
      exact shifted_index_coprime t 1 (by omega) (by omega) (by omega) (by simp)
    · refine ⟨t - 2, by omega, by omega, ?_⟩
      exact shifted_index_coprime t 2 (by omega) (by omega) (by omega)
        (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega))
    · refine ⟨t - 3, by omega, by omega, ?_⟩
      exact shifted_index_coprime t 3 (by omega) (by omega) (by omega)
        (Nat.prime_three.coprime_iff_not_dvd.mpr (by omega))
    · refine ⟨t - 4, by omega, by omega, ?_⟩
      apply shifted_index_coprime t 4 (by omega) (by omega) (by omega)
      have hcop : Nat.Coprime 2 t := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
      simpa using (Nat.coprime_pow_left_iff (by decide : 0 < 2) 2 t).mpr hcop
  · refine ⟨3, by omega, by omega, ?_⟩
    exact (show Nat.Coprime 3 2 by decide).mul_right
      (Nat.prime_three.coprime_iff_not_dvd.mpr h3)

/-- Every denominator n≥4 outside S has a forbidden small unit.
The finite part only considers n<16 and indices k<4; k=3 suffices there. -/
theorem exists_small_unit_of_not_mem (n : ℕ) (hn : 4 ≤ n)
    (hnot : n ∉ repeatedDenominators) :
    ∃ k : ℕ, 1 < k ∧ 3 * k < n ∧ k.Coprime (2 * n) := by
  by_cases hlarge : 15 < n
  · exact exists_small_unit_of_large n hlarge
  · have hfinite : ∀ m : Fin 16, 4 ≤ (m : ℕ) → (m : ℕ) ∉ repeatedDenominators →
        ∃ k : Fin 4, 1 < (k : ℕ) ∧ 3 * (k : ℕ) < m ∧ (k : ℕ).Coprime (2 * m) := by
      decide +kernel
    obtain ⟨k, hk⟩ := hfinite ⟨n, by omega⟩ hn hnot
    exact ⟨k, hk⟩

/-- The converse finite check: denominators in S admit no small unit. -/
theorem no_small_unit_of_mem (n : ℕ) (hn : n ∈ repeatedDenominators) :
    ¬∃ k : ℕ, 1 < k ∧ 3 * k < n ∧ k.Coprime (2 * n) := by
  have hn16 : n < 16 := by
    unfold repeatedDenominators at hn
    fin_cases hn <;> omega
  have hfinite : ∀ m : Fin 16, (m : ℕ) ∈ repeatedDenominators →
      ∀ k : Fin 6, 1 < (k : ℕ) → 3 * (k : ℕ) < m → ¬(k : ℕ).Coprime (2 * m) := by
    decide +kernel
  rintro ⟨k, hk1, hk3, hk⟩
  exact hfinite ⟨n, hn16⟩ hn ⟨k, by omega⟩ hk1 hk3 hk

/-- PDF Lemma 4.1, with both directions and the full unbounded range. -/
theorem no_small_unit_iff_mem_repeatedDenominators (n : ℕ) (hn : 4 ≤ n) :
    (¬∃ k : ℕ, 1 < k ∧ 3 * k < n ∧ k.Coprime (2 * n)) ↔ n ∈ repeatedDenominators := by
  constructor
  · intro h
    by_contra hnot
    exact h (exists_small_unit_of_not_mem n hn hnot)
  · exact no_small_unit_of_mem n

end ArithmeticTriangles
