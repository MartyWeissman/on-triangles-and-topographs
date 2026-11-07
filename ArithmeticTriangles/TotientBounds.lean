module

public import ArithmeticTriangles.TraceBounds
public import Mathlib.Data.Nat.Factorization.Induction

/-!
# Effective denominator bounds from small totients

The elementary estimate n≤2φ(n)² turns degree bounds into finite searches.
For the searches, Euler's product formula evaluates the same totient much
more efficiently than its definition as a count of coprime residues.
-/

@[expose] public section

namespace ArithmeticTriangles

/-- Euler's product formula, packaged for exact finite computations. -/
def fastTotient (n : ℕ) : ℕ :=
  if n = 0 then 0 else n.factorization.prod (fun p k => p ^ (k - 1) * (p - 1))

/-- The computational version is exactly Euler's totient, including at zero. -/
theorem fastTotient_eq (n : ℕ) : fastTotient n = n.totient := by
  by_cases hn : n = 0
  · simp [fastTotient, hn]
  · simp only [fastTotient, ite_eq_right hn]
    exact (Nat.totient_eq_prod_factorization hn).symm

/-- Odd numbers satisfy the slightly stronger estimate n≤φ(n)². -/
theorem odd_le_totient_sq (n : ℕ) (hn : Odd n) : n ≤ n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp at hn
  | one => simp
  | prime_pow p k hp hk =>
    have hpodd : Odd p := hn.of_dvd_nat (dvd_pow_self p (by omega : k ≠ 0))
    have hp3 : 3 ≤ p := by have := hp.two_le; obtain ⟨r, hr⟩ := hpodd; omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Nat.totient_prime_pow_succ hp, pow_succ]
    have hpow : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
    have hbase : p ≤ (p - 1) ^ 2 := by
      have hsub : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
      nlinarith
    calc
      p ^ j * p ≤ p ^ j * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hbase
      _ ≤ (p ^ j * (p - 1)) ^ 2 := by nlinarith
  | coprime a b ha hb hab ia ib =>
    obtain ⟨hao, hbo⟩ := Nat.odd_mul.mp hn
    rw [Nat.totient_mul hab, mul_pow]
    exact Nat.mul_le_mul (ia hao) (ib hbo)

/-- A uniform elementary totient bound. Only the prime 2 costs a factor 2. -/
theorem le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    by_cases hp2 : p = 2
    · subst p
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [Nat.totient_prime_pow_succ Nat.prime_two, pow_succ]
      simp only [Nat.reduceSub, mul_one]
      have hp : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by decide)
      nlinarith
    · have ho : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
      exact (odd_le_totient_sq _ ho).trans (by omega)
  | coprime a b ha hb hab ia ib =>
    rw [Nat.totient_mul hab, mul_pow]
    rcases Nat.even_or_odd a with hea | hoa
    · have hob : Odd b := by
        apply Nat.not_even_iff_odd.mp
        intro heb
        have hd := Nat.dvd_gcd hea.two_dvd heb.two_dvd
        rw [hab.gcd_eq_one] at hd
        omega
      have hbo := odd_le_totient_sq b hob
      nlinarith [Nat.mul_le_mul ia hbo]
    · have hao := odd_le_totient_sq a hoa
      nlinarith [Nat.mul_le_mul hao ib]

/-- If φ(2n)≤B, then n≤B². This deliberately coarse bound is enough to
justify the sharper, kernel-checked finite lists used below. -/
theorem denominator_le_totient_bound_sq (n B : ℕ) (h : (2 * n).totient ≤ B) : n ≤ B ^ 2 := by
  have hb := le_two_totient_sq (2 * n)
  nlinarith

end ArithmeticTriangles
