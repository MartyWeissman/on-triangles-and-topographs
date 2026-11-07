import ArithmeticTriangles

open ArithmeticTriangles

/- A first lesson using the definitions from this project.

An `example` is an unnamed theorem. The part before `:= by` states the
claim; the lines after it construct a proof that Lean checks.
-/

-- The angles of the (2, 3, 7) triangle sum to less than π.
example : Triangle.Hyperbolic ⟨2, 3, 7⟩ := by
  norm_num [Triangle.Hyperbolic]

-- Every equilateral triangle is isosceles.
example (triangle : Triangle) (h : triangle.Equilateral) :
    triangle.Isosceles := by
  -- `h` contains two equalities. `h.1` is the first: e = f.
  -- `Or.inl` uses that equality to prove the first alternative in Isosceles.
  exact Or.inl h.1

/- Lesson 2: reuse a general theorem to prove something about actual cosines.

The discriminant of (2,3,7) contains cos(π/7). We do not approximate it.
Instead, the new theorem turns its sign into a rational inequality.
-/
example : 0 < (⟨2, 3, 7⟩ : Triangle).discriminant := by
  -- First establish the hypotheses of the general theorem.
  have admissible : (⟨2, 3, 7⟩ : Triangle).Admissible := by
    norm_num [Triangle.Admissible]
  have hyperbolic : (⟨2, 3, 7⟩ : Triangle).Hyperbolic := by
    norm_num [Triangle.Hyperbolic]
  -- The equivalence is `0 < D ↔ Hyperbolic`.
  -- `.mpr` uses its right-to-left direction: hyperbolic implies positive D.
  exact (Triangle.discriminant_pos_iff_hyperbolic _ admissible).mpr hyperbolic

/- Lesson 3: pay attention to the hypotheses of a conditional result.

This proves a bound from an explicit structural hypothesis. Lesson 8 below
uses the new embedding argument to obtain that hypothesis from arithmeticity.
-/
example (triangle : Triangle) (admissible : triangle.Admissible)
    (scalene : triangle.Scalene) (structural : triangle.StructuralInequality)
    (first_is_three : triangle.e = 3) : triangle.g < 12 := by
  have bound := triangle.last_lt_first_mul_succ admissible scalene structural
  -- Substitute e=3 into the general bound g < e(e+1).
  rw [first_is_three] at bound
  -- `norm_num` checks the arithmetic 3*(3+1)=12.
  norm_num at bound
  exact bound

/- Lesson 4: why conjugates obey the same polynomial equations.

`σ : triangle.cosineField →ₐ[ℚ] ℝ` means a ℚ-algebra homomorphism.
It preserves addition, multiplication, and rational constants. Because its
source is a field and its target is nontrivial, it is also injective.
-/
example (triangle : Triangle) (σ : triangle.cosineField →ₐ[ℚ] ℝ)
    (x : triangle.cosineField) (hx : x ^ 2 = 2) : (σ x) ^ 2 = 2 := by
  -- Apply the function σ to both sides of the known equality.
  have transported := congrArg σ hx
  -- Rewrite σ(x²) as (σ x)² and σ(2) as 2.
  simpa only [map_pow, map_ofNat] using transported

/- Lesson 5: the quadratic relation gives two possibilities, not a free
choice of embeddings. This only constrains an embedding already given. -/
example (triangle : Triangle) (σ : triangle.cosineField →ₐ[ℚ] ℝ)
    (x : triangle.cosineField) (hx : (x : ℝ) ^ 2 = 2)
    (not_fixed : σ x ≠ (x : ℝ)) : σ x = -(x : ℝ) := by
  have possibilities := triangle.embedding_eq_or_eq_neg_of_square σ x 2 hx
  exact possibilities.resolve_left not_fixed

-- The new candidate theorem includes the sign condition at EVERY other
-- real embedding, not just the ordinary hyperbolic-angle inequality.
example : (⟨3, 3, 4⟩ : Triangle).ArithmeticHyperbolic :=
  arithmeticHyperbolic_three_three_four

/- Lesson 6: use total reality and the sign condition to bound the trace.

The trace belongs to ℚ, while D is a real number. The cast `: ℝ` lets Lean
compare them. The proof of `trace_le_discriminant` sums the negative values
at every embedding except the distinguished inclusion.
-/
example (triangle : Triangle) (h : triangle.ArithmeticHyperbolic) :
    (triangle.discriminantTrace : ℝ) < 16 := by
  have trace_bound := h.trace_le_discriminant
  have geometric_bound := triangle.discriminant_lt_sixteen h.admissible
  exact trace_bound.trans_lt geometric_bound

/- Lesson 7: a concrete use of the cyclotomic containment theorem.

Because 5 divides 15, `2 cos(π/5)` lies in ℚ(ζ₃₀). This proves field
membership; it does not assert that this element generates all of ℚ(ζ₃₀).
-/
example : (cosineGenerator 5 : ℂ) ∈ cosineCyclotomicField 15 := by
  exact cosineGenerator_mem_cyclotomic_of_dvd 5 15 (by norm_num) (by norm_num)

/- Lesson 8: the old conditional bound now has an arithmetic application.

Unlike Lesson 3, this example does not assume StructuralInequality. The
new theorem derives it from arithmeticity (and e>2) using cyclotomic embeddings.
-/
example (triangle : Triangle) (arithmetic : triangle.ArithmeticHyperbolic)
    (scalene : triangle.Scalene) (first_is_three : triangle.e = 3) :
    triangle.g < 12 := by
  have bound := arithmetic.last_lt_first_mul_succ (by omega) scalene
  rw [first_is_three] at bound
  norm_num at bound
  exact bound

/- Lesson 9: symmetry can compute a trace without finding every conjugate.

An automorphism `τ : F ≃ₐ[ℚ] F` is a bijective field map fixing ℚ.
If τ negates x, then Tr(x)=Tr(τ(x))=Tr(-x)=-Tr(x), hence Tr(x)=0.
Here x is any field element; the lemma is reusable beyond abc.
-/
example (triangle : Triangle) (τ : triangle.cosineField ≃ₐ[ℚ] triangle.cosineField)
    (x : triangle.cosineField) (negated : τ x = -x) : triangle.fieldTrace x = 0 := by
  -- Mathlib supplies invariance of trace under an algebra equivalence.
  have equal_traces := Algebra.trace_eq_of_algEquiv τ x
  -- `rw` uses our hypothesis, then linearity of trace on a negative element.
  rw [negated, map_neg] at equal_traces
  -- `change` unfolds the project abbreviation without changing the statement.
  change -triangle.fieldTrace x = triangle.fieldTrace x at equal_traces
  -- This last step is rational linear arithmetic, not a field-theory theorem.
  linarith

/- Lesson 10: separate the assumptions each argument actually needs.

Evenness of the degree needs ordering, e>2, and even N; it does not need
arithmeticity. This example asserts only degree parity for (3,4,5).
-/
example : Even (⟨3, 4, 5⟩ : Triangle).deg := by
  apply Triangle.even_deg_of_even_denominator
  · norm_num [Triangle.Admissible]
  · norm_num
  · norm_num [Triangle.commonDenominator, even_iff_two_dvd]

-- A concrete application of the new trace theorem to a verified candidate.
example : (⟨4, 4, 4⟩ : Triangle).fieldTrace
    (⟨4, 4, 4⟩ : Triangle).fieldGeneratorProduct = 0 := by
  apply arithmeticHyperbolic_four_four_four.product_trace_zero
  · norm_num
  · norm_num [Triangle.commonDenominator, even_iff_two_dvd]

/- Lesson 11: use a general trace formula without computing the field degree.

If the first denominator is 5, the normalized trace of a² is 3/2, even
though the other two denominators may change the field and its degree.
-/
example (triangle : Triangle) (admissible : triangle.Admissible)
    (first_is_five : triangle.e = 5) :
    triangle.fieldTrace (triangle.firstGenerator ^ 2) / triangle.deg = 3 / 2 := by
  have square_average := triangle.generator_square_trace admissible triangle.e
    (Nat.dvd_lcm_left _ _) triangle.firstGenerator rfl
  rw [first_is_five] at square_average
  -- The Möbius function is -1 at a prime; mathlib supplies primality of 5.
  have mu_five : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_five
  -- `decide` checks the finite count defining φ(5) in Lean's kernel.
  have phi_five : Nat.totient 5 = 4 := by decide
  -- The remaining calculation is 2 + 2*(-1)/4 = 3/2.
  norm_num [mu_five, phi_five] at square_average
  exact square_average

/- Lesson 12: evaluate the normalized discriminant trace of a known candidate.

The theorem supplies the field theory. The final line uses only the finite
values μ(3)=-1, φ(3)=2, μ(4)=0, φ(4)=2. Repeated 3s appear twice.
A positive discriminant can have zero trace: the other conjugates contribute
negative values.
-/
example : (⟨3, 3, 4⟩ : Triangle).normalizedDiscriminantTrace = 0 := by
  rw [arithmeticHyperbolic_three_three_four.normalizedDiscriminantTrace_even
    (by norm_num) (by norm_num [Triangle.commonDenominator, even_iff_two_dvd])]
  have mu_three : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have mu_four : ArithmeticFunction.moebius 4 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  norm_num [mu_three, mu_four,
    show Nat.totient 3 = 2 by decide, show Nat.totient 4 = 2 by decide]

-- μ(6)=+1, so all three square averages contribute more than 2 in this example.
example : (⟨6, 6, 6⟩ : Triangle).normalizedDiscriminantTrace = 5 := by
  rw [arithmeticHyperbolic_six_six_six.normalizedDiscriminantTrace_even
    (by norm_num) (by norm_num [Triangle.commonDenominator, even_iff_two_dvd])]
  -- Multiplicativity gives μ(6)=μ(2)μ(3)=(-1)(-1)=1.
  have mu_six := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (by decide : Nat.Coprime 2 3)
  norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three] at mu_six
  norm_num [mu_six, show Nat.totient 6 = 2 by decide]

/- Lesson 13: the infinite estimate has a finite exception.

The general ratio bound excludes 7. If n≥8, `omega` supplies both n≥6
and n≠7, allowing us to apply it. The second example checks the exceptional
value exactly; `+kernel` asks Lean's kernel to perform the reduction.
-/
example (n : ℕ) (at_least_eight : 8 ≤ n) : -(1 : ℚ) / 8 ≤ moebiusRatio n := by
  exact moebiusRatio_ge_neg_eighth n (by omega) (by omega)

example : moebiusRatio 7 = -(1 : ℚ) / 6 := by
  decide +kernel

/- Lesson 14: a previously conditional theorem now has its missing input.

The earlier degree bound required a trace lower bound. The new theorem
proves that input from arithmeticity, scaleneness, e≥4, and even N.
Here we assemble the two steps explicitly so the dependency is visible.
-/
example (triangle : Triangle) (arithmetic : triangle.ArithmeticHyperbolic)
    (scalene : triangle.Scalene) (first_at_least_four : 4 ≤ triangle.e)
    (even_common_denominator : Even triangle.commonDenominator) : triangle.deg ≤ 12 := by
  have lower_bound := arithmetic.trace_ge_degree_mul_seven_sixths
    scalene first_at_least_four even_common_denominator
  exact arithmetic.deg_le_twelve_of_trace_lower_bound
    (by omega) even_common_denominator lower_bound

-- With e=4, N is automatically even because 4 divides N. The new theorem
-- supplies both that fact and the trace lower bound internally.
example (triangle : Triangle) (arithmetic : triangle.ArithmeticHyperbolic)
    (scalene : triangle.Scalene) (first_is_four : triangle.e = 4) : triangle.deg ≤ 10 := by
  exact arithmetic.deg_le_ten_of_first_four scalene first_is_four

/- Lesson 15: identity on the field is a finite congruence calculation.

The signs are independent: for (3,4,4), k=7 is +1 modulo 6 but -1
modulo 8. It still fixes all three cosines. The predicate is decidable
integer arithmetic; the theorem connects it to an equality of field maps.
-/
example : (⟨3, 4, 4⟩ : Triangle).FixesCosines 7 := by decide

example : (⟨3, 4, 4⟩ : Triangle).cyclotomicRealEmbedding
    (by norm_num [Triangle.Admissible]) 7 (by decide) =
      (⟨3, 4, 4⟩ : Triangle).cosineField.val := by
  apply (Triangle.cyclotomicRealEmbedding_eq_inclusion_iff _ _ _ _).mpr
  decide

-- At (4,5,6), k=7 fixes the first generator but fails the other tests.
example : ¬(⟨4, 5, 6⟩ : Triangle).FixesCosines 7 := by decide

/- Lesson 16: use a general field-degree theorem to compute an example.

The field generated by 2cos(π/7) has degree φ(14)/2 = 3.
`rw` supplies the field theory; `decide` evaluates only the natural numbers.
-/
example : Module.finrank ℚ (singleCosineField 7) = 3 := by
  rw [singleCosineField_finrank 7 (by omega)]
  decide

/- Lesson 17: divisibility can exclude a triangle even when an inequality cannot.

For (4,5,19), the individual degree at 19 is φ(38)/2 = 9. Therefore
9 divides the full degree d. Arithmeticity would force d≤10 and even d.
The positive multiple 9 is odd, while the next multiple is 18: impossible.
The weaker estimate φ(38)≤20 alone would not exclude this triple.
-/
example : ¬(⟨4, 5, 19⟩ : Triangle).ArithmeticHyperbolic := by
  intro arithmetic
  let triangle : Triangle := ⟨4, 5, 19⟩
  change triangle.ArithmeticHyperbolic at arithmetic
  have scalene : triangle.Scalene := by norm_num [triangle, Triangle.Scalene]
  have degree_bound := arithmetic.deg_le_ten_of_first_four scalene rfl
  have degree_even := triangle.even_deg_of_even_denominator arithmetic.admissible
    (by norm_num [triangle])
    (by norm_num [triangle, Triangle.commonDenominator, even_iff_two_dvd])
  have divides_degree := triangle.cosine_degree_dvd 19 (by omega) triangle.thirdGenerator.property
  have degree_at_nineteen : Nat.totient (2 * 19) / 2 = 9 := by decide
  rw [degree_at_nineteen] at divides_degree
  have degree_positive := triangle.deg_pos
  -- Convert evenness to divisibility so `omega` sees both integer constraints.
  rw [even_iff_two_dvd] at degree_even
  omega

/- Lesson 18: reduce arithmeticity to an exhaustive finite family.

The hypothesis below is still substantial: it requires exact proofs of
negative real values. The new theorem supplies the completeness of this
family of tests, so no unseen embedding needs to be checked separately.
-/
example (triangle : Triangle) (admissible : triangle.Admissible)
    (hyperbolic : triangle.Hyperbolic)
    (negative_values : ∀ k : Fin (2 * triangle.commonDenominator),
      (k : ℕ).Coprime (2 * triangle.commonDenominator) →
      ¬triangle.FixesCosines k → triangle.cyclotomicDiscriminant k < 0) :
    triangle.ArithmeticHyperbolic := by
  exact (triangle.arithmeticHyperbolic_iff_cyclotomic admissible).mpr
    ⟨hyperbolic, negative_values⟩

/- Lesson 19: exact signs are easier than exact cosine values.

The certificate uses rational arithmetic to locate an angle modulo 2π.
A nonzero certificate has a proved meaning for the real cosine. The boundary
angle π/2 deliberately receives 0, so it cannot certify either strict sign.
-/
example : cosineSignCertificate (7 / 5) = -1 := by decide +kernel
example : cosineSignCertificate (1 / 2) = 0 := by decide +kernel
example : cosineSignCertificate (-2) = 1 := by decide +kernel

example : Real.cos ((7 / 5 : ℝ) * Real.pi) < 0 := by
  have certificate : cosineSignCertificate (7 / 5) = -1 := by decide +kernel
  have sign_correct := cosineSignCertificate_pos (7 / 5) (by omega)
  rw [certificate] at sign_correct
  norm_num at sign_correct
  exact sign_correct

/- Lesson 20: using the completed sufficiency theorem.

We no longer need a new conjugate calculation for each listed candidate.
The general theorem contains all those sign checks. Here `decide` proves
only membership of the concrete triple in the stated 25-element list.
-/
example : (⟨5, 5, 15⟩ : Triangle).ArithmeticHyperbolic := by
  apply expectedArithmeticTriples_arithmeticHyperbolic
  decide

example : (⟨2, 3, 11⟩ : Triangle).ArithmeticHyperbolic := by
  apply expectedArithmeticTriples_arithmeticHyperbolic
  decide

/- Lesson 21: one forbidden embedding is enough for an exclusion.

For (3,4,5), k=13 is coprime to 2N=120 and does not fix the cosine field.
Its four cosine factors have signs (-,+,+,-), so their product is positive.
The last three goals below are exact integer/rational computations.
-/
example : ¬(⟨3, 4, 5⟩ : Triangle).ArithmeticHyperbolic := by
  apply Triangle.not_arithmeticHyperbolic_of_sign_certificate _
    (by norm_num [Triangle.Admissible]) 13
  · decide
  · decide
  · decide +kernel

/- Lesson 22: a finite check can finish a theorem with unbounded parameters.

The library first uses structural bounds to place f and g in a finite box.
Its kernel-checked witness search then excludes every scalene triple there.
We can consequently apply the result to arbitrary f and g below.
-/
example (f g : ℕ) (first_smaller : 5 < f) (second_smaller : f < g) :
    ¬(⟨5, f, g⟩ : Triangle).ArithmeticHyperbolic := by
  apply Triangle.not_arithmeticHyperbolic_of_scalene_first_three_to_six
  · unfold Triangle.Scalene
    simp only
    omega
  · norm_num
  · norm_num

example (triangle : Triangle) (arithmetic : triangle.ArithmeticHyperbolic)
    (scalene : triangle.Scalene) (not_right : 2 < triangle.e) : 7 ≤ triangle.e := by
  exact arithmetic.seven_le_first_of_scalene scalene not_right

/- Lesson 23: an unbounded number-theoretic construction.

The small-unit theorem works for every n>15, not just a finite range. It
produces an index k whose cosine image is still greater than 1 and differs
from the principal value. The exclusion theorem turns it into a contradiction.
-/
example (n : ℕ) (large : 15 < n) :
    ¬(⟨n, n, n⟩ : Triangle).ArithmeticHyperbolic := by
  obtain ⟨k, greater_than_one, three_k_below_n, coprime⟩ := exists_small_unit_of_large n large
  exact not_equilateral_arithmetic_of_small_unit n k
    greater_than_one three_k_below_n coprime

-- For n=21=3*7, the construction uses k=7-2=5.
example : 1 < (5 : ℕ) ∧ 3 * 5 < 21 ∧ Nat.Coprime 5 (2 * 21) := by decide

/- Lesson 24: a classification theorem works in both directions.

`rw` replaces arithmeticity by membership in the eight-element denominator
set. The remaining claims are finite, decidable propositions. This uses both
the earlier survivor verification and the new completeness argument.
-/
example : (⟨8, 8, 8⟩ : Triangle).ArithmeticHyperbolic := by
  rw [equilateral_arithmetic_iff]
  decide

example : ¬(⟨10, 10, 10⟩ : Triangle).ArithmeticHyperbolic := by
  rw [equilateral_arithmetic_iff]
  decide

example : ¬(⟨3, 3, 21⟩ : Triangle).ArithmeticHyperbolic := by
  rw [initial_three_pair_arithmetic_iff]
  decide

/- Lesson 25: an index for a small field may need lifting.

For n=10, k=3 is a unit modulo 20, but is not a unit modulo the ambient
conductor 60 for (3,3,10). The replacement 23=3+20 is a unit modulo 60
and gives exactly the same cosine image. Periodicity proves the last claim.
-/
example : Nat.Coprime 3 (2 * 10) ∧ ¬Nat.Coprime 3 (2 * 30) := by decide
example : Nat.Coprime 23 (2 * 30) := by decide

example : Real.cos ((23 : ℝ) * Real.pi / 10) = Real.cos ((3 : ℝ) * Real.pi / 10) := by
  exact cosine_index_add_two_mul 10 3 (by decide)

/- Lesson 26: extract consequences from completeness.

The `.mp` direction takes arithmeticity as input and forces the denominator
into the finite set. `fin_cases` then handles all possibilities in that set.
-/
example (n : ℕ) (arithmetic : (⟨3, 3, n⟩ : Triangle).ArithmeticHyperbolic) : n ≤ 15 := by
  have in_the_list := (initial_three_pair_arithmetic_iff n).mp arithmetic
  unfold repeatedDenominators at in_the_list
  fin_cases in_the_list <;> omega

example (triangle : Triangle) (arithmetic : triangle.ArithmeticHyperbolic)
    (equilateral : triangle.Equilateral) : triangle ∈ expectedArithmeticTriples := by
  exact arithmetic.mem_expected_of_equilateral equilateral

/- Lesson 27: the entire right-triangle family is now classified.

This equivalence needs no preliminary bound on f or g. The library proves
oddness and denominator bounds first, then uses exact finite certificates.
`rw` lets us use that whole proof as a simple arithmetic description.
-/
example : (⟨2, 3, 9⟩ : Triangle).ArithmeticHyperbolic := by
  rw [right_arithmetic_iff]
  decide

example : ¬(⟨2, 3, 101⟩ : Triangle).ArithmeticHyperbolic := by
  rw [right_arithmetic_iff]
  decide

example (f g : ℕ) (arithmetic : (⟨2, f, g⟩ : Triangle).ArithmeticHyperbolic) :
    Odd f ∧ Odd g := by
  exact right_denominators_odd f g arithmetic

/- Lesson 28: a rational relation simplifies an infinite family.

For e=4 and e=6, the repeated cosine has square 2 and 3 respectively.
Every embedding preserves those rational squares. This makes the reduced
factor a²+c−2 easy to control and gives an unbounded classification in n.
-/
example (n : ℕ) : (⟨4, 4, n⟩ : Triangle).ArithmeticHyperbolic ↔ n = 4 := by
  exact four_or_six_pair_arithmetic_iff 4 n (Or.inl rfl)

example (n : ℕ) (larger : 6 < n) : ¬(⟨6, 6, n⟩ : Triangle).ArithmeticHyperbolic := by
  rw [four_or_six_pair_arithmetic_iff 6 n (Or.inr rfl)]
  omega

/- Lesson 29: a bound on every conjugate.

Here k is arbitrary. Coprimality ensures that it represents a conjugate;
the theorem bounds its square below. No decimal cosine values occur.
The n≥3 hypothesis matters: at n=2 the generator is zero.
-/
example (n k : ℕ) (at_least_three : 3 ≤ n) (coprime : k.Coprime n) :
    2 - cosineGenerator n ≤ (2 * Real.cos ((k : ℝ) * Real.pi / n)) ^ 2 := by
  exact cosine_power_sq_lower_bound n k at_least_three coprime

/- Lesson 30: read the scope of a completeness theorem from its hypotheses.

For (e,f,f) with e<f, the theorem below requires e≤15. Within this range,
f is unbounded at the start: the structural inequality forces f<2e.
This theorem alone does not cover the full infinite family. Lesson 33 uses
the later unbounded theorem.
-/
example : (⟨4, 5, 5⟩ : Triangle).ArithmeticHyperbolic := by
  rw [equal_larger_arithmetic_iff_of_first_le_fifteen 4 5 (by decide) (by decide) (by decide)]
  decide

example (f : ℕ) (larger : 11 < f) : ¬(⟨11, f, f⟩ : Triangle).ArithmeticHyperbolic := by
  rw [equal_larger_arithmetic_iff_of_first_le_fifteen 11 f (by decide) larger (by decide)]
  simp

/- Lesson 31: from uniqueness of an embedding to a field equality.

For arithmetic (e,e,g) with 2<e<g, fixing c forces identity because every
such embedding has positive discriminant. Over ℚ(c), the number of complex
embeddings equals the relative degree. There is only one, so that degree
is one and the entire cosine field is ℚ(c). We can use the conclusion directly.
-/
example (e g : ℕ) (not_right : 2 < e) (larger : e < g)
    (arithmetic : (⟨e, e, g⟩ : Triangle).ArithmeticHyperbolic) :
    (⟨e, e, g⟩ : Triangle).cosineField = singleCosineField g := by
  exact arithmetic.cosineField_eq_single_third not_right rfl larger

example (e g : ℕ) (not_right : 2 < e) (larger : e < g)
    (arithmetic : (⟨e, e, g⟩ : Triangle).ArithmeticHyperbolic) :
    singleCosineField e ≤ singleCosineField g := by
  exact arithmetic.single_first_le_single_third not_right rfl larger

/- Lesson 32: a complete classification is a reusable equivalence.

The theorem now applies to every triple. `rw` replaces the algebraic-number
condition by membership in the explicit list; `decide` checks that membership.
The work behind this short proof includes the infinite completeness argument.
-/
example : (⟨5, 5, 15⟩ : Triangle).ArithmeticHyperbolic := by
  rw [arithmeticHyperbolic_iff_mem]
  decide

example : ¬(⟨17, 19, 23⟩ : Triangle).ArithmeticHyperbolic := by
  rw [arithmeticHyperbolic_iff_mem]
  decide

/- Lesson 33: removing an old range restriction.

Compare with Lesson 30. The new final-pair theorem has no bound on e or f.
For an initial pair with e=5, the diagonal and two exceptional values survive.
-/
example (g : ℕ) : (⟨5, 5, g⟩ : Triangle).ArithmeticHyperbolic ↔
    g = 5 ∨ g = 10 ∨ g = 15 := by
  rw [initial_pair_arithmetic_iff]
  simp [repeatedDenominators]
  omega

example (e f : ℕ) (large : 16 ≤ e) :
    ¬(⟨e, f, f⟩ : Triangle).ArithmeticHyperbolic := by
  rw [final_pair_arithmetic_iff]
  simp [repeatedDenominators]
  omega

/- Lesson 34: a weak uniform estimate can finish a hard classification.

Here τ is the average of all conjugates of D, counting embeddings of the
whole cosine field. Seven root pairs each contribute at least −1/4 and the
constant contributes 2. Hence τ≥1/4. Together with Tr(D)<16, this bounds d.
The bound covers repeated and distinct denominators, and both parities of N.
-/
example (triangle : Triangle) (arithmetic : triangle.ArithmeticHyperbolic)
    (large : 11 ≤ triangle.e) : triangle.deg ≤ 63 := by
  exact arithmetic.deg_le_sixty_three_of_first_ge_eleven large

example (triangle : Triangle) (arithmetic : triangle.ArithmeticHyperbolic)
    (large : 11 ≤ triangle.e) : triangle.g ≤ 231 := by
  exact (arithmetic.denominators_le_231_of_first_ge_eleven large).2.2

/- Lesson 35: exact arithmetic can certify a real inequality.

The integer expression records the signs of four cosine factors. The
soundness theorem converts a positive certificate at a nonidentity embedding
into an obstruction to arithmeticity. These are the same ingredients used
in the large finite check; no approximate evaluation of cosine is involved.
-/
example : (⟨4, 5, 19⟩ : Triangle).integerDiscriminantSignCertificate 3 = 1 := by
  decide +kernel

example : ¬(⟨4, 5, 19⟩ : Triangle).ArithmeticHyperbolic := by
  apply Triangle.not_arithmeticHyperbolic_of_integer_sign_certificate _
    (by norm_num [Triangle.Admissible]) 3 (by decide) (by decide)
  decide +kernel

/- Lesson 36: keep the non-right hypothesis!

The completed theorem excludes every scalene case with e>2. It cannot exclude
all scalene arithmetic triples: (2,3,7), (2,3,9), and (2,3,11) are examples.
An explicit hypothesis keeps that distinction visible in the theorem's type.
-/
example (triangle : Triangle) (arithmetic : triangle.ArithmeticHyperbolic)
    (not_right : 2 < triangle.e) : triangle.Isosceles := by
  exact arithmetic.isosceles_of_not_right not_right

example (triangle : Triangle) (scalene : triangle.Scalene)
    (not_right : 2 < triangle.e) : ¬triangle.ArithmeticHyperbolic := by
  exact triangle.not_arithmeticHyperbolic_of_scalene scalene not_right
