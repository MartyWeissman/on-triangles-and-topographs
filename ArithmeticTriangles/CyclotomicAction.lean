module

public import ArithmeticTriangles.Cyclotomic
public import ArithmeticTriangles.TotalReality

/-!
# Cyclotomic power automorphisms and their real restrictions

For a natural index k coprime to 2N, construct an ambient automorphism sending
our chosen primitive root to its kth power. Restrict its domain to the cosine
field, and use total reality to obtain an embedding into ℝ. This construction
does not require computing the stabilizer or the degree of the cosine field.
-/

@[expose] public section

namespace ArithmeticTriangles
/-- The chosen complex root, now as an element of the ambient field. -/
noncomputable def cyclotomicRoot (N : ℕ) : cosineCyclotomicField N :=
  ⟨cosineRoot N, IntermediateField.subset_adjoin ℚ _ (by simp)⟩

/-- Primitivity survives passage into the field subtype. -/
theorem cyclotomicRoot_primitive (N : ℕ) [NeZero N] :
    IsPrimitiveRoot (cyclotomicRoot N) (2 * N) := by
  exact (cosineRoot_primitive N (NeZero.ne N)).of_map_of_injective
    (cosineCyclotomicField N).val.injective

/-- A coprime power of the root has the same cyclotomic minimal polynomial.
Mathlib's power-basis equivalence therefore gives an automorphism carrying
the chosen root to that power. All generator images come from one map. -/
theorem exists_cyclotomicPowAut (N k : ℕ) [NeZero N] (hk : k.Coprime (2 * N)) :
    ∃ σ : cosineCyclotomicField N ≃ₐ[ℚ] cosineCyclotomicField N,
      σ (cyclotomicRoot N) = cyclotomicRoot N ^ k := by
  let hζ := cyclotomicRoot_primitive N
  let hμ := hζ.pow_of_coprime k hk
  have hirr := Polynomial.cyclotomic.irreducible_rat (show 0 < 2 * N by have := NeZero.pos N; omega)
  have hm : minpoly ℚ (cyclotomicRoot N) = minpoly ℚ (cyclotomicRoot N ^ k) :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible hirr).symm.trans
      (hμ.minpoly_eq_cyclotomic_of_irreducible hirr)
  refine ⟨(hζ.powerBasis ℚ).equivOfMinpoly (hμ.powerBasis ℚ) ?_, ?_⟩
  · simpa only [IsPrimitiveRoot.powerBasis_gen] using hm
  · exact (hζ.powerBasis ℚ).equivOfMinpoly_gen (hμ.powerBasis ℚ) _

/-- Choose the ambient automorphism whose existence was just proved.
Its action is fixed by `cyclotomicPowAut_root`. -/
noncomputable def cyclotomicPowAut (N k : ℕ) [NeZero N] (hk : k.Coprime (2 * N)) :
    cosineCyclotomicField N ≃ₐ[ℚ] cosineCyclotomicField N :=
  (exists_cyclotomicPowAut N k hk).choose

/-- The defining action on our specific root (not a separately chosen root). -/
theorem cyclotomicPowAut_root (N k : ℕ) [NeZero N] (hk : k.Coprime (2 * N)) :
    cyclotomicPowAut N k hk (cyclotomicRoot N) = cyclotomicRoot N ^ k :=
  (exists_cyclotomicPowAut N k hk).choose_spec

/-- Euler's identity for the kth power of our root. -/
theorem root_pow_add_inv (n k : ℕ) :
    cosineRoot n ^ k + (cosineRoot n ^ k)⁻¹ =
      ((2 * Real.cos ((k : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  unfold cosineRoot
  rw [← Complex.exp_nat_mul]
  push_cast
  rw [Complex.cos, mul_div_cancel₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [← Complex.exp_neg]
  congr 2 <;> ring

/-- If `n ∣ N`, the ambient automorphism sends `2 cos(π/n)` to `2 cos(kπ/n)`.
Write `N=n * m`, so that the smaller root is the mth power of the ambient root. -/
theorem cyclotomicPowAut_cosine (N k : ℕ) [NeZero N] (hk : k.Coprime (2 * N))
    (n : ℕ) (hdvd : n ∣ N) (x : cosineCyclotomicField N)
    (hx : (x : ℂ) = (cosineGenerator n : ℂ)) :
    (cyclotomicPowAut N k hk x : ℂ) =
      ((2 * Real.cos ((k : ℝ) * Real.pi / n) : ℝ) : ℂ) := by
  obtain ⟨m, rfl⟩ := hdvd
  have hn : n ≠ 0 := by have := NeZero.ne (n * m); aesop
  have hm : m ≠ 0 := by have := NeZero.ne (n * m); aesop
  let r : cosineCyclotomicField (n * m) := cyclotomicRoot (n * m) ^ m
  have hr : (r : ℂ) = cosineRoot n := cosineRoot_pow_mul n m hn hm
  have hx' : x = r + r⁻¹ := by
    apply Subtype.ext
    change (x : ℂ) = (r : ℂ) + (r : ℂ)⁻¹
    rw [hx, hr, cosineGenerator_eq_root_add_inv]
  have hσr : cyclotomicPowAut (n * m) k hk r = r ^ k := by
    simp only [r, map_pow, cyclotomicPowAut_root, ← pow_mul, Nat.mul_comm]
  rw [hx', map_add, map_inv₀, hσr]
  change (r : ℂ) ^ k + ((r : ℂ) ^ k)⁻¹ = _
  rw [hr, root_pow_add_inv]

namespace Triangle
/-- Bundle the previously proved field containment as an algebra embedding. -/
noncomputable def toCyclotomic (t : Triangle) (h : t.Admissible) :
    t.cosineField →ₐ[ℚ] cosineCyclotomicField t.commonDenominator :=
  ((IsScalarTower.toAlgHom ℚ ℝ ℂ).comp t.cosineField.val).codRestrict
    (cosineCyclotomicField t.commonDenominator).toSubalgebra (fun x =>
      t.cosineField_map_le_cyclotomic h
        ((IntermediateField.mem_map t.cosineField).mpr ⟨x, x.property, rfl⟩))

@[simp] theorem coe_toCyclotomic (t : Triangle) (h : t.Admissible) (x : t.cosineField) :
    (t.toCyclotomic h x : ℂ) = ((x : ℝ) : ℂ) := rfl

/-- Restrict the domain of an ambient automorphism, then use total reality
to view its image in ℝ. No formula for the cosine-field degree is needed. -/
noncomputable def cyclotomicRealEmbedding (t : Triangle) (h : t.Admissible)
    (k : ℕ) (hk : k.Coprime (2 * t.commonDenominator)) : t.cosineField →ₐ[ℚ] ℝ := by
  letI : NeZero t.commonDenominator := ⟨t.commonDenominator_ne_zero h⟩
  exact t.realEmbeddingOfComplex ((cosineCyclotomicField t.commonDenominator).val.comp
    ((cyclotomicPowAut t.commonDenominator k hk).toAlgHom.comp (t.toCyclotomic h)))

/-- The explicit action formula for any of the three cosine generators.
The divisibility and equality hypotheses let the same lemma cover all three. -/
theorem cyclotomicRealEmbedding_cosine (t : Triangle) (h : t.Admissible)
    (k : ℕ) (hk : k.Coprime (2 * t.commonDenominator))
    (n : ℕ) (hdvd : n ∣ t.commonDenominator) (x : t.cosineField)
    (hx : (x : ℝ) = cosineGenerator n) :
    t.cyclotomicRealEmbedding h k hk x = 2 * Real.cos ((k : ℝ) * Real.pi / n) := by
  let : NeZero t.commonDenominator := ⟨t.commonDenominator_ne_zero h⟩
  apply Complex.ofReal_injective
  unfold cyclotomicRealEmbedding
  rw [coe_realEmbeddingOfComplex]
  exact cyclotomicPowAut_cosine t.commonDenominator k hk n hdvd (t.toCyclotomic h x)
    (by simpa using congrArg Complex.ofReal hx)

end Triangle
end ArithmeticTriangles
