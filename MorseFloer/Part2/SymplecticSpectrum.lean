import MorseFloer.Part2.Ch5
import MorseFloer.Part2.SymplecticEigen

/-!
# The spectrum of a symplectic matrix is symmetric under `μ ↦ μ̄` and `μ ↦ 1/μ`

A brick for the continuity of `ρ` (§7.3.c): the multiset of eigenvalues of a real symplectic
matrix, counted with multiplicity, is stable under conjugation (`roots_map_conj`, the
coefficients being real) and under inversion (`roots_map_inv`, Proposition 5.6.4 read on the
multiset of roots).  The second is the content of the book's remark that the eigenvalues off
the unit circle come in pairs `μ, 1/μ̄` of equal multiplicity.

For inversion, the polynomial `q = ∏ (X - 1/z)` over the eigenvalues `z` is compared with the
characteristic polynomial `p`: for `λ ≠ 0`, `q(λ) = λ^{2n} (∏ 1/z) p(1/λ)`, and
`p(1/λ) = λ^{-2n} p(λ)` by Proposition 5.6.4, so `q = c p` on infinitely many points, hence as
polynomials, and `c = 1` by comparing leading coefficients.  No eigenvalue is zero, the
determinant being `1`.
-/

open Polynomial Matrix

namespace MorseFloer
namespace SymplecticSpectrum

open SymplecticEigen Chapter5

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem cpx_mem_symplecticGroup {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) : cpx A ∈ Matrix.symplecticGroup l ℂ :=
  SymplecticGroup.mem_iff'.2 (cpx_symplectic hA)

theorem charpoly_cpx (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (cpx A).charpoly = A.charpoly.map Complex.ofRealHom :=
  Matrix.charpoly_map A Complex.ofRealHom

/-- **The eigenvalues are stable under conjugation, with multiplicity.** -/
theorem roots_map_conj (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    (cpx A).charpoly.roots.map (starRingEnd ℂ) = (cpx A).charpoly.roots := by
  have hmap : (cpx A).charpoly.map (starRingEnd ℂ) = (cpx A).charpoly := by
    rw [charpoly_cpx, Polynomial.map_map]
    congr 1
    ext r
    simp
  have h := roots_map_of_injective_of_card_eq_natDegree (p := (cpx A).charpoly)
    (f := starRingEnd ℂ) (RingHom.injective _) IsAlgClosed.card_roots_eq_natDegree
  rw [h, hmap]

theorem det_cpx_eq_one {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    (cpx A).det = 1 :=
  SymplecticGroup.det_eq_one (cpx_mem_symplecticGroup hA)

omit [DecidableEq l] in
theorem even_card : Even (Fintype.card (l ⊕ l)) := ⟨Fintype.card l, by rw [Fintype.card_sum]⟩

/-- The characteristic polynomial at `t`, as a determinant. -/
theorem charpoly_eval (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) (t : ℂ) :
    M.charpoly.eval t = (M - t • 1).det := by
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← neg_sub,
    Matrix.det_neg, even_card.neg_one_pow, one_mul]

theorem zero_notMem_roots {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) : (0 : ℂ) ∉ (cpx A).charpoly.roots := by
  rw [mem_roots (charpoly_monic _).ne_zero, IsRoot, charpoly_eval, zero_smul, sub_zero,
    det_cpx_eq_one hA]
  exact one_ne_zero

/-- **Proposition 5.6.4** over `ℂ`: `p(λ) = λ^{2n} p(1/λ)` for the characteristic polynomial
`p` of a symplectic matrix and `λ ≠ 0`. -/
theorem charpoly_eval_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (hA : A ∈ Matrix.symplecticGroup l ℝ) {c : ℂ} (hc : c ≠ 0) :
    (cpx A).charpoly.eval c = c ^ Fintype.card (l ⊕ l) * (cpx A).charpoly.eval c⁻¹ := by
  rw [charpoly_eval, charpoly_eval, det_sub_inv_smul (cpx_mem_symplecticGroup hA) hc,
    even_card.neg_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, one_mul]

/-- **The eigenvalues are stable under inversion, with multiplicity.** -/
theorem roots_map_inv {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ) :
    (cpx A).charpoly.roots.map (fun z => z⁻¹) = (cpx A).charpoly.roots := by
  set p := (cpx A).charpoly with hp
  set s := p.roots with hs
  have hne : ∀ z ∈ s, z ≠ 0 := fun z hz h0 => zero_notMem_roots hA (h0 ▸ hz)
  have hcard : Multiset.card s = Fintype.card (l ⊕ l) := by
    rw [hs, IsAlgClosed.card_roots_eq_natDegree, hp, charpoly_natDegree_eq_dim]
  have hpprod : p = (s.map fun z => X - C z).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic _)
      IsAlgClosed.card_roots_eq_natDegree).symm
  set q : ℂ[X] := ((s.map fun z => z⁻¹).map fun z => X - C z).prod with hq
  set c : ℂ := (s.map fun z => z⁻¹).prod with hc
  -- `q(λ) = c p(λ)` for `λ ≠ 0`
  have hqeval : ∀ lam : ℂ, lam ≠ 0 → q.eval lam = c * p.eval lam := by
    intro lam hlam
    have h1 : q.eval lam = (s.map fun z => lam - z⁻¹).prod := by
      rw [hq, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun z _ => ?_
      simp
    have h2 : (s.map fun z => lam - z⁻¹).prod
        = (s.map fun z => lam * z⁻¹).prod * (s.map fun z => z - lam⁻¹).prod := by
      rw [← Multiset.prod_map_mul]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun z hz => ?_)
      field_simp [hne z hz]
    have h3 : (s.map fun z => lam * z⁻¹).prod = lam ^ Fintype.card (l ⊕ l) * c := by
      show (s.map fun z => lam * z⁻¹).prod = lam ^ Fintype.card (l ⊕ l) * (s.map fun z => z⁻¹).prod
      rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]
    have h4 : (s.map fun z => z - lam⁻¹).prod = p.eval lam⁻¹ := by
      rw [hpprod, eval_multiset_prod, Multiset.map_map]
      have e1 : (s.map fun z => z - lam⁻¹) = s.map fun z => (-1) * (lam⁻¹ - z) :=
        Multiset.map_congr rfl fun z _ => by ring
      have e2 : (s.map (eval lam⁻¹ ∘ fun z => X - C z)) = s.map fun z => lam⁻¹ - z :=
        Multiset.map_congr rfl fun z _ => by simp
      rw [e1, e2, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard,
        even_card.neg_one_pow, one_mul]
    rw [h1, h2, h3, h4, charpoly_eval_inv hA hlam]
    ring
  -- hence `q = c p` as polynomials
  have hqp : q = C c * p := by
    refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℂ)).infinite_compl.mono ?_)
    intro lam hlam
    rw [Set.mem_compl_singleton_iff] at hlam
    show q.eval lam = (C c * p).eval lam
    rw [eval_mul, eval_C, hqeval lam hlam]
  -- `c = 1`, comparing leading coefficients
  have hqmonic : q.Monic := monic_multiset_prod_of_monic _ _ fun z _ => monic_X_sub_C z
  have hc1 : c = 1 := by
    have := congrArg leadingCoeff hqp
    rw [hqmonic.leadingCoeff, leadingCoeff_mul, leadingCoeff_C, (charpoly_monic _).leadingCoeff,
      mul_one] at this
    exact this.symm
  rw [hc1, C_1, one_mul] at hqp
  -- and the roots agree
  have := congrArg roots hqp
  rw [hq, roots_multiset_prod_X_sub_C] at this
  exact this

/-- **The spectrum is stable under `μ ↦ 1/μ̄`.** -/
theorem inv_conj_mem_roots {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ Matrix.symplecticGroup l ℝ)
    {μ : ℂ} (hμ : μ ∈ (cpx A).charpoly.roots) : (starRingEnd ℂ μ)⁻¹ ∈ (cpx A).charpoly.roots := by
  have h1 : starRingEnd ℂ μ ∈ (cpx A).charpoly.roots := by
    rw [← roots_map_conj A]
    exact Multiset.mem_map_of_mem _ hμ
  rw [← roots_map_inv hA]
  exact Multiset.mem_map_of_mem _ h1

omit [DecidableEq l] [Fintype l] in
/-- The distance of `1/μ̄` to a point `c` of the unit circle is that of `μ`, divided by `‖μ‖`:
the eigenvalues near `c` of a nearby matrix stay in a disc about `c` under `μ ↦ 1/μ̄`. -/
theorem norm_inv_conj_sub {c μ : ℂ} (hc : ‖c‖ = 1) (hμ : μ ≠ 0) :
    ‖(starRingEnd ℂ μ)⁻¹ - c‖ = ‖μ - c‖ / ‖μ‖ := by
  have hμ' : starRingEnd ℂ μ ≠ 0 := (_root_.map_ne_zero _).2 hμ
  have hcc : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]
    simp
  have e : (starRingEnd ℂ μ)⁻¹ - c = c * starRingEnd ℂ (c - μ) / starRingEnd ℂ μ := by
    rw [map_sub, mul_sub, hcc]
    field_simp
  rw [e, norm_div, norm_mul, Complex.norm_conj, Complex.norm_conj, hc, one_mul, norm_sub_rev]

end SymplecticSpectrum
end MorseFloer
