import MorseFloer.Part2.RootsContinuity

/-!
# Spectral projectors of a matrix, and their continuity

The second brick for the map `ρ : Sp(2n) → S¹` of Chapter 7.  For a complex matrix `A` and a
disc `D` about `c` of radius `r` whose boundary circle carries no eigenvalue of `A`, the
characteristic polynomial splits as `f_A · g_A`, `f_A` collecting the eigenvalues in `D` and
`g_A` the others (`fPoly`, `gPoly`, `fPoly_mul_gPoly`).  The two factors are coprime
(`isCoprime_fPoly_gPoly`), so `ℂⁿ = ker f_A(A) ⊕ ker g_A(A)`: the first summand is the sum
of the generalised eigenspaces for the eigenvalues in `D`.

The **spectral projector** onto that sum is built from a Bézout relation `u₀ f₀ + v₀ g₀ = 1`
at a base point `A₀`, without contour integrals: for `A` near `A₀`,
`R_A = u₀ f_A(A) + v₀ g_A(A)` is close to the identity, hence invertible, and

`P_A = v₀(A) g_A(A) R_A⁻¹`

is the projector onto `ker f_A(A)` along `ker g_A(A)` (`proj`, `exists_continuous_projector`).
It is continuous in `A`, because the coefficients of `f_A` and `g_A` are
(`continuousAt_coeff_filterProd`): by the continuity of the roots
(`Part2/RootsContinuity.lean`) the eigenvalues in `D` of a nearby matrix are close to those of
`A₀`, with multiplicity, and the coefficients of `∏ (X - a_i)` are uniformly continuous in `a`
on a bounded set.  The number of eigenvalues in `D`, with multiplicity, is locally constant.
-/

open Polynomial Filter Topology Metric Set Matrix

namespace MorseFloer
namespace SpectralProjector

variable {m : Type*} [Fintype m] [DecidableEq m]

/-! ### Continuity of coefficients -/

/-- The coefficients of a finite product are continuous when those of the factors are. -/
theorem continuous_coeff_finset_prod {α ι : Type*} [TopologicalSpace α] (s : Finset ι)
    (Q : α → ι → ℂ[X]) (hQ : ∀ i ∈ s, ∀ k, Continuous fun x => (Q x i).coeff k) (k : ℕ) :
    Continuous fun x => (∏ i ∈ s, Q x i).coeff k := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty]
    exact continuous_const
  | insert i s hi ih =>
    have e : (fun x => (∏ j ∈ insert i s, Q x j).coeff k)
        = fun x => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          (Q x i).coeff (p : ℕ × ℕ).1 * (∏ j ∈ s, Q x j).coeff (p : ℕ × ℕ).2 :=
      funext fun x => by rw [Finset.prod_insert hi, coeff_mul]
    rw [e]
    exact continuous_finsetSum _ fun p _ => (hQ i (Finset.mem_insert_self i s) p.1).mul
      (ih (fun j hj k => hQ j (Finset.mem_insert_of_mem hj) k) p.2)

/-- The coefficients of `X - C (x i)` are continuous in `x`. -/
theorem continuous_coeff_X_sub_C {ι : Type*} (i : ι) (k : ℕ) :
    Continuous fun x : ι → ℂ => (X - C (x i)).coeff k := by
  have e : (fun x : ι → ℂ => (X - C (x i)).coeff k)
      = fun x => (X : ℂ[X]).coeff k - if k = 0 then x i else 0 :=
    funext fun x => by rw [coeff_sub, coeff_C]
  rw [e]
  refine continuous_const.sub ?_
  split_ifs
  · exact continuous_apply i
  · exact continuous_const

/-- The coefficients of `∏ i ∈ I, (X - C (x i))` are continuous in `x`. -/
theorem continuous_coeff_prod_X_sub_C {ι : Type*} (I : Finset ι) (k : ℕ) :
    Continuous fun x : ι → ℂ => (∏ i ∈ I, (X - C (x i))).coeff k := by
  classical
  induction I using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty]
    exact continuous_const
  | insert i s hi ih =>
    have e : (fun x : ι → ℂ => (∏ j ∈ insert i s, (X - C (x j))).coeff k)
        = fun x => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
          (X - C (x i)).coeff (p : ℕ × ℕ).1 * (∏ j ∈ s, (X - C (x j))).coeff (p : ℕ × ℕ).2 :=
      funext fun x => by rw [Finset.prod_insert hi, coeff_mul]
    rw [e]
    exact continuous_finsetSum _ fun p _ => (continuous_coeff_X_sub_C i p.1).mul (ih p.2)

/-- **The coefficients of the characteristic polynomial are continuous in the matrix.** -/
theorem continuous_charpoly_coeff (k : ℕ) :
    Continuous fun A : Matrix m m ℂ => A.charpoly.coeff k := by
  classical
  have e : (fun A : Matrix m m ℂ => A.charpoly.coeff k)
      = fun A => ∑ σ : Equiv.Perm m,
          ((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, charmatrix A (σ i) i).coeff k := by
    funext A
    rw [charpoly, det_apply', finsetSum_coeff]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← C_eq_intCast, coeff_C_mul]
  rw [e]
  refine continuous_finsetSum _ fun σ _ => continuous_const.mul ?_
  refine continuous_coeff_finset_prod Finset.univ (fun A i => charmatrix A (σ i) i)
    (fun i _ j => ?_) k
  have e2 : (fun A : Matrix m m ℂ => (charmatrix A (σ i) i).coeff j)
      = fun A => ((Matrix.diagonal fun _ : m => (X : ℂ[X])) (σ i) i).coeff j
        - if j = 0 then A (σ i) i else 0 :=
    funext fun A => by rw [charmatrix_apply, coeff_sub, coeff_C]
  rw [e2]
  refine continuous_const.sub ?_
  split_ifs
  · exact continuous_id.matrix_elem (σ i) i
  · exact continuous_const

/-! ### Splitting the characteristic polynomial along a disc -/

variable (c : ℂ) (r : ℝ)

/-- The eigenvalues in the open disc, with multiplicity. -/
noncomputable def inside (A : Matrix m m ℂ) : Multiset ℂ :=
  A.charpoly.roots.filter fun z => dist z c < r

/-- The eigenvalues outside the open disc, with multiplicity. -/
noncomputable def outside (A : Matrix m m ℂ) : Multiset ℂ :=
  A.charpoly.roots.filter fun z => ¬dist z c < r

/-- The factor of the characteristic polynomial carrying the eigenvalues in the disc. -/
noncomputable def fPoly (A : Matrix m m ℂ) : ℂ[X] := ((inside c r A).map fun z => X - C z).prod

/-- The complementary factor. -/
noncomputable def gPoly (A : Matrix m m ℂ) : ℂ[X] := ((outside c r A).map fun z => X - C z).prod

theorem fPoly_mul_gPoly (A : Matrix m m ℂ) : fPoly c r A * gPoly c r A = A.charpoly := by
  rw [fPoly, gPoly, ← Multiset.prod_add, ← Multiset.map_add, inside, outside,
    Multiset.filter_add_not]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq (charpoly_monic A)
    IsAlgClosed.card_roots_eq_natDegree

theorem monic_fPoly (A : Matrix m m ℂ) : (fPoly c r A).Monic :=
  monic_multiset_prod_of_monic _ _ fun z _ => monic_X_sub_C z

theorem monic_gPoly (A : Matrix m m ℂ) : (gPoly c r A).Monic :=
  monic_multiset_prod_of_monic _ _ fun z _ => monic_X_sub_C z

theorem natDegree_prod_X_sub_C (s : Multiset ℂ) :
    ((s.map fun z => X - C z).prod).natDegree = Multiset.card s := by
  have hmon : ∀ q ∈ s.map fun z => X - C z, Monic q := fun q hq => by
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hq
    exact monic_X_sub_C z
  refine (natDegree_multiset_prod_of_monic _ hmon).trans ?_
  simp [Multiset.map_map]

theorem natDegree_fPoly (A : Matrix m m ℂ) :
    (fPoly c r A).natDegree = Multiset.card (inside c r A) :=
  natDegree_prod_X_sub_C _

theorem natDegree_gPoly (A : Matrix m m ℂ) :
    (gPoly c r A).natDegree = Multiset.card (outside c r A) :=
  natDegree_prod_X_sub_C _

theorem card_inside_le (A : Matrix m m ℂ) : Multiset.card (inside c r A) ≤ Fintype.card m := by
  rw [← charpoly_natDegree_eq_dim A, ← IsAlgClosed.card_roots_eq_natDegree]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

theorem card_outside_le (A : Matrix m m ℂ) : Multiset.card (outside c r A) ≤ Fintype.card m := by
  rw [← charpoly_natDegree_eq_dim A, ← IsAlgClosed.card_roots_eq_natDegree]
  exact Multiset.card_le_card (Multiset.filter_le _ _)

/-- The two factors are coprime: they have no common root. -/
theorem isCoprime_fPoly_gPoly (A : Matrix m m ℂ) : IsCoprime (fPoly c r A) (gPoly c r A) := by
  classical
  rw [fPoly, gPoly, Finset.prod_multiset_map_count, Finset.prod_multiset_map_count]
  refine IsCoprime.prod_left fun z hz => IsCoprime.prod_right fun w hw => IsCoprime.pow ?_
  refine isCoprime_X_sub_C_of_isUnit_sub ?_
  rw [isUnit_iff_ne_zero, sub_ne_zero]
  intro hzw
  rw [Multiset.mem_toFinset, inside, Multiset.mem_filter] at hz
  rw [Multiset.mem_toFinset, outside, Multiset.mem_filter] at hw
  exact hw.2 (hzw ▸ hz.2)

theorem aeval_fPoly_mul_gPoly (A : Matrix m m ℂ) :
    aeval A (fPoly c r A) * aeval A (gPoly c r A) = 0 := by
  rw [← map_mul, fPoly_mul_gPoly, aeval_self_charpoly]

/-! ### Continuity of the two factors -/

/-- The product over the eigenvalues satisfying a predicate, read through an enumeration of the
eigenvalues. -/
theorem filterProd_eq_prod {n : ℕ} (Pred : ℂ → Prop) [DecidablePred Pred] (x : Fin n → ℂ) :
    (((Finset.univ.val.map x).filter Pred).map fun z => X - C z).prod
      = ∏ i ∈ Finset.univ.filter (fun i => Pred (x i)), (X - C (x i)) := by
  rw [Multiset.filter_map, Finset.prod_eq_multiset_prod, Finset.filter_val, Multiset.map_map]
  rfl

/-- A root of a polynomial whose coefficients are within `1` of those of `p` is bounded in terms
of `p` alone. -/
theorem norm_root_le_of_coeff_close {n : ℕ} {p q : ℂ[X]} (hq : q.Monic) (hqn : q.natDegree = n)
    (hclose : ∀ i, ‖q.coeff i - p.coeff i‖ ≤ 1) {z : ℂ} (hz : q.IsRoot z) :
    ‖z‖ ≤ max 1 (∑ i ∈ Finset.range n, (‖p.coeff i‖ + 1)) := by
  refine (RootsContinuity.norm_root_le hq hz).trans (max_le_max le_rfl ?_)
  rw [hqn]
  refine Finset.sum_le_sum fun i _ => ?_
  calc ‖q.coeff i‖ = ‖p.coeff i + (q.coeff i - p.coeff i)‖ := by rw [add_sub_cancel]
    _ ≤ ‖p.coeff i‖ + ‖q.coeff i - p.coeff i‖ := norm_add_le _ _
    _ ≤ ‖p.coeff i‖ + 1 := by linarith [hclose i]

/-- **The coefficients of the factor selected by a stable predicate are continuous.**  If the
predicate does not change within `ε₀` of any eigenvalue of `A₀`, the coefficients of the
product of `X - z` over the eigenvalues `z` satisfying it are continuous at `A₀`. -/
theorem continuousAt_coeff_filterProd (Pred : ℂ → Prop) [DecidablePred Pred]
    (A₀ : Matrix m m ℂ) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hstab : ∀ z ∈ A₀.charpoly.roots, ∀ w : ℂ, dist w z < ε₀ → (Pred w ↔ Pred z)) (k : ℕ) :
    ContinuousAt (fun A : Matrix m m ℂ =>
      (((A.charpoly.roots.filter Pred).map fun z => X - C z).prod).coeff k) A₀ := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Fintype.card m = N := ⟨_, rfl⟩
  -- the coefficient maps on enumerations, uniformly continuous on a bounded set
  have hΦ : Continuous fun x : Fin N → ℂ => fun I : Finset (Fin N) =>
      (∏ i ∈ I, (X - C (x i))).coeff k :=
    continuous_pi fun I => continuous_coeff_prod_X_sub_C I k
  have hK : IsCompact (closedBall (0 : Fin N → ℂ)
      (max 1 (∑ i ∈ Finset.range N, (‖A₀.charpoly.coeff i‖ + 1)))) :=
    isCompact_closedBall _ _
  have hΦu := hK.uniformContinuousOn_of_continuous hΦ.continuousOn
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.uniformContinuousOn_iff.1 hΦu η hη
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := RootsContinuity.exists_delta_roots_close (n := N)
    (p := A₀.charpoly) (ε := min δ₁ ε₀) (lt_min hδ₁ hε₀)
  -- the neighbourhood on which the coefficients are close
  have hcoef : ∀ᶠ A in 𝓝 A₀, ∀ i ∈ Finset.range (N + 1),
      ‖A.charpoly.coeff i - A₀.charpoly.coeff i‖ < min δ₂ 1 := by
    rw [eventually_all_finset]
    intro i _
    have h := (continuous_charpoly_coeff (m := m) i).continuousAt (x := A₀)
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 h)).2 _ (lt_min hδ₂ one_pos)
  filter_upwards [hcoef] with A hA
  have hclose : ∀ i, ‖A.charpoly.coeff i - A₀.charpoly.coeff i‖ < min δ₂ 1 := by
    intro i
    by_cases hi : i ∈ Finset.range (N + 1)
    · exact hA i hi
    · rw [Finset.mem_range, not_lt] at hi
      rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, hN]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, hN]; omega), sub_zero,
        norm_zero]
      exact lt_min hδ₂ one_pos
  obtain ⟨a, b, ha, hb, hab⟩ := hδ₂' A.charpoly (charpoly_monic A)
    (by rw [charpoly_natDegree_eq_dim, hN]) fun i => (hclose i).trans_le (min_le_left _ _)
  -- the predicate agrees on matched roots
  have hbmem : ∀ i, b i ∈ A₀.charpoly.roots := fun i => by
    rw [hb]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  have hI : ∀ i, Pred (a i) ↔ Pred (b i) := fun i =>
    hstab (b i) (hbmem i) (a i) (by
      rw [dist_eq_norm]
      exact (hab i).trans_le (min_le_right _ _))
  have hfilt : (Finset.univ.filter fun i => Pred (a i)) = Finset.univ.filter fun i => Pred (b i) :=
    Finset.filter_congr fun i _ => hI i
  -- both enumerations lie in the bounded set
  have haK : a ∈ closedBall (0 : Fin N → ℂ)
      (max 1 (∑ i ∈ Finset.range N, (‖A₀.charpoly.coeff i‖ + 1))) := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    refine norm_root_le_of_coeff_close (charpoly_monic A)
      (by rw [charpoly_natDegree_eq_dim, hN]) (fun j => ((hclose j).trans_le (min_le_right _ _)).le) ?_
    refine (mem_roots (charpoly_monic A).ne_zero).1 ?_
    rw [ha]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  have hbK : b ∈ closedBall (0 : Fin N → ℂ)
      (max 1 (∑ i ∈ Finset.range N, (‖A₀.charpoly.coeff i‖ + 1))) := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    refine norm_root_le_of_coeff_close (charpoly_monic A₀)
      (by rw [charpoly_natDegree_eq_dim, hN]) (fun j => by rw [sub_self, norm_zero]; exact zero_le_one) ?_
    exact (mem_roots (charpoly_monic A₀).ne_zero).1 (hbmem i)
  have hdist : dist a b < δ₁ := by
    rw [dist_pi_lt_iff hδ₁]
    intro i
    rw [dist_eq_norm]
    exact (hab i).trans_le (min_le_left _ _)
  have hΦab := hδ₁' a haK b hbK hdist
  rw [ha, hb, filterProd_eq_prod, filterProd_eq_prod, hfilt, dist_eq_norm]
  have := dist_le_pi_dist (fun I : Finset (Fin N) => (∏ i ∈ I, (X - C (a i))).coeff k)
    (fun I => (∏ i ∈ I, (X - C (b i))).coeff k) (Finset.univ.filter fun i => Pred (b i))
  rw [dist_eq_norm] at this
  exact this.trans_lt hΦab

/-- The separation of the eigenvalues of `A₀` from the circle. -/
theorem exists_circle_separation (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ z ∈ A₀.charpoly.roots, ε₀ ≤ |dist z c - r| := by
  classical
  rcases A₀.charpoly.roots.toFinset.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    exact absurd (Multiset.mem_toFinset.2 hz) (by rw [h]; exact Finset.notMem_empty z)
  obtain ⟨z₀, hz₀, hmin⟩ := Finset.exists_min_image _ (fun z => |dist z c - r|) h
  refine ⟨|dist z₀ c - r|, abs_pos.2 (sub_ne_zero.2 (hcirc z₀ (Multiset.mem_toFinset.1 hz₀))),
    fun z hz => hmin z (Multiset.mem_toFinset.2 hz)⟩

/-- Inside the disc is a stable predicate away from the circle. -/
theorem stable_inside {ε₀ : ℝ} {z w : ℂ} (hz : ε₀ ≤ |dist z c - r|) (hw : dist w z < ε₀) :
    dist w c < r ↔ dist z c < r := by
  have h1 := dist_triangle w z c
  have h2 := dist_triangle z w c
  rw [dist_comm z w] at h2
  rcases lt_or_ge (dist z c) r with h | h
  · rw [abs_of_neg (by linarith)] at hz
    exact ⟨fun _ => h, fun _ => by linarith⟩
  · rw [abs_of_nonneg (by linarith)] at hz
    exact ⟨fun h' => absurd h' (by linarith), fun h' => absurd h' (not_lt.2 h)⟩

theorem continuousAt_coeff_fPoly (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r) (k : ℕ) :
    ContinuousAt (fun A => (fPoly c r A).coeff k) A₀ := by
  obtain ⟨ε₀, hε₀, hsep⟩ := exists_circle_separation c r A₀ hcirc
  exact continuousAt_coeff_filterProd (fun z => dist z c < r) A₀ hε₀
    (fun z hz w hw => stable_inside c r (hsep z hz) hw) k

theorem continuousAt_coeff_gPoly (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r) (k : ℕ) :
    ContinuousAt (fun A => (gPoly c r A).coeff k) A₀ := by
  obtain ⟨ε₀, hε₀, hsep⟩ := exists_circle_separation c r A₀ hcirc
  exact continuousAt_coeff_filterProd (fun z => ¬dist z c < r) A₀ hε₀
    (fun z hz w hw => not_congr (stable_inside c r (hsep z hz) hw)) k

/-! ### The projector -/

section Algebra

variable (A : Matrix m m ℂ)

theorem aeval_comm (p q : ℂ[X]) : aeval A p * aeval A q = aeval A q * aeval A p := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem mul_aeval_comm (q : ℂ[X]) : A * aeval A q = aeval A q * A := by
  have := aeval_comm A X q
  rwa [aeval_X] at this

theorem inv_comm_of_comm {B R : Matrix m m ℂ} (hR : IsUnit R.det) (h : B * R = R * B) :
    B * R⁻¹ = R⁻¹ * B := by
  calc B * R⁻¹ = R⁻¹ * (R * B) * R⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hR, Matrix.one_mul]
    _ = R⁻¹ * (B * R) * R⁻¹ := by rw [h]
    _ = R⁻¹ * B * (R * R⁻¹) := by simp only [Matrix.mul_assoc]
    _ = R⁻¹ * B := by rw [Matrix.mul_nonsing_inv _ hR, Matrix.mul_one]

/-- **The projector attached to a Bézout-like relation.**  If `f g` vanishes at `A` and
`R = u f + v g` is invertible at `A`, then `P = v g R⁻¹` is a projector commuting with `A`,
killed by `f`, with `g` killing `1 - P`; it fixes `ker f(A)` and kills `ker g(A)`. -/
theorem proj_spec {u v f g : ℂ[X]} (hfg : aeval A (f * g) = 0)
    (hR : IsUnit (aeval A (u * f + v * g)).det) :
    aeval A (v * g) * (aeval A (u * f + v * g))⁻¹ * (aeval A (v * g) * (aeval A (u * f + v * g))⁻¹)
        = aeval A (v * g) * (aeval A (u * f + v * g))⁻¹ ∧
      A * (aeval A (v * g) * (aeval A (u * f + v * g))⁻¹)
        = aeval A (v * g) * (aeval A (u * f + v * g))⁻¹ * A ∧
      aeval A f * (aeval A (v * g) * (aeval A (u * f + v * g))⁻¹) = 0 ∧
      aeval A g * (1 - aeval A (v * g) * (aeval A (u * f + v * g))⁻¹) = 0 ∧
      (∀ x, aeval A f *ᵥ x = 0 → (aeval A (v * g) * (aeval A (u * f + v * g))⁻¹) *ᵥ x = x) ∧
      (∀ x, aeval A g *ᵥ x = 0 → (aeval A (v * g) * (aeval A (u * f + v * g))⁻¹) *ᵥ x = 0) := by
  set R := aeval A (u * f + v * g) with hRdef
  set VG := aeval A (v * g) with hVGdef
  have hRsplit : R = aeval A (u * f) + VG := by rw [hRdef, hVGdef, map_add]
  have hVG_U : VG * aeval A (u * f) = 0 := by
    rw [hVGdef, ← map_mul, show v * g * (u * f) = v * u * (f * g) by ring, map_mul, hfg, mul_zero]
  have hG_U : aeval A g * aeval A (u * f) = 0 := by
    rw [← map_mul, show g * (u * f) = u * (f * g) by ring, map_mul, hfg, mul_zero]
  have hVG_R : VG * R = VG * VG := by rw [hRsplit, Matrix.mul_add, hVG_U, zero_add]
  have hG_R : aeval A g * R = aeval A g * VG := by rw [hRsplit, Matrix.mul_add, hG_U, zero_add]
  have hcommR : ∀ q, aeval A q * R⁻¹ = R⁻¹ * aeval A q := fun q =>
    inv_comm_of_comm hR (aeval_comm A q _)
  have hAR : A * R⁻¹ = R⁻¹ * A := inv_comm_of_comm hR (mul_aeval_comm A _)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc VG * R⁻¹ * (VG * R⁻¹) = VG * (R⁻¹ * VG) * R⁻¹ := by simp only [Matrix.mul_assoc]
      _ = VG * (VG * R⁻¹) * R⁻¹ := by rw [hcommR]
      _ = VG * VG * (R⁻¹ * R⁻¹) := by simp only [Matrix.mul_assoc]
      _ = VG * R * (R⁻¹ * R⁻¹) := by rw [hVG_R]
      _ = VG * R⁻¹ := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, Matrix.mul_nonsing_inv _ hR, Matrix.one_mul]
  · calc A * (VG * R⁻¹) = A * VG * R⁻¹ := by rw [Matrix.mul_assoc]
      _ = VG * A * R⁻¹ := by rw [mul_aeval_comm]
      _ = VG * (A * R⁻¹) := by rw [Matrix.mul_assoc]
      _ = VG * (R⁻¹ * A) := by rw [hAR]
      _ = VG * R⁻¹ * A := by rw [Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc, hVGdef, ← map_mul, show f * (v * g) = v * (f * g) by ring, map_mul,
      hfg, mul_zero, Matrix.zero_mul]
  · rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← hG_R, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hR, Matrix.mul_one, sub_self]
  · intro x hx
    have h1 : R *ᵥ x = VG *ᵥ x := by
      rw [hRsplit, Matrix.add_mulVec, map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero,
        zero_add]
    rw [hcommR, ← Matrix.mulVec_mulVec, ← h1, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hR,
      Matrix.one_mulVec]
  · intro x hx
    have h1 : VG *ᵥ x = 0 := by
      rw [hVGdef, map_mul, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    rw [hcommR, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

end Algebra

/-- The candidate projector, built from a Bézout pair `(u₀, v₀)` chosen at a base point. -/
noncomputable def projOf (u₀ v₀ : ℂ[X]) (A : Matrix m m ℂ) : Matrix m m ℂ :=
  aeval A (v₀ * gPoly c r A) * (aeval A (u₀ * fPoly c r A + v₀ * gPoly c r A))⁻¹

/-! ### Continuity of the matrix-valued pieces -/

theorem continuousAt_aeval_of_coeff {q : Matrix m m ℂ → ℂ[X]} {N : ℕ} (A₀ : Matrix m m ℂ)
    (hdeg : ∀ A, (q A).natDegree < N) (hcoef : ∀ k, ContinuousAt (fun A => (q A).coeff k) A₀) :
    ContinuousAt (fun A => aeval A (q A)) A₀ := by
  have e : (fun A : Matrix m m ℂ => aeval A (q A))
      = fun A => ∑ i ∈ Finset.range N, (q A).coeff i • A ^ i :=
    funext fun A => aeval_eq_sum_range' (hdeg A) A
  rw [e]
  exact tendsto_finsetSum _ fun i _ => (hcoef i).smul (continuous_pow i).continuousAt

theorem continuousAt_aeval_fPoly (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r) :
    ContinuousAt (fun A => aeval A (fPoly c r A)) A₀ :=
  continuousAt_aeval_of_coeff (N := Fintype.card m + 1) A₀
    (fun A => by rw [natDegree_fPoly]; exact Nat.lt_succ_of_le (card_inside_le c r A))
    (continuousAt_coeff_fPoly c r A₀ hcirc)

theorem continuousAt_aeval_gPoly (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r) :
    ContinuousAt (fun A => aeval A (gPoly c r A)) A₀ :=
  continuousAt_aeval_of_coeff (N := Fintype.card m + 1) A₀
    (fun A => by rw [natDegree_gPoly]; exact Nat.lt_succ_of_le (card_outside_le c r A))
    (continuousAt_coeff_gPoly c r A₀ hcirc)

theorem continuousAt_R (u₀ v₀ : ℂ[X]) (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r) :
    ContinuousAt (fun A => aeval A (u₀ * fPoly c r A + v₀ * gPoly c r A)) A₀ := by
  have e : (fun A : Matrix m m ℂ => aeval A (u₀ * fPoly c r A + v₀ * gPoly c r A))
      = fun A => aeval A u₀ * aeval A (fPoly c r A) + aeval A v₀ * aeval A (gPoly c r A) :=
    funext fun A => by rw [map_add, map_mul, map_mul]
  rw [e]
  exact ((Polynomial.continuous_aeval (p := u₀)).continuousAt.mul
    (continuousAt_aeval_fPoly c r A₀ hcirc)).add
    ((Polynomial.continuous_aeval (p := v₀)).continuousAt.mul
      (continuousAt_aeval_gPoly c r A₀ hcirc))

theorem continuousAt_inv_of_det {R : Matrix m m ℂ → Matrix m m ℂ} {A₀ : Matrix m m ℂ}
    (hR : ContinuousAt R A₀) (hdet : (R A₀).det ≠ 0) : ContinuousAt (fun A => (R A)⁻¹) A₀ := by
  have e : (fun A => (R A)⁻¹) = fun A => (R A).det⁻¹ • (R A).adjugate :=
    funext fun A => by rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [e]
  exact (((continuous_id.matrix_det).continuousAt.comp hR).inv₀ hdet).smul
    ((continuous_id.matrix_adjugate).continuousAt.comp hR)

theorem continuousAt_projOf (u₀ v₀ : ℂ[X]) (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r)
    (hdet : (aeval A₀ (u₀ * fPoly c r A₀ + v₀ * gPoly c r A₀)).det ≠ 0) :
    ContinuousAt (projOf c r u₀ v₀) A₀ := by
  have e : (projOf c r u₀ v₀ : Matrix m m ℂ → Matrix m m ℂ)
      = fun A : Matrix m m ℂ => aeval A v₀ * aeval A (gPoly c r A)
        * (aeval A (u₀ * fPoly c r A + v₀ * gPoly c r A))⁻¹ :=
    funext fun A => by
      unfold projOf
      rw [map_mul (aeval A) v₀ (gPoly c r A)]
  rw [e]
  exact ((Polynomial.continuous_aeval (p := v₀)).continuousAt.mul
    (continuousAt_aeval_gPoly c r A₀ hcirc)).mul
    (continuousAt_inv_of_det (continuousAt_R c r u₀ v₀ A₀ hcirc) hdet)

/-! ### The neighbourhood -/

theorem card_filter_map {n : ℕ} (Pred : ℂ → Prop) [DecidablePred Pred] (x : Fin n → ℂ) :
    Multiset.card ((Finset.univ.val.map x).filter Pred)
      = (Finset.univ.filter fun i => Pred (x i)).card := by
  rw [Multiset.filter_map, Multiset.card_map, Finset.card_def, Finset.filter_val]
  rfl

/-- **Near `A₀` no eigenvalue crosses the circle, and the number inside is constant.** -/
theorem eventually_circle (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r) :
    ∀ᶠ A in 𝓝 A₀, (∀ z ∈ A.charpoly.roots, dist z c ≠ r) ∧
      Multiset.card (inside c r A) = Multiset.card (inside c r A₀) := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Fintype.card m = N := ⟨_, rfl⟩
  obtain ⟨ε₀, hε₀, hsep⟩ := exists_circle_separation c r A₀ hcirc
  obtain ⟨δ, hδ, hδ'⟩ := RootsContinuity.exists_delta_roots_close (n := N) (p := A₀.charpoly)
    (ε := ε₀ / 2) (by positivity)
  have hcoef : ∀ᶠ A in 𝓝 A₀, ∀ i ∈ Finset.range (N + 1),
      ‖A.charpoly.coeff i - A₀.charpoly.coeff i‖ < δ := by
    rw [eventually_all_finset]
    intro i _
    have h := (continuous_charpoly_coeff (m := m) i).continuousAt (x := A₀)
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 h)).2 _ hδ
  filter_upwards [hcoef] with A hA
  have hclose : ∀ i, ‖A.charpoly.coeff i - A₀.charpoly.coeff i‖ < δ := by
    intro i
    by_cases hi : i ∈ Finset.range (N + 1)
    · exact hA i hi
    · rw [Finset.mem_range, not_lt] at hi
      rw [coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, hN]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [charpoly_natDegree_eq_dim, hN]; omega), sub_zero,
        norm_zero]
      exact hδ
  obtain ⟨a, b, ha, hb, hab⟩ := hδ' A.charpoly (charpoly_monic A)
    (by rw [charpoly_natDegree_eq_dim, hN]) hclose
  have hbmem : ∀ i, b i ∈ A₀.charpoly.roots := fun i => by
    rw [hb]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  have hdab : ∀ i, dist (a i) (b i) < ε₀ / 2 := fun i => by
    rw [dist_eq_norm]; exact hab i
  constructor
  · intro z hz
    rw [ha] at hz
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    intro h
    have h1 := abs_dist_sub_le (a i) (b i) c
    rw [h, abs_sub_comm] at h1
    have h2 := hsep (b i) (hbmem i)
    linarith [hdab i]
  · rw [inside, inside, ha, hb, card_filter_map, card_filter_map]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    exact stable_inside c r (hsep (b i) (hbmem i)) ((hdab i).trans_le (by linarith))

/-- **The spectral projector, continuous near `A₀`.**  If no eigenvalue of `A₀` lies on the
circle of radius `r` about `c`, there are a neighbourhood `U` of `A₀` and a continuous map
`P : U → Matrix` such that for every `A ∈ U`, `P A` is a projector commuting with `A`, whose
range is `ker f_A(A)` — the sum of the generalised eigenspaces for the eigenvalues in the disc
— and whose kernel is `ker g_A(A)`; and the number of eigenvalues in the disc, with
multiplicity, is that of `A₀`. -/
theorem exists_continuous_projector (A₀ : Matrix m m ℂ)
    (hcirc : ∀ z ∈ A₀.charpoly.roots, dist z c ≠ r) :
    ∃ (U : Set (Matrix m m ℂ)) (P : Matrix m m ℂ → Matrix m m ℂ), U ∈ 𝓝 A₀ ∧
      ContinuousOn P U ∧ ∀ A ∈ U,
        P A * P A = P A ∧ A * P A = P A * A ∧
        aeval A (fPoly c r A) * P A = 0 ∧ aeval A (gPoly c r A) * (1 - P A) = 0 ∧
        (∀ x, aeval A (fPoly c r A) *ᵥ x = 0 → P A *ᵥ x = x) ∧
        (∀ x, aeval A (gPoly c r A) *ᵥ x = 0 → P A *ᵥ x = 0) ∧
        Multiset.card (inside c r A) = Multiset.card (inside c r A₀) := by
  obtain ⟨u₀, v₀, hbez⟩ := isCoprime_fPoly_gPoly c r A₀
  have hR₀ : aeval A₀ (u₀ * fPoly c r A₀ + v₀ * gPoly c r A₀) = 1 := by
    rw [hbez, map_one]
  have hdet₀ : (aeval A₀ (u₀ * fPoly c r A₀ + v₀ * gPoly c r A₀)).det ≠ 0 := by
    rw [hR₀, Matrix.det_one]
    exact one_ne_zero
  have hdet : ∀ᶠ A in 𝓝 A₀, (aeval A (u₀ * fPoly c r A + v₀ * gPoly c r A)).det ≠ 0 :=
    ((continuous_id.matrix_det).continuousAt.comp
      (continuousAt_R c r u₀ v₀ A₀ hcirc)).eventually_ne hdet₀
  refine ⟨{A | (∀ z ∈ A.charpoly.roots, dist z c ≠ r) ∧
      (aeval A (u₀ * fPoly c r A + v₀ * gPoly c r A)).det ≠ 0 ∧
      Multiset.card (inside c r A) = Multiset.card (inside c r A₀)},
    projOf c r u₀ v₀, ?_, ?_, ?_⟩
  · filter_upwards [eventually_circle c r A₀ hcirc, hdet] with A h1 h2
    exact ⟨h1.1, h2, h1.2⟩
  · intro A hA
    exact (continuousAt_projOf c r u₀ v₀ A hA.1 hA.2.1).continuousWithinAt
  · intro A hA
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := proj_spec A (u := u₀) (v := v₀)
      (by rw [map_mul]; exact aeval_fPoly_mul_gPoly c r A) (isUnit_iff_ne_zero.2 hA.2.1)
    exact ⟨h1, h2, h3, h4, h5, h6, hA.2.2⟩

end SpectralProjector
end MorseFloer
