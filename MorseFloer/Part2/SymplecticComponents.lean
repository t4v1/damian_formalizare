import MorseFloer.Part2.HamiltonianSpectrum

/-!
# Proposition 7.1.4: the two pieces of `Sp(2n)⋆` are path-connected

The book derives Proposition 7.1.4 from Lemma 7.1.5 (perturbing a symplectic
matrix to one with distinct eigenvalues).  This file proves it by another
route, which needs neither distinct eigenvalues nor complex eigenvectors:

1. **Cayley transform.**  `cay M = (M + 1)(M − 1)⁻¹` maps the Hamiltonian
   matrices without the eigenvalue `1` into `Sp(2n)⋆`, and every `A ∈ Sp(2n)⋆`
   is `cay M` for `M = (A + 1)(A − 1)⁻¹` (`cayInv_spec`).  A path of such
   Hamiltonian matrices therefore gives a path in `Sp(2n)⋆` (`joinedIn_cay`).
2. **Spectral normalisation** (`HamiltonianSpectrum.lean`): `M` is joined by a
   segment to a Hamiltonian `N` with `N³ = 4N`.
3. **Adapted symplectic basis** (`exists_conj_normal`): the eigenspaces
   `L± = ker(N ∓ 2)` are isotropic and dual to each other under `ω`, and
   `L₀ = ker N` is their symplectic complement; a basis of `L₊`, its `ω`-dual
   basis of `L₋` and a symplectic basis of `L₀` (Proposition 5.1.1) form a
   symplectic matrix `T` with `N = T · HN(2P_K) · T⁻¹`, where
   `HN(B) = [[B, 0], [0, −Bᵀ]]` and `P_K` is the diagonal projection onto the
   first `k = dim L₊` coordinates.  Conjugating by `T` stays in the path
   component (`joinedIn_conj`, since `Sp(2n)` is path-connected).
4. **Merging hyperbolic pairs** (`joinedIn_merge`): in two coordinates, the
   block `2·Id₂` of `B` is turned by `2(1−s)·R(πs/2)` into `0`, through
   matrices `B` with `B ± 1` invertible, so two pairs of eigenvalues `±2` of
   `HN(B)` become a complex quadruple and then disappear.  Hence every point of
   `Sp(2n)⋆` is joined in `Sp(2n)⋆` to `cay(0) = −Id` or to
   `W = cay(HN(2P_{\{m₀\}}))`.
5. **Sign.**  `det(cay N − 1)` has the sign of `det(N − 1)`, which is
   `(−3)^{|K|}` for the normal forms; a path in `Sp(2n)⋆` cannot change the
   sign of `det(A − 1)`, so `Sp(2n)⁺` is joined to `−Id` and `Sp(2n)⁻` to `W`.
-/

open scoped Matrix
open Polynomial

namespace MorseFloer
namespace Chapter7

/-! ## The Cayley transform -/

section Cayley

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The Cayley transform `(M + 1)(M − 1)⁻¹`. -/
noncomputable def cay (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ :=
  (M + 1) * (M - 1)⁻¹

theorem cay_sub_one {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (h1 : (M - 1).det ≠ 0) :
    cay M - 1 = (2 : ℝ) • (M - 1)⁻¹ := by
  have hu : IsUnit (M - 1).det := Ne.isUnit h1
  calc cay M - 1 = (M + 1) * (M - 1)⁻¹ - (M - 1) * (M - 1)⁻¹ := by
        rw [cay, Matrix.mul_nonsing_inv _ hu]
    _ = ((M + 1) - (M - 1)) * (M - 1)⁻¹ := by rw [Matrix.sub_mul (M + 1) (M - 1)]
    _ = (2 : ℝ) • (M - 1)⁻¹ := by
        rw [show (M + 1) - (M - 1) = (2 : ℝ) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) by
          rw [two_smul]; abel, Matrix.smul_mul, Matrix.one_mul]

theorem det_cay_sub_one {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (h1 : (M - 1).det ≠ 0) :
    (cay M - 1).det = 2 ^ Fintype.card (l ⊕ l) * ((M - 1).det)⁻¹ := by
  rw [cay_sub_one h1, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

/-- The Cayley transform of a Hamiltonian matrix without the eigenvalue `1` lies
in `Sp(2n)⋆`. -/
theorem cay_mem_symplecticStar {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : IsHam M)
    (h1 : (M - 1).det ≠ 0) : cay M ∈ symplecticStar l := by
  refine ⟨?_, ?_⟩
  · have hu : IsUnit (M - 1).det := Ne.isUnit h1
    have hut : IsUnit (M - 1)ᵀ.det := by rw [Matrix.det_transpose]; exact hu
    have hPQ : (M + 1)ᵀ * Matrix.J l ℝ * (M + 1) = (M - 1)ᵀ * Matrix.J l ℝ * (M - 1) := by
      simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one]
      rw [hM.transpose_mul_J]
      abel
    rw [SymplecticGroup.mem_iff', cay, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
    calc (M - 1)ᵀ⁻¹ * (M + 1)ᵀ * Matrix.J l ℝ * ((M + 1) * (M - 1)⁻¹)
        = (M - 1)ᵀ⁻¹ * ((M + 1)ᵀ * Matrix.J l ℝ * (M + 1)) * (M - 1)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (M - 1)ᵀ⁻¹ * (M - 1)ᵀ * Matrix.J l ℝ * ((M - 1) * (M - 1)⁻¹) := by
          rw [hPQ]; simp only [Matrix.mul_assoc]
      _ = Matrix.J l ℝ := by
          rw [Matrix.nonsing_inv_mul _ hut, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
            Matrix.mul_one]
  · rw [det_cay_sub_one h1]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) (inv_ne_zero h1)

/-- Every `A ∈ Sp(2n)⋆` is the Cayley transform of a Hamiltonian matrix without
the eigenvalue `1`. -/
theorem cayInv_spec {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplecticStar l) :
    IsHam ((A + 1) * (A - 1)⁻¹) ∧ ((A + 1) * (A - 1)⁻¹ - 1).det ≠ 0 ∧
      cay ((A + 1) * (A - 1)⁻¹) = A := by
  have hu : IsUnit (A - 1).det := Ne.isUnit hA.2
  set B := (A - 1)⁻¹ with hBdef
  have hAB : (A - 1) * B = 1 := Matrix.mul_nonsing_inv _ hu
  have hBA : B * (A - 1) = 1 := Matrix.nonsing_inv_mul _ hu
  have hBtAt : Bᵀ * (A - 1)ᵀ = 1 := by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]
  have hAJA : Aᵀ * Matrix.J l ℝ * A = Matrix.J l ℝ := SymplecticGroup.mem_iff'.mp hA.1
  have hbr : (A + 1)ᵀ * Matrix.J l ℝ * (A - 1) + (A - 1)ᵀ * Matrix.J l ℝ * (A + 1) = 0 := by
    simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_one,
      Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one]
    rw [hAJA]
    abel
  have hM1 : (A + 1) * B - 1 = (2 : ℝ) • B := by
    calc (A + 1) * B - 1 = (A + 1) * B - (A - 1) * B := by rw [hAB]
      _ = ((A + 1) - (A - 1)) * B := by rw [Matrix.sub_mul (A + 1) (A - 1)]
      _ = (2 : ℝ) • B := by
          rw [show (A + 1) - (A - 1) = (2 : ℝ) • (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) by
            rw [two_smul]; abel, Matrix.smul_mul, Matrix.one_mul]
  have hBdet : B.det ≠ 0 := by
    rw [hBdef, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]; exact inv_ne_zero hA.2
  refine ⟨?_, ?_, ?_⟩
  · have t1 : Bᵀ * ((A + 1)ᵀ * Matrix.J l ℝ * (A - 1)) * B = ((A + 1) * B)ᵀ * Matrix.J l ℝ := by
      rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]; rw [hAB, Matrix.mul_one]
    have t2 : Bᵀ * ((A - 1)ᵀ * Matrix.J l ℝ * (A + 1)) * B = Matrix.J l ℝ * ((A + 1) * B) := by
      simp only [← Matrix.mul_assoc]; rw [hBtAt, Matrix.one_mul]
    unfold IsHam
    rw [← t1, ← t2, ← Matrix.add_mul, ← Matrix.mul_add, hbr, Matrix.mul_zero, Matrix.zero_mul]
  · rw [hM1, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ two_ne_zero) hBdet
  · have hM2 : (A + 1) * B + 1 = (2 : ℝ) • (A * B) := by
      calc (A + 1) * B + 1 = (A + 1) * B + (A - 1) * B := by rw [hAB]
        _ = ((A + 1) + (A - 1)) * B := by rw [Matrix.add_mul (A + 1) (A - 1)]
        _ = (2 : ℝ) • (A * B) := by
            rw [show (A + 1) + (A - 1) = (2 : ℝ) • A by rw [two_smul]; abel, Matrix.smul_mul]
    have hinv : ((2 : ℝ) • B)⁻¹ = (2 : ℝ)⁻¹ • (A - 1) := by
      apply Matrix.inv_eq_left_inv
      rw [smul_mul_smul_comm, hAB, inv_mul_cancel₀ two_ne_zero, one_smul]
    rw [cay, hM2, hM1, hinv, smul_mul_smul_comm, mul_inv_cancel₀ two_ne_zero, one_smul,
      Matrix.mul_assoc, hBA, Matrix.mul_one]

theorem cay_conj {M T : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hT : IsUnit T.det) :
    cay (T * M * T⁻¹) = T * cay M * T⁻¹ := by
  have e1 : T * M * T⁻¹ + 1 = T * (M + 1) * T⁻¹ := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hT]
  have e2 : T * M * T⁻¹ - 1 = T * (M - 1) * T⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hT]
  rw [cay, cay, e1, e2, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ hT]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc T⁻¹ T, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]

/-- A path of Hamiltonian matrices without the eigenvalue `1` gives a path in
`Sp(2n)⋆`. -/
theorem joinedIn_cay (γ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ) (hγ : ContinuousOn γ unitInterval)
    (hH : ∀ t ∈ unitInterval, IsHam (γ t)) (hd : ∀ t ∈ unitInterval, (γ t - 1).det ≠ 0) :
    JoinedIn (symplecticStar l) (cay (γ 0)) (cay (γ 1)) :=
  joinedIn_of_line (fun t => cay (γ t))
    ((hγ.add continuousOn_const).mul
      (continuousOn_inv_of_det_ne_zero (hγ.sub continuousOn_const) hd)) rfl rfl
    fun t ht => cay_mem_symplecticStar (hH t ht) (hd t ht)

end Cayley

/-! ## The normal forms -/

section Normal

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- `HN B = [[B, 0], [0, −Bᵀ]]`, a Hamiltonian matrix for every `B`. -/
def HN (B : Matrix l l ℝ) : Matrix (l ⊕ l) (l ⊕ l) ℝ := Matrix.fromBlocks B 0 0 (-Bᵀ)

theorem isHam_HN (B : Matrix l l ℝ) : IsHam (HN B) := by
  unfold IsHam HN
  rw [show Matrix.J l ℝ = Matrix.fromBlocks 0 (-1) 1 0 from rfl, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp

theorem det_HN_sub_one (B : Matrix l l ℝ) :
    (HN B - 1).det = (B - 1).det * ((-1) ^ Fintype.card l * (B + 1).det) := by
  have h : HN B - 1 = Matrix.fromBlocks (B - 1) 0 0 (-(Bᵀ + 1)) := by
    ext (i | i) (j | j) <;> simp [HN, Matrix.one_apply, sub_eq_add_neg, add_comm]
  rw [h, Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg,
    show Bᵀ + 1 = (B + 1)ᵀ by rw [Matrix.transpose_add, Matrix.transpose_one],
    Matrix.det_transpose]

omit [DecidableEq l] [Fintype l] in
theorem continuous_HN {X : Type*} [TopologicalSpace X] {B : X → Matrix l l ℝ}
    (hB : Continuous B) : Continuous fun x => HN (B x) :=
  hB.matrix_fromBlocks continuous_const continuous_const hB.matrix_transpose.neg

/-- `2 P_K`, twice the diagonal projection onto the coordinates in `K`. -/
def dK (K : Finset l) : Matrix l l ℝ := Matrix.diagonal fun m => if m ∈ K then 2 else 0

theorem det_HN_dK_sub_one (K : Finset l) : (HN (dK K) - 1).det = (-3 : ℝ) ^ K.card := by
  rw [det_HN_sub_one, dK, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_add,
    Matrix.det_diagonal, Matrix.det_diagonal, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (g := fun m => if m ∈ K then (-3 : ℝ) else 1) fun m _ => by
    split_ifs <;> norm_num, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem det_HN_dK_sub_one_ne_zero (K : Finset l) : (HN (dK K) - 1).det ≠ 0 := by
  rw [det_HN_dK_sub_one]; exact pow_ne_zero _ (by norm_num)

theorem cay_HN_dK_mem (K : Finset l) : cay (HN (dK K)) ∈ symplecticStar l :=
  cay_mem_symplecticStar (isHam_HN _) (det_HN_dK_sub_one_ne_zero K)

theorem det_cay_HN_dK_sub_one (K : Finset l) :
    (cay (HN (dK K)) - 1).det = 2 ^ Fintype.card (l ⊕ l) * ((-3 : ℝ) ^ K.card)⁻¹ := by
  rw [det_cay_sub_one (det_HN_dK_sub_one_ne_zero K), det_HN_dK_sub_one]

/-- `cay 0 = −Id`. -/
theorem cay_HN_dK_empty : cay (HN (dK (∅ : Finset l))) = -1 := by
  have h0 : HN (dK (∅ : Finset l)) = 0 := by
    ext (i | i) (j | j) <;> simp [HN, dK]
  rw [h0, cay, zero_add, zero_sub, Matrix.one_mul]
  apply Matrix.inv_eq_left_inv
  rw [Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, neg_neg]

/-- The first `k` coordinates, for a fixed enumeration of `l`. -/
noncomputable def Kset (l : Type*) [DecidableEq l] [Fintype l] (k : ℕ) : Finset l :=
  Finset.univ.filter fun m => ((Fintype.equivFin l m : Fin (Fintype.card l)) : ℕ) < k

theorem mem_Kset {k : ℕ} {m : l} : m ∈ Kset l k ↔ ((Fintype.equivFin l m : Fin _) : ℕ) < k := by
  simp [Kset]

theorem Kset_zero : Kset l 0 = ∅ := by
  ext m; simp [mem_Kset]

theorem Kset_succ {k : ℕ} (hk : k < Fintype.card l) :
    Kset l (k + 1) = insert ((Fintype.equivFin l).symm ⟨k, hk⟩) (Kset l k) := by
  ext m
  simp only [mem_Kset, Finset.mem_insert, Equiv.eq_symm_apply, Fin.ext_iff]
  omega

theorem notMem_Kset {k : ℕ} (hk : k < Fintype.card l) :
    (Fintype.equivFin l).symm ⟨k, hk⟩ ∉ Kset l k := by
  simp [mem_Kset]

theorem card_Kset {k : ℕ} (hk : k ≤ Fintype.card l) : (Kset l k).card = k := by
  induction k with
  | zero => rw [Kset_zero, Finset.card_empty]
  | succ k ih =>
    rw [Kset_succ (by omega), Finset.card_insert_of_notMem (notMem_Kset (by omega)), ih (by omega)]

end Normal

/-! ## Merging two hyperbolic pairs -/

section Merge

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The block `2·Id₂` at the coordinates `i, j`, turned by `2(1−s) R(πs/2)` into `0`. -/
noncomputable def mergeB (K : Finset l) (i j : l) (s : ℝ) : Matrix l l ℝ :=
  Matrix.diagonal (fun m => if m = i ∨ m = j then 2 * (1 - s) * Real.cos (Real.pi * s / 2)
    else if m ∈ K then 2 else 0) +
  (2 * (1 - s) * Real.sin (Real.pi * s / 2)) • (Matrix.single j i 1 - Matrix.single i j 1)

omit [Fintype l] in
theorem mergeB_zero (K : Finset l) (i j : l) :
    mergeB K i j 0 = dK (insert i (insert j K)) := by
  simp only [mergeB, mul_zero, zero_div, Real.cos_zero, Real.sin_zero, sub_zero, mul_one,
    zero_smul, add_zero, dK, Finset.mem_insert]
  congr 1
  funext m
  split_ifs <;> first | rfl | (exfalso; tauto)

omit [Fintype l] in
theorem mergeB_one {K : Finset l} {i j : l} (hiK : i ∉ K) (hjK : j ∉ K) :
    mergeB K i j 1 = dK K := by
  simp only [mergeB, sub_self, mul_zero, zero_mul, zero_smul, add_zero, dK]
  congr 1
  funext m
  split_ifs with h1 h2 <;> first | rfl | (exfalso; rcases h1 with rfl | rfl <;> tauto)

omit [Fintype l] in
theorem continuous_mergeB (K : Finset l) (i j : l) : Continuous (mergeB K i j) := by
  unfold mergeB
  refine Continuous.add (Continuous.matrix_diagonal (continuous_pi fun m => ?_))
    ((show Continuous fun s : ℝ => 2 * (1 - s) * Real.sin (Real.pi * s / 2) by fun_prop).smul
      continuous_const)
  split_ifs <;> fun_prop

/-- `mergeB − c` is invertible for `c = ±1`. -/
theorem det_mergeB_sub_ne_zero {K : Finset l} {i j : l} (hij : i ≠ j) {s : ℝ} (hs : s ∈ unitInterval) {c : ℝ} (hc : c ^ 2 = 1) :
    (mergeB K i j s - c • 1).det ≠ 0 := by
  set a := 2 * (1 - s)
  set φ := Real.pi * s / 2
  set d : l → ℝ := fun m => if m = i ∨ m = j then a * Real.cos φ else if m ∈ K then 2 else 0
  intro h
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have hcoord : ∀ m, (d m - c) * v m +
      a * Real.sin φ * ((if m = j then v i else 0) - (if m = i then v j else 0)) = 0 := by
    intro m
    have := congrFun hBv m
    simp only [mergeB, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_diagonal,
      Matrix.single_mulVec, Function.update_apply, Pi.zero_apply, one_mul, smul_eq_mul,
      Pi.zero_apply] at this
    simp only [d, a, φ]
    linear_combination this
  -- the coordinates outside `{i, j}` vanish
  have hout : ∀ m, m ≠ i → m ≠ j → v m = 0 := by
    intro m hmi hmj
    have h' := hcoord m
    simp only [d, hmi, hmj, or_self, if_false, sub_zero, mul_zero, add_zero] at h'
    have hne : (if m ∈ K then (2 : ℝ) else 0) - c ≠ 0 := by
      intro h0
      have hc' : c = 2 ∨ c = 0 := by split_ifs at h0 <;> [left; right] <;> linarith
      rcases hc' with rfl | rfl <;> norm_num at hc
    exact (mul_eq_zero.mp h').resolve_left hne
  -- the two coordinates `i, j`
  have hi := hcoord i
  have hj := hcoord j
  simp only [d, true_or, if_true, hij, Ne.symm hij, if_false, or_true] at hi hj
  set α := a * Real.cos φ - c
  set β := a * Real.sin φ
  have hsc := Real.sin_sq_add_cos_sq φ
  have hkey : α ^ 2 + β ^ 2 = (a - c * Real.cos φ) ^ 2 + Real.sin φ ^ 2 := by
    simp only [α, β]
    linear_combination (a ^ 2 - 1) * hsc + (1 - Real.cos φ ^ 2) * hc
  have hpos : 0 < α ^ 2 + β ^ 2 := by
    rcases eq_or_lt_of_le hs.1 with h0 | hs0
    · subst h0
      simp only [α, β, a, φ, mul_zero, zero_div, Real.cos_zero, Real.sin_zero, sub_zero,
        mul_one]
      have : c ≠ 2 := by rintro rfl; norm_num at hc
      have : (2 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm this)
      positivity
    · have hφ : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by have := hs.2; have := Real.pi_pos; simp only [φ]; nlinarith)
      rw [hkey]; positivity
  have hvi : v i = 0 := by
    have : (α ^ 2 + β ^ 2) * v i = 0 := by linear_combination α * hi + β * hj
    exact (mul_eq_zero.mp this).resolve_left hpos.ne'
  have hvj : v j = 0 := by
    have : (α ^ 2 + β ^ 2) * v j = 0 := by linear_combination -β * hi + α * hj
    exact (mul_eq_zero.mp this).resolve_left hpos.ne'
  apply hv
  funext m
  by_cases hmi : m = i
  · rw [hmi, hvi]; rfl
  · by_cases hmj : m = j
    · rw [hmj, hvj]; rfl
    · exact hout m hmi hmj

/-- **Merging.**  Two hyperbolic pairs of eigenvalues `±2` are removed inside
`Sp(2n)⋆`. -/
theorem joinedIn_merge {K : Finset l} {i j : l} (hij : i ≠ j) (hiK : i ∉ K) (hjK : j ∉ K) :
    JoinedIn (symplecticStar l) (cay (HN (dK (insert i (insert j K))))) (cay (HN (dK K))) := by
  have h := joinedIn_cay (fun s => HN (mergeB K i j s))
    (continuous_HN (continuous_mergeB K i j)).continuousOn (fun s _ => isHam_HN _)
    (fun s hs => by
      rw [det_HN_sub_one]
      refine mul_ne_zero ?_ (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_)
      · have := det_mergeB_sub_ne_zero (K := K) hij hs (c := 1) (by norm_num)
        rwa [one_smul] at this
      · have := det_mergeB_sub_ne_zero (K := K) hij hs (c := -1) (by norm_num)
        rwa [neg_one_smul, sub_neg_eq_add] at this)
  simpa only [mergeB_zero, mergeB_one hiK hjK] using h

/-- Every normal form is joined to the one with `k mod 2` pairs. -/
theorem joinedIn_Kset (k : ℕ) (hk : k ≤ Fintype.card l) :
    JoinedIn (symplecticStar l) (cay (HN (dK (Kset l k)))) (cay (HN (dK (Kset l (k % 2))))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · rw [Nat.mod_eq_of_lt hk2]; exact JoinedIn.refl (cay_HN_dK_mem _)
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      have e : Kset l (k' + 2) = insert ((Fintype.equivFin l).symm ⟨k' + 1, by omega⟩)
          (insert ((Fintype.equivFin l).symm ⟨k', by omega⟩) (Kset l k')) := by
        rw [Kset_succ (by omega), Kset_succ (by omega)]
      rw [e, show (k' + 2) % 2 = k' % 2 by omega]
      refine (joinedIn_merge ?_ ?_ ?_).trans (ih k' (by omega) (by omega))
      · simp [Fin.ext_iff]
      · simp [mem_Kset]
      · simp [mem_Kset]

end Merge

/-! ## Sign of `det(A − 1)` along a path in `Sp(2n)⋆` -/

section Sign

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem isOpen_det_sub_one_pos :
    IsOpen {X : Matrix (l ⊕ l) (l ⊕ l) ℝ | 0 < (X - 1).det} :=
  isOpen_lt continuous_const (continuous_id.sub continuous_const).matrix_det

theorem isOpen_det_sub_one_neg :
    IsOpen {X : Matrix (l ⊕ l) (l ⊕ l) ℝ | (X - 1).det < 0} :=
  isOpen_lt (continuous_id.sub continuous_const).matrix_det continuous_const

theorem joinedIn_plus_of_star {A B : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (h : JoinedIn (symplecticStar l) A B) (hA : A ∈ symplecticPlus l) :
    JoinedIn (symplecticPlus l) A B := by
  obtain ⟨γ, hγ⟩ := h
  have hsub : Set.range γ ⊆ {X : Matrix (l ⊕ l) (l ⊕ l) ℝ | 0 < (X - 1).det} := by
    refine (isConnected_range γ.continuous).isPreconnected.subset_left_of_subset_union
      isOpen_det_sub_one_pos isOpen_det_sub_one_neg ?_ ?_ ⟨A, ⟨0, γ.source⟩, hA.2⟩
    · rw [Set.disjoint_left]; intro X h1 h2
      exact lt_asymm (show (X - 1).det < 0 from h2) (show 0 < (X - 1).det from h1)
    · rintro _ ⟨t, rfl⟩
      rcases lt_or_gt_of_ne (hγ t).2 with h | h
      · exact Or.inr h
      · exact Or.inl h
  exact ⟨γ, fun t => ⟨(hγ t).1, hsub ⟨t, rfl⟩⟩⟩

theorem joinedIn_minus_of_star {A B : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (h : JoinedIn (symplecticStar l) A B) (hA : A ∈ symplecticMinus l) :
    JoinedIn (symplecticMinus l) A B := by
  obtain ⟨γ, hγ⟩ := h
  have hsub : Set.range γ ⊆ {X : Matrix (l ⊕ l) (l ⊕ l) ℝ | (X - 1).det < 0} := by
    refine (isConnected_range γ.continuous).isPreconnected.subset_left_of_subset_union
      isOpen_det_sub_one_neg isOpen_det_sub_one_pos ?_ ?_ ⟨A, ⟨0, γ.source⟩, hA.2⟩
    · rw [Set.disjoint_left]; intro X h1 h2
      exact lt_asymm (show (X - 1).det < 0 from h1) (show 0 < (X - 1).det from h2)
    · rintro _ ⟨t, rfl⟩
      rcases lt_or_gt_of_ne (hγ t).2 with h | h
      · exact Or.inl h
      · exact Or.inr h
  exact ⟨γ, fun t => ⟨(hγ t).1, hsub ⟨t, rfl⟩⟩⟩

end Sign

/-! ## The adapted symplectic basis -/

section Adapted

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem stdForm_ham {N : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hN : IsHam N) (x y : (l ⊕ l) → ℝ) :
    Chapter5.stdForm l (N *ᵥ x) y = -Chapter5.stdForm l x (N *ᵥ y) := by
  have h := stdForm_aeval hN X x y
  rwa [aeval_X, aeval_X, Matrix.neg_mulVec, map_neg] at h

/-- Eigenvectors of a Hamiltonian matrix for eigenvalues `a, b` with `a + b ≠ 0`
are `ω`-orthogonal. -/
theorem stdForm_eigen_zero {N : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hN : IsHam N) {x y : (l ⊕ l) → ℝ}
    {a b : ℝ} (hx : N *ᵥ x = a • x) (hy : N *ᵥ y = b • y) (hab : a + b ≠ 0) :
    Chapter5.stdForm l x y = 0 := by
  have h := stdForm_ham hN x y
  rw [hx, hy] at h
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h
  have h' : (a + b) * Chapter5.stdForm l x y = 0 := by linarith
  exact (mul_eq_zero.mp h').resolve_left hab

omit [DecidableEq l] [Fintype l] in
theorem coe_mem_span_basis {W : Submodule ℝ ((l ⊕ l) → ℝ)} {ι : Type*} (bW : Module.Basis ι ℝ W)
    (x : W) : (x : (l ⊕ l) → ℝ) ∈ Submodule.span ℝ (Set.range fun i => (bW i : (l ⊕ l) → ℝ)) := by
  have h := Submodule.mem_map_of_mem (f := W.subtype) (bW.mem_span x)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

/-- A Hamiltonian `N` with `N³ = 4N` is conjugate, by a symplectic matrix, to a
normal form `HN(2 P_K)` with `K` the first `k` coordinates. -/
theorem exists_conj_normal {N : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hN : IsHam N)
    (hcube : N * N * N = (4 : ℝ) • N) :
    ∃ k ≤ Fintype.card l, ∃ T ∈ Matrix.symplecticGroup l ℝ,
      N = T * HN (dK (Kset l k)) * T⁻¹ := by
  classical
  have hform := Chapter5.stdForm_isSymplectic l
  -- the three eigenspaces
  let eig : ℝ → Submodule ℝ ((l ⊕ l) → ℝ) := fun c => LinearMap.ker (Matrix.toLin' (N - c • 1))
  have mem_eig : ∀ (c : ℝ) (x : (l ⊕ l) → ℝ), x ∈ eig c ↔ N *ᵥ x = c • x := by
    intro c x
    simp only [eig, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  have orth : ∀ {a b : ℝ} {x y : (l ⊕ l) → ℝ}, x ∈ eig a → y ∈ eig b → a + b ≠ 0 →
      Chapter5.stdForm l x y = 0 := fun hx hy hab =>
    stdForm_eigen_zero hN ((mem_eig _ _).mp hx) ((mem_eig _ _).mp hy) hab
  -- the spectral projectors
  have hN3 : N * (N * N) = (4 : ℝ) • N := by rw [← Matrix.mul_assoc, hcube]
  set QP := (8 : ℝ)⁻¹ • (N * N + (2 : ℝ) • N) with hQPdef
  set QM := (8 : ℝ)⁻¹ • (N * N - (2 : ℝ) • N) with hQMdef
  set Q0 := 1 - (4 : ℝ)⁻¹ • (N * N) with hQ0def
  have hQP : N * QP = (2 : ℝ) • QP := by
    simp only [hQPdef, Matrix.mul_smul, Matrix.mul_add, hN3]; module
  have hQM : N * QM = (-2 : ℝ) • QM := by
    simp only [hQMdef, Matrix.mul_smul, Matrix.mul_sub, hN3]; module
  have hQ0 : N * Q0 = (0 : ℝ) • Q0 := by
    simp only [hQ0def, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, hN3]; module
  have hsumQ : QP + QM + Q0 = 1 := by simp only [hQPdef, hQMdef, hQ0def]; module
  have hdec : ∀ v : (l ⊕ l) → ℝ, v = QP *ᵥ v + QM *ᵥ v + Q0 *ᵥ v := by
    intro v; rw [← Matrix.add_mulVec, ← Matrix.add_mulVec, hsumQ, Matrix.one_mulVec]
  have hP : ∀ v, QP *ᵥ v ∈ eig 2 := fun v => by
    rw [mem_eig, Matrix.mulVec_mulVec, hQP, Matrix.smul_mulVec]
  have hM : ∀ v, QM *ᵥ v ∈ eig (-2) := fun v => by
    rw [mem_eig, Matrix.mulVec_mulVec, hQM, Matrix.smul_mulVec]
  have h0 : ∀ v, Q0 *ᵥ v ∈ eig 0 := fun v => by
    rw [mem_eig, Matrix.mulVec_mulVec, hQ0, Matrix.smul_mulVec]
  -- nondegeneracy
  have nd1 : ∀ y ∈ eig (-2), (∀ x ∈ eig 2, Chapter5.stdForm l x y = 0) → y = 0 := by
    intro y hy h
    refine hform.eq_zero_of_forall' fun w => ?_
    rw [hdec w, LinearMap.map_add₂, LinearMap.map_add₂, h _ (hP w), orth (hM w) hy (by norm_num),
      orth (h0 w) hy (by norm_num), add_zero, add_zero]
  have nd2 : ∀ x ∈ eig 2, (∀ y ∈ eig (-2), Chapter5.stdForm l x y = 0) → x = 0 := by
    intro x hx h
    refine hform.eq_zero_of_forall fun w => ?_
    rw [hdec w, map_add, map_add, orth hx (hP w) (by norm_num), h _ (hM w),
      orth hx (h0 w) (by norm_num), add_zero, add_zero]
  have nd3 : ∀ x ∈ eig 0, (∀ y ∈ eig 0, Chapter5.stdForm l x y = 0) → x = 0 := by
    intro x hx h
    refine hform.eq_zero_of_forall fun w => ?_
    rw [hdec w, map_add, map_add, orth hx (hP w) (by norm_num), orth hx (hM w) (by norm_num),
      h _ (h0 w), add_zero, add_zero]
  -- the dual basis of `L₋`
  let Bpm : eig 2 →ₗ[ℝ] eig (-2) →ₗ[ℝ] ℝ :=
    (Chapter5.stdForm l).compl₁₂ (eig 2).subtype (eig (-2)).subtype
  have Φinj : Function.Injective Bpm.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact Subtype.ext (nd1 y y.2 fun x hx => LinearMap.congr_fun hy ⟨x, hx⟩)
  have Ψinj : Function.Injective Bpm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (nd2 x x.2 fun y hy => LinearMap.congr_fun hx ⟨y, hy⟩)
  have hdim : Module.finrank ℝ (eig (-2)) = Module.finrank ℝ (eig 2) :=
    le_antisymm ((LinearMap.finrank_le_finrank_of_injective Φinj).trans
      Subspace.dual_finrank_eq.le)
      ((LinearMap.finrank_le_finrank_of_injective Ψinj).trans Subspace.dual_finrank_eq.le)
  have Φsurj : Function.Surjective Bpm.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdim.trans Subspace.dual_finrank_eq.symm)).mp Φinj
  let Φe := LinearEquiv.ofBijective Bpm.flip ⟨Φinj, Φsurj⟩
  set k := Module.finrank ℝ (eig 2) with hkdef
  let b := Module.finBasis ℝ (eig 2)
  let fb := b.dualBasis.map Φe.symm
  have hpair : ∀ i j, Chapter5.stdForm l (b i : (l ⊕ l) → ℝ) (fb j : (l ⊕ l) → ℝ)
      = if i = j then 1 else 0 := by
    intro i j
    have h1 : Bpm.flip (fb j) = b.dualBasis j := by
      rw [Module.Basis.map_apply]; exact Φe.apply_symm_apply _
    calc Chapter5.stdForm l (b i : (l ⊕ l) → ℝ) (fb j : (l ⊕ l) → ℝ)
        = Bpm.flip (fb j) (b i) := rfl
      _ = if i = j then 1 else 0 := by rw [h1, Module.Basis.dualBasis_apply_self]
  -- a symplectic basis of `L₀`
  let ω0 : LinearMap.BilinForm ℝ (eig 0) :=
    (Chapter5.stdForm l).compl₁₂ (eig 0).subtype (eig 0).subtype
  have hω0 : Chapter5.IsSymplecticForm ω0 :=
    ⟨fun x => hform.self_eq_zero x,
      ⟨fun x hx => Subtype.ext (nd3 x x.2 fun y hy => hx ⟨y, hy⟩),
        fun y hy => Subtype.ext (nd3 y y.2 fun x hx => by
          have := hy ⟨x, hx⟩
          rw [hform.skew]
          exact neg_eq_zero.mpr this)⟩⟩
  obtain ⟨ι₀, hι₀, b0, hb0⟩ := Chapter5.exists_isSymplecticBasis ω0 hω0
  -- the adapted family
  let cL : Fin k ⊕ ι₀ → (l ⊕ l) → ℝ :=
    Sum.elim (fun i => (b i : (l ⊕ l) → ℝ)) (fun j => (b0 (Sum.inl j) : (l ⊕ l) → ℝ))
  let cR : Fin k ⊕ ι₀ → (l ⊕ l) → ℝ :=
    Sum.elim (fun i => (fb i : (l ⊕ l) → ℝ)) (fun j => (b0 (Sum.inr j) : (l ⊕ l) → ℝ))
  have pLL : ∀ p q, Chapter5.stdForm l (cL p) (cL q) = 0 := by
    rintro (i | j) (i' | j')
    · exact orth (b i).2 (b i').2 (by norm_num)
    · exact orth (b i).2 (b0 _).2 (by norm_num)
    · exact orth (b0 _).2 (b i').2 (by norm_num)
    · exact hb0.ee j j'
  have pRR : ∀ p q, Chapter5.stdForm l (cR p) (cR q) = 0 := by
    rintro (i | j) (i' | j')
    · exact orth (fb i).2 (fb i').2 (by norm_num)
    · exact orth (fb i).2 (b0 _).2 (by norm_num)
    · exact orth (b0 _).2 (fb i').2 (by norm_num)
    · exact hb0.ff j j'
  have pLR : ∀ p q, Chapter5.stdForm l (cL p) (cR q) = if p = q then 1 else 0 := by
    rintro (i | j) (i' | j')
    · show Chapter5.stdForm l (b i : (l ⊕ l) → ℝ) (fb i' : (l ⊕ l) → ℝ) = _
      simp only [Sum.inl.injEq]
      exact hpair i i'
    · rw [if_neg Sum.inl_ne_inr]
      exact orth (b i).2 (b0 _).2 (by norm_num)
    · rw [if_neg Sum.inr_ne_inl]
      exact orth (b0 _).2 (fb i').2 (by norm_num)
    · by_cases hjj : j = j'
      · subst hjj
        rw [if_pos rfl]
        exact hb0.ef_self j
      · have : (Sum.inr j : Fin k ⊕ ι₀) ≠ Sum.inr j' := by simpa using hjj
        rw [if_neg this]; exact hb0.ef_ne j j' hjj
  -- independence and spanning
  have hli : LinearIndependent ℝ (Sum.elim cL cR) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have eL : ∀ w, Chapter5.stdForm l (∑ a, g a • Sum.elim cL cR a) w
        = ∑ a, g a * Chapter5.stdForm l (Sum.elim cL cR a) w := by
      intro w
      rw [map_sum (Chapter5.stdForm l), LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    have eR : ∀ w, Chapter5.stdForm l w (∑ a, g a • Sum.elim cL cR a)
        = ∑ a, g a * Chapter5.stdForm l w (Sum.elim cL cR a) := by
      intro w
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
    have hL : ∀ q, g (Sum.inl q) = 0 := by
      intro q
      have := eL (cR q)
      rw [hg, map_zero, LinearMap.zero_apply, Fintype.sum_sum_type] at this
      simp only [Sum.elim_inl, Sum.elim_inr, pLR, pRR, mul_zero, Finset.sum_const_zero, add_zero,
        mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      exact this.symm
    have hR : ∀ q, g (Sum.inr q) = 0 := by
      intro q
      have := eR (cL q)
      rw [hg, map_zero, Fintype.sum_sum_type] at this
      simp only [Sum.elim_inl, Sum.elim_inr, pLR, pLL, mul_zero, Finset.sum_const_zero, zero_add,
        mul_ite, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this
      exact this.symm
    rintro (q | q)
    · exact hL q
    · exact hR q
  have hspan : Submodule.span ℝ (Set.range (Sum.elim cL cR)) = ⊤ := by
    refine eq_top_iff.mpr fun v _ => ?_
    have hsub1 : Set.range (fun i => (b i : (l ⊕ l) → ℝ)) ⊆ Set.range (Sum.elim cL cR) := by
      rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl (Sum.inl i), rfl⟩
    have hsub2 : Set.range (fun i => (fb i : (l ⊕ l) → ℝ)) ⊆ Set.range (Sum.elim cL cR) := by
      rintro _ ⟨i, rfl⟩; exact ⟨Sum.inr (Sum.inl i), rfl⟩
    have hsub3 : Set.range (fun i => (b0 i : (l ⊕ l) → ℝ)) ⊆ Set.range (Sum.elim cL cR) := by
      rintro _ ⟨(j | j), rfl⟩
      · exact ⟨Sum.inl (Sum.inr j), rfl⟩
      · exact ⟨Sum.inr (Sum.inr j), rfl⟩
    rw [hdec v]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.span_mono hsub1 (coe_mem_span_basis b ⟨_, hP v⟩)
    · exact Submodule.span_mono hsub2 (coe_mem_span_basis fb ⟨_, hM v⟩)
    · exact Submodule.span_mono hsub3 (coe_mem_span_basis b0 ⟨_, h0 v⟩)
  have hcard1 := hli.fintype_card_le_finrank
  have hcard2 := finrank_range_le_card (R := ℝ) (Sum.elim cL cR)
  rw [Set.finrank, hspan, finrank_top] at hcard2
  rw [Module.finrank_fintype_fun_eq_card] at hcard1 hcard2
  simp only [Fintype.card_sum, Fintype.card_fin] at hcard1 hcard2
  have hcard : k + Fintype.card ι₀ = Fintype.card l := by omega
  have hkle : k ≤ Fintype.card l := by omega
  -- the ordering of the coordinates
  have hK : (Kset l k).card = k := card_Kset hkle
  let e1 : Fin k ≃ {m // m ∈ Kset l k} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, hK])
  let e2 : ι₀ ≃ {m // m ∉ Kset l k} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype_compl, Fintype.card_coe, hK]; omega)
  let σ : Fin k ⊕ ι₀ ≃ l := (Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun m => m ∈ Kset l k)
  have hσL : ∀ i, σ (Sum.inl i) ∈ Kset l k := fun i => (e1 i).2
  have hσR : ∀ j, σ (Sum.inr j) ∉ Kset l k := fun j => (e2 j).2
  -- the symplectic matrix
  let c' : l ⊕ l → (l ⊕ l) → ℝ := Sum.elim (cL ∘ σ.symm) (cR ∘ σ.symm)
  let T : Matrix (l ⊕ l) (l ⊕ l) ℝ := Matrix.of fun r a => c' a r
  have hTcol : ∀ a, T *ᵥ Pi.single a 1 = c' a := by
    intro a; rw [Matrix.mulVec_single_one]; rfl
  have hTsp : T ∈ Matrix.symplecticGroup l ℝ := by
    rw [Chapter5.mem_symplecticGroup_iff_preserves]
    intro X Y
    have hB : (Chapter5.stdForm l).compl₁₂ (Matrix.toLin' T) (Matrix.toLin' T)
        = Chapter5.stdForm l := by
      refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℝ (l ⊕ l)) fun a a' => ?_
      simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply, Matrix.toLin'_apply, hTcol,
        Chapter5.stdForm_single]
      rcases a with m | m <;> rcases a' with m' | m'
      · simp [c', pLL, Matrix.J]
      · simp [c', pLR, Matrix.J, Matrix.one_apply]
      · simp only [c', Sum.elim_inr, Sum.elim_inl, Function.comp_apply]
        rw [hform.skew, pLR]
        by_cases hmm : m = m'
        · subst hmm; simp [Matrix.J]
        · have : σ.symm m' ≠ σ.symm m := fun h => hmm (σ.symm.injective h).symm
          rw [if_neg this]; simp [Matrix.J, hmm]
      · simp [c', pRR, Matrix.J]
    exact LinearMap.congr_fun₂ hB X Y
  -- `N T = T D`
  set d : l → ℝ := fun m => if m ∈ Kset l k then 2 else 0 with hd
  have hD : HN (dK (Kset l k)) = Matrix.diagonal (Sum.elim d fun m => -d m) := by
    rw [HN, dK, Matrix.diagonal_transpose, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]
  have hcolN : ∀ a, N *ᵥ c' a = (Sum.elim d (fun m => -d m) a) • c' a := by
    rintro (m | m)
    · rcases hm : σ.symm m with i | j
      · have hmK : m ∈ Kset l k := by rw [← σ.apply_symm_apply m, hm]; exact hσL i
        simp only [c', Sum.elim_inl, Function.comp_apply, hm, cL, hd, hmK, if_true]
        exact (mem_eig 2 _).mp (b i).2
      · have hmK : m ∉ Kset l k := by rw [← σ.apply_symm_apply m, hm]; exact hσR j
        simp only [c', Sum.elim_inl, Function.comp_apply, hm, cL, hd, hmK, if_false]
        exact (mem_eig 0 _).mp (b0 _).2
    · rcases hm : σ.symm m with i | j
      · have hmK : m ∈ Kset l k := by rw [← σ.apply_symm_apply m, hm]; exact hσL i
        simp only [c', Sum.elim_inr, Function.comp_apply, hm, cR, hd, hmK, if_true]
        exact (mem_eig (-2) _).mp (fb i).2
      · have hmK : m ∉ Kset l k := by rw [← σ.apply_symm_apply m, hm]; exact hσR j
        simp only [c', Sum.elim_inr, Function.comp_apply, hm, cR, hd, hmK, if_false, neg_zero]
        exact (mem_eig 0 _).mp (b0 _).2
  have hNT : N * T = T * HN (dK (Kset l k)) := by
    rw [hD]
    ext r a
    rw [Matrix.mul_diagonal]
    have h1 := congrFun (hcolN a) r
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    have h2 : (N * T) r a = (N *ᵥ c' a) r := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rfl
    rw [h2, h1, mul_comm]
    rfl
  refine ⟨k, hkle, T, hTsp, ?_⟩
  have hTu : IsUnit T.det := Ne.isUnit (det_ne_zero_of_mem_symplecticGroup hTsp)
  calc N = N * T * T⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTu, Matrix.mul_one]
    _ = T * HN (dK (Kset l k)) * T⁻¹ := by rw [hNT]

end Adapted

/-! ## Proposition 7.1.4 -/

section Components

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- Every point of `Sp(2n)⋆` is joined inside `Sp(2n)⋆` to `cay(HN(2P_K))` with
`|K| ≤ 1`. -/
theorem exists_joinedIn_normal {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplecticStar l) :
    ∃ k < 2, JoinedIn (symplecticStar l) A (cay (HN (dK (Kset l k)))) := by
  obtain ⟨hM, h1, hcay⟩ := cayInv_spec hA
  set M := (A + 1) * (A - 1)⁻¹
  obtain ⟨N, hNham, hcube, hpath⟩ := exists_normal_path hM h1
  have j1 : JoinedIn (symplecticStar l) (cay M) (cay N) := by
    have h := joinedIn_cay (fun t => (1 - t) • M + t • N)
      (show Continuous fun t : ℝ => (1 - t) • M + t • N by fun_prop).continuousOn
      (fun t _ => (hM.smul _).add (hNham.smul _)) hpath
    simpa using h
  obtain ⟨k, hk, T, hT, hNT⟩ := exists_conj_normal hNham hcube
  have hTu : IsUnit T.det := Ne.isUnit (det_ne_zero_of_mem_symplecticGroup hT)
  have j2 : JoinedIn (symplecticStar l) (cay N) (cay (HN (dK (Kset l k)))) := by
    rw [hNT, cay_conj hTu]
    exact (joinedIn_conj (cay_HN_dK_mem _) hT).symm
  refine ⟨k % 2, Nat.mod_lt _ (by norm_num), ?_⟩
  rw [← hcay]
  exact (j1.trans j2).trans (joinedIn_Kset k hk)

theorem det_W_sub_one_neg [Nonempty l] : (cay (HN (dK (Kset l 1))) - 1).det < 0 := by
  have hn : 0 < Fintype.card l := Fintype.card_pos
  rw [det_cay_HN_dK_sub_one, card_Kset hn, pow_one]
  have : (0 : ℝ) < 2 ^ Fintype.card (l ⊕ l) := by positivity
  nlinarith

/-- **Proposition 7.1.4** (first half).  `Sp(2n)⁺` is path-connected. -/
theorem isPathConnected_symplecticPlus' :
    IsPathConnected (symplecticPlus l) := by
  refine ⟨-1, neg_one_mem_symplecticPlus, fun A hA => ?_⟩
  obtain ⟨k, hk, hj⟩ := exists_joinedIn_normal ⟨hA.1, ne_of_gt hA.2⟩
  have hj' := joinedIn_plus_of_star hj hA
  interval_cases k
  · rw [Kset_zero, cay_HN_dK_empty] at hj'
    exact hj'.symm
  · by_cases hl : Nonempty l
    · have := hl
      exact absurd hj'.mem.2.2 (not_lt.mpr det_W_sub_one_neg.le)
    · have : IsEmpty l := not_nonempty_iff.mp hl
      have hK : Kset l 1 = ∅ := Finset.eq_empty_of_isEmpty _
      rw [hK, cay_HN_dK_empty] at hj'
      exact hj'.symm

/-- **Proposition 7.1.4** (second half).  `Sp(2n)⁻` is path-connected. -/
theorem isPathConnected_symplecticMinus' [Nonempty l] :
    IsPathConnected (symplecticMinus l) := by
  have hW : cay (HN (dK (Kset l 1))) ∈ symplecticMinus l :=
    ⟨(cay_HN_dK_mem _).1, det_W_sub_one_neg⟩
  refine ⟨_, hW, fun A hA => ?_⟩
  obtain ⟨k, hk, hj⟩ := exists_joinedIn_normal ⟨hA.1, ne_of_lt hA.2⟩
  have hj' := joinedIn_minus_of_star hj hA
  interval_cases k
  · exfalso
    have hmem := hj'.mem.2
    rw [Kset_zero, cay_HN_dK_empty] at hmem
    exact absurd hmem.2 (not_lt.mpr neg_one_mem_symplecticPlus.2.le)
  · exact hj'.symm

end Components

/-! ## Lemma 7.1.5: distinct eigenvalues -/

section Distinct

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem posEigenCount_diagonal {ι : Type*} [DecidableEq ι] [Fintype ι] (d : ι → ℝ) :
    posEigenCount (Matrix.diagonal d) = (Finset.univ.filter fun i => 0 < d i).card := by
  have h : (fun i => Polynomial.X - Polynomial.C (d i))
      = (fun a : ℝ => Polynomial.X - Polynomial.C a) ∘ d := rfl
  rw [posEigenCount, Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod, h,
    ← Multiset.map_map, Polynomial.roots_multiset_prod_X_sub_C, Multiset.countP_map]
  rfl

theorem roots_charpoly_diagonal {ι : Type*} [DecidableEq ι] [Fintype ι] (d : ι → ℂ) :
    (Matrix.diagonal d).charpoly.roots = Finset.univ.val.map d := by
  have h : (fun i => Polynomial.X - Polynomial.C (d i))
      = (fun a : ℂ => Polynomial.X - Polynomial.C a) ∘ d := rfl
  rw [Matrix.charpoly_diagonal, Finset.prod_eq_multiset_prod, h, ← Multiset.map_map,
    Polynomial.roots_multiset_prod_X_sub_C]

theorem det_HN_diagonal_sub_one (d : l → ℝ) :
    (HN (Matrix.diagonal d) - 1).det = ∏ m, (1 - d m ^ 2) := by
  rw [det_HN_sub_one, ← Matrix.diagonal_one, Matrix.diagonal_sub, Matrix.diagonal_add,
    Matrix.det_diagonal, Matrix.det_diagonal, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => by ring

omit [Fintype l] in
theorem HN_diagonal (d : l → ℝ) :
    HN (Matrix.diagonal d) = Matrix.diagonal (Sum.elim d fun m => -d m) := by
  rw [HN, Matrix.diagonal_transpose, Matrix.diagonal_neg, Matrix.fromBlocks_diagonal]

/-- The Cayley transform of a diagonal matrix without the entry `1`. -/
theorem cay_diagonal {ι : Type*} [DecidableEq ι] [Fintype ι] (e : ι → ℝ) (he : ∀ a, e a ≠ 1) :
    (Matrix.diagonal e + 1) * (Matrix.diagonal e - 1)⁻¹
      = Matrix.diagonal fun a => (e a + 1) / (e a - 1) := by
  have h1 : Matrix.diagonal e - 1 = Matrix.diagonal fun a => e a - 1 := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_sub]
  have h2 : Matrix.diagonal e + 1 = Matrix.diagonal fun a => e a + 1 := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_add]
  have hinv : (Matrix.diagonal fun a => e a - 1)⁻¹ = Matrix.diagonal fun a => (e a - 1)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (he a))
  rw [h1, h2, hinv, Matrix.diagonal_mul_diagonal]
  rfl

/-- Distinct positive weights in `(0, 1)`. -/
noncomputable def wt (l : Type*) [Fintype l] (m : l) : ℝ :=
  (((Fintype.equivFin l m : Fin (Fintype.card l)) : ℕ) + 1 : ℝ) / (Fintype.card l + 1)

omit [DecidableEq l] in
theorem wt_pos (m : l) : 0 < wt l m := by unfold wt; positivity

omit [DecidableEq l] in
theorem wt_lt_one (m : l) : wt l m < 1 := by
  unfold wt
  rw [div_lt_one (by positivity)]
  have := (Fintype.equivFin l m).isLt
  have : ((Fintype.equivFin l m : Fin (Fintype.card l)) : ℝ) < Fintype.card l := by
    exact_mod_cast this
  linarith

omit [DecidableEq l] in
theorem wt_injective : Function.Injective (wt l) := by
  intro m m' h
  unfold wt at h
  rw [div_left_inj' (by positivity), add_left_inj, Nat.cast_inj] at h
  exact (Fintype.equivFin l).injective (Fin.ext h)

/-- The diagonal entries of the path: `2` on `K`, `t · wt` elsewhere. -/
noncomputable def bt (K : Finset l) (t : ℝ) (m : l) : ℝ := if m ∈ K then 2 else t * wt l m

theorem card_Kset_le_one {k : ℕ} (hk : k < 2) : (Kset l k).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  rw [mem_Kset] at ha hb
  exact (Fintype.equivFin l).injective (Fin.ext (by omega))

/-- **Lemma 7.1.5.**  Every `A ∈ Sp(2n)⋆` is joined inside `Sp(2n)⋆` to a
symplectic matrix with pairwise distinct eigenvalues, none of them positive if
`A ∈ Sp(2n)⁺`, exactly two if `A ∈ Sp(2n)⁻`.  The endpoint is the Cayley
transform of a diagonal Hamiltonian matrix `diag(b, −b)` with the entries of `b`
distinct, one of them `2` in the second case, the others in `(0, 1)`. -/
theorem exists_joinedIn_distinct {A : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hA : A ∈ symplecticStar l) :
    ∃ B ∈ symplecticStar l, JoinedIn (symplecticStar l) A B ∧
      (B.map (fun r : ℝ => (r : ℂ))).charpoly.roots.Nodup ∧
      ((A ∈ symplecticPlus l ∧ posEigenCount B = 0) ∨
        (A ∈ symplecticMinus l ∧ posEigenCount B = 2)) := by
  obtain ⟨k, hk, hj⟩ := exists_joinedIn_normal hA
  set K := Kset l k with hKdef
  have hKc : K.card ≤ 1 := card_Kset_le_one hk
  -- the path of diagonal normal forms
  have hbt0 : Matrix.diagonal (bt K 0) = dK K := by
    rw [dK]; congr 1; funext m; simp [bt]
  have hsq : ∀ t ∈ unitInterval, ∀ m, 1 - bt K t m ^ 2 ≠ 0 := by
    intro t ht m
    unfold bt
    split_ifs
    · norm_num
    · have h1 := wt_pos m
      have h2 := wt_lt_one m
      have : t * wt l m < 1 := by nlinarith [ht.1, ht.2]
      have : 0 ≤ t * wt l m := mul_nonneg ht.1 h1.le
      nlinarith
  have j2 := joinedIn_cay (fun t => HN (Matrix.diagonal (bt K t)))
    (continuous_HN (Continuous.matrix_diagonal (continuous_pi fun m => by
      unfold bt; split_ifs <;> fun_prop))).continuousOn
    (fun t _ => isHam_HN _)
    (fun t ht => by
      rw [det_HN_diagonal_sub_one]
      exact Finset.prod_ne_zero_iff.mpr fun m _ => hsq t ht m)
  simp only [hbt0] at j2
  set b := bt K 1 with hb
  set e : l ⊕ l → ℝ := Sum.elim b fun m => -b m with he
  have hbpos : ∀ m, 0 < b m := fun m => by
    simp only [hb, bt]; split_ifs
    · norm_num
    · rw [one_mul]; exact wt_pos m
  have hb2 : ∀ m, m ∈ K → b m = 2 := fun m hm => by simp [hb, bt, hm]
  have hbw : ∀ m, m ∉ K → b m = wt l m := fun m hm => by simp [hb, bt, hm]
  have he1 : ∀ a, e a ≠ 1 := by
    rintro (m | m)
    · by_cases hm : m ∈ K
      · simp [he, hb2 m hm]
      · have := wt_lt_one m
        simp only [he, Sum.elim_inl, hbw m hm]; exact ne_of_lt this
    · have := hbpos m
      simp only [he, Sum.elim_inr]; intro h; linarith
  set c : l ⊕ l → ℝ := fun a => (e a + 1) / (e a - 1) with hc
  have hB : cay (HN (Matrix.diagonal b)) = Matrix.diagonal c := by
    rw [cay, HN_diagonal]; exact cay_diagonal e he1
  refine ⟨cay (HN (Matrix.diagonal b)), (hj.trans j2).mem.2, hj.trans j2, ?_, ?_⟩
  · -- distinct eigenvalues
    rw [hB, Matrix.diagonal_map (by simp), roots_charpoly_diagonal]
    refine Multiset.Nodup.map ?_ Finset.univ.nodup
    refine Complex.ofReal_injective.comp ?_
    -- `c` is injective
    have hmob : Function.Injective e := by
      have hbinj : Function.Injective b := by
        intro m m' h
        by_cases hm : m ∈ K <;> by_cases hm' : m' ∈ K
        · exact Finset.card_le_one.mp hKc m hm m' hm'
        · rw [hb2 m hm, hbw m' hm'] at h; have := wt_lt_one m'; linarith
        · rw [hbw m hm, hb2 m' hm'] at h; have := wt_lt_one m; linarith
        · rw [hbw m hm, hbw m' hm'] at h; exact wt_injective h
      rintro (m | m) (m' | m') h
      · simp only [he, Sum.elim_inl] at h; rw [hbinj h]
      · simp only [he, Sum.elim_inl, Sum.elim_inr] at h
        have := hbpos m; have := hbpos m'; linarith
      · simp only [he, Sum.elim_inl, Sum.elim_inr] at h
        have := hbpos m; have := hbpos m'; linarith
      · simp only [he, Sum.elim_inr, neg_inj] at h; rw [hbinj h]
    intro a a' h
    apply hmob
    simp only [hc] at h
    have h1 := sub_ne_zero.mpr (he1 a)
    have h2 := sub_ne_zero.mpr (he1 a')
    rw [div_eq_div_iff h1 h2] at h
    linarith
  · -- the count of positive eigenvalues, decided by the sign of `det(A − 1)`
    have hcount : posEigenCount (cay (HN (Matrix.diagonal b))) = 2 * K.card := by
      rw [hB, posEigenCount_diagonal, Finset.card_filter, Fintype.sum_sum_type]
      have hpos : ∀ m, (if 0 < c (Sum.inl m) then 1 else 0) = (if m ∈ K then 1 else 0) ∧
          (if 0 < c (Sum.inr m) then 1 else 0) = (if m ∈ K then 1 else 0) := by
        intro m
        by_cases hm : m ∈ K
        · simp only [hc, he, Sum.elim_inl, Sum.elim_inr, hb2 m hm, hm, if_true]
          norm_num
        · have h1 := wt_pos m
          have h2 := wt_lt_one m
          simp only [hc, he, Sum.elim_inl, Sum.elim_inr, hbw m hm, hm, if_false]
          constructor
          · rw [if_neg]; rw [not_lt]
            exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
          · rw [if_neg]; rw [not_lt]
            exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      rw [Finset.sum_congr rfl fun m _ => (hpos m).1, Finset.sum_congr rfl fun m _ => (hpos m).2,
        Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simp only [Nat.cast_id]
      ring
    have hdet : (cay (HN (Matrix.diagonal b)) - 1).det
        = 2 ^ Fintype.card (l ⊕ l) * (∏ m, (1 - b m ^ 2))⁻¹ := by
      have hne : (HN (Matrix.diagonal b) - 1).det ≠ 0 := by
        rw [det_HN_diagonal_sub_one]
        exact Finset.prod_ne_zero_iff.mpr fun m _ => hsq 1 ⟨zero_le_one, le_rfl⟩ m
      rw [det_cay_sub_one hne, det_HN_diagonal_sub_one]
    have hprod : ∏ m, (1 - b m ^ 2)
        = (-3 : ℝ) ^ K.card * ∏ m ∈ Finset.univ.filter (fun m => m ∉ K), (1 - wt l m ^ 2) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => m ∈ K),
        Finset.filter_mem_eq_inter, Finset.univ_inter,
        Finset.prod_congr rfl fun m hm => by rw [hb2 m hm],
        Finset.prod_const]
      congr 1
      · norm_num
      · exact Finset.prod_congr rfl fun m hm => by
          rw [hbw m (Finset.mem_filter.mp hm).2]
    have hQ : 0 < ∏ m ∈ Finset.univ.filter (fun m => m ∉ K), (1 - wt l m ^ 2) :=
      Finset.prod_pos fun m _ => by
        have := wt_pos m; have := wt_lt_one m; nlinarith
    have h2pos : (0 : ℝ) < 2 ^ Fintype.card (l ⊕ l) := by positivity
    have hjoin := hj.trans j2
    rcases lt_or_gt_of_ne hA.2 with hneg | hpos
    · -- `A ∈ Sp(2n)⁻`
      right
      refine ⟨⟨hA.1, hneg⟩, ?_⟩
      have hBneg := (joinedIn_minus_of_star hjoin ⟨hA.1, hneg⟩).mem.2.2
      rw [hdet, hprod] at hBneg
      rw [hcount]
      interval_cases hcard : K.card
      · exfalso
        rw [pow_zero, one_mul] at hBneg
        have := mul_pos h2pos (inv_pos.mpr hQ)
        linarith
      · rfl
    · left
      refine ⟨⟨hA.1, hpos⟩, ?_⟩
      have hBpos := (joinedIn_plus_of_star hjoin ⟨hA.1, hpos⟩).mem.2.2
      rw [hdet, hprod] at hBpos
      rw [hcount]
      interval_cases hcard : K.card
      · rfl
      · exfalso
        simp only [pow_one] at hBpos
        have : (0 : ℝ) < ((-3) * ∏ m ∈ Finset.univ.filter (fun m => m ∉ K), (1 - wt l m ^ 2))⁻¹ :=
          pos_of_mul_pos_right hBpos h2pos.le
        rw [inv_pos] at this
        nlinarith

end Distinct

end Chapter7
end MorseFloer
