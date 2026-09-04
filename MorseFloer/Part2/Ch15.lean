import MorseFloer.Part1.Ch4

/-!
# Chapter 15: A little algebraic topology

Formalization of Chapter 15 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part II, printed pages 505–509).

This is the book's appendix of algebraic prerequisites.  It has three parts:

* **§15.1.a** the Künneth formula over `Z/2` — more generally over a field:
  the homology of a tensor product of complexes is the tensor product of the
  homologies (Proposition 15.1.1), with Remark 15.1.2 pointing out that the
  proof really uses that the complexes are complexes of *vector spaces*, since
  it splits off a complement of `Ker ∂`;
* **§15.1.b** a short exact sequence of complexes induces an exact sequence
  `Hₖ(A) → Hₖ(B) → Hₖ(C)`, and the failure of injectivity and surjectivity at
  the two ends is measured by a long exact sequence with a connecting morphism
  `∂ : Hₖ(C) → Hₖ₋₁(A)`, whose construction the book spells out;
* **§15.2** the first Chern class `c₁(E) = e(Λⁿ E) ∈ H²(W; Z)` of a complex
  vector bundle, and the remark that `c₁(TW)` of a symplectic manifold is well
  defined because the calibrated almost complex structures form a contractible,
  hence connected, set while `H²(W; Z)` is discrete.

## The model used here

Chapter 3 builds the Morse complex from *based* data: a finite set `Crit` of
critical points, a degree function `ind` and a count function `cnt`, with
`Chains R ind k` the free module on the critical points of index `k`.  A tensor
product of two such complexes is again of the same shape: the critical points of
`C ⊗ D` are the pairs, the degree is `Ind(a,a') = Ind a + Ind a'` and the
differential is `∂ ⊗ 1 + 1 ⊗ ∂`.  That is exactly Chapter 4's `prodIndex` and
`prodCount`, so §15.1.a is formalized in the based model, which is faithful
because the Morse complexes the book applies Künneth to carry a canonical basis.
A basis-free formulation would have to build `(C ⊗ D)ₙ = ⨁_{i+j=n} Cᵢ ⊗ Dⱼ` as a
dependent direct sum over `{(i,j) | i + j = n}`; Mathlib has no Künneth theorem
to plug into (a search of this checkout for `Kunneth` returns nothing), so
nothing would be gained by paying for that bookkeeping.

## What is proved

* `sum_critSet_eq`, `sum_critSet_prod`, `numCrit_eq_sum` — the bookkeeping that
  turns a sum over the critical points of a fixed index into a sum over all
  critical points, and splits it over a product;
* `numCrit_prodIndex` — **the underlying graded module of Proposition 15.1.1**:
  `dim (C ⊗ D)ₖ = Σ_{i+j=k} dim Cᵢ · dim Dⱼ`, i.e. the tensor product complex
  really is graded by `(C ⊗ D)ₖ = ⨁_{i+j=k} Cᵢ ⊗ Dⱼ`;
* `numCrit_prodIndex_of_isEmpty` — the first bullet of the book's proof,
  `C ⊗ 0 = 0`;
* `tensor_brokenPairs` — **`∂_{C⊗D} ∘ ∂_{C⊗D} = 0`**, so the object §15.1.a
  writes down is a complex.  As the book's footnote and Chapter 4 both note,
  without signs this needs characteristic `2`: the two cross terms
  `(∂ ⊗ 1)(1 ⊗ ∂)` and `(1 ⊗ ∂)(∂ ⊗ 1)` are equal, and cancel only because
  `2 = 0`.  This is exactly Chapter 4's `brokenPairs_prod`, which is `sorry`
  there and proved here;
* `betti_prod_of_count_zero` — **Proposition 15.1.1 in the case both
  differentials vanish**, which is the case of every example computed in the
  book (the round sphere, the torus, `ℂPⁿ`, `Pⁿ(ℝ)`: all their mod `2`
  differentials are zero), and where it reduces to `numCrit_prodIndex`;
* `exists_isCompl_ker`, `injective_domRestrict_of_isCompl` — **Remark 15.1.2**:
  over a field `Ker ∂` has a complement and `∂` is injective on it.  This is the
  one step of the book's induction that fails over a ring, and it is Mathlib's
  `Submodule.exists_isCompl`;
* `connecting`, `homologySequence_exact₁/₂/₃` — **§15.1.b**, the long exact
  sequence of a short exact sequence of chain complexes of modules.  Mathlib has
  this (`CategoryTheory.ShortComplex.ShortExact.δ` and the snake lemma), so the
  content here is the specialisation to `ChainComplex (ModuleCat R) ℕ`, the
  category in which Chapter 3's `morseComplex` lives;
* `exists_connecting` — the explicit construction of `∂` that the book gives:
  lift a cycle `c` of `C` to `b ∈ B`, push `∂b` down to a unique `a ∈ A`, and
  check `a` is a cycle.  Proved from scratch, since this is the only part of
  §15.1.b the book proves;
* `finrank_exteriorPower_top` — the reason §15.2's definition makes sense: the
  maximal exterior power of a rank `n` space is a line, so `Λⁿ E` is a complex
  line bundle and its Euler class is defined;
* `eq_of_contractible_of_discrete` — **the well-definedness argument of §15.2**:
  a continuous map from a contractible (hence connected) space to a discrete
  space is constant, which is why `c₁(TW)` does not depend on the choice of
  calibrated almost complex structure.

## Stated with `sorry`

* `betti_tensor` — **Proposition 15.1.1** itself, in the form Chapter 4 needs:
  `βₖ(C ⊗ D) = Σ_{i+j=k} βᵢ(C) βⱼ(D)`.  The book proves it by induction on the
  length of the second complex, decomposing `Dⱼ = Ker ∂ ⊕ D'ⱼ` and
  `Dⱼ₋₁ = E'ⱼ₋₁ ⊕ Im ∂` at each step.  In the based model of Chapter 3 such a
  decomposition changes the basis, so running the induction here would first
  require a basis-free notion of a finite-dimensional complex, its tensor
  product, and the direct-sum additivity of homology.  The pieces that *are*
  reachable — the graded dimension count, the splitting of `Ker ∂`, and the case
  of vanishing differentials — are proved above.

## Gaps: results carrying no Lean declaration

* **The first Chern class itself.**  `c₁(E) = c₁(Λⁿ E) = e(Λⁿ E) ∈ H²(W; Z)`
  needs, in this order: complex vector bundles (Mathlib has vector bundles, but
  no exterior power of one), the Euler class of an oriented rank `2` real
  bundle, and `H²(W; Z)`.  None of the last two exists in this Mathlib, and
  singular or Morse cohomology of a manifold is not available either (Chapter 4
  computes the *transposed* complex of abstract count data, not the cohomology
  of a space).  Writing a `def chernClass` would therefore be a fictitious
  statement, so none is given; what is recorded instead are the two facts the
  paragraph actually uses, `finrank_exteriorPower_top` and
  `eq_of_contractible_of_discrete`.
* **`c₁(TW)` for a symplectic manifold.**  Beyond the missing Chern class this
  needs symplectic manifolds, which Chapter 5 records as unstatable (only the
  linear theory is reachable), and the contractibility of the space of
  calibrated almost complex structures, which is Chapter 5's Proposition 5.5.6,
  itself listed there as carrying no Lean statement.
* **§15.2's opening remark** that `H²(W; Z)` can be computed by the Morse
  complex: this is Chapter 4's §4.3 material applied to a manifold, and there is
  no manifold attached to the abstract count data.
-/

open CategoryTheory

namespace MorseFloer
namespace Chapter15

open MorseFloer.Chapter3 MorseFloer.Chapter4

/-! ## §15.1 A little homological algebra

Recall from §15.1 that a complex is a family of modules together with maps
`∂ : Cₖ → Cₖ₋₁` satisfying `∂ ∘ ∂ = 0`.  Chapter 3 provides such an object:
`dLin ind cnt k : Cₖ₊₁ → Cₖ` is the differential attached to a count function
and `BrokenPairs ind cnt` is exactly the condition `∂ ∘ ∂ = 0` (Chapter 3's
`dLin_comp_dLin`). -/

/-! ### Bookkeeping for sums over critical points of a fixed index -/

section Sums

/-- A sum over the critical points of index `m` is the sum over all critical
points of the function extended by zero. -/
theorem sum_critSet_eq {Crit : Type*} [Fintype Crit] {M : Type*} [AddCommMonoid M]
    (ind : Crit → ℕ) (m : ℕ) (f : Crit → M) :
    ∑ c : CritSet ind m, f c.1 = ∑ c : Crit, if ind c = m then f c else 0 := by
  have h1 : ∑ c ∈ Finset.univ.filter (fun c : Crit => ind c = m), f c
      = ∑ c : CritSet ind m, f c.1 :=
    Finset.sum_subtype _ (fun x => by simp) f
  rw [← h1, Finset.sum_filter]

/-- `cₖ(f)`, the number of critical points of index `k`, as a sum of indicators. -/
theorem numCrit_eq_sum {Crit : Type*} [Fintype Crit] (ind : Crit → ℕ) (m : ℕ) :
    numCrit ind m = ∑ c : Crit, if ind c = m then 1 else 0 := by
  have h := sum_critSet_eq ind m (fun _ => (1 : ℕ))
  have h2 : (∑ _c : CritSet ind m, (1 : ℕ)) = numCrit ind m := by
    simp [numCrit, Finset.card_univ]
  rw [← h2]
  exact h

/-- The same for the product complex: a sum over the critical points of `C ⊗ D`
of total degree `m` is a double sum over the two factors, restricted to the
pairs of degrees adding up to `m`.  This is the statement that
`(C ⊗ D)ₘ = ⨁_{i+j=m} Cᵢ ⊗ Dⱼ` (§15.1.a), read on the canonical bases. -/
theorem sum_critSet_prod {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]
    {M : Type*} [AddCommMonoid M] (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) (m : ℕ)
    (f : Crit₁ × Crit₂ → M) :
    ∑ c : CritSet (prodIndex ind₁ ind₂) m, f c.1
      = ∑ c₁ : Crit₁, ∑ c₂ : Crit₂, if ind₁ c₁ + ind₂ c₂ = m then f (c₁, c₂) else 0 := by
  have h := sum_critSet_eq (prodIndex ind₁ ind₂) m f
  rw [Fintype.sum_prod_type] at h
  exact h

private theorem sum_range_ite_mul (k p q : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (if p = i then (1 : ℕ) else 0) * (if q = k - i then 1 else 0))
      = if p + q = k then 1 else 0 := by
  by_cases hp : p ≤ k
  · have h1 : (∑ i ∈ Finset.range (k + 1),
        (if p = i then (1 : ℕ) else 0) * (if q = k - i then 1 else 0))
        = (if p = p then (1 : ℕ) else 0) * (if q = k - p then 1 else 0) :=
      Finset.sum_eq_single p (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h)
    rw [h1, if_pos rfl, one_mul]
    by_cases hq : p + q = k
    · rw [if_pos (show q = k - p by omega), if_pos hq]
    · rw [if_neg (show ¬(q = k - p) by omega), if_neg hq]
  · rw [if_neg (show ¬(p + q = k) by omega)]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [if_neg (show ¬(p = i) by omega), zero_mul]

end Sums

/-! ### §15.1.a The Künneth formula over `Z/2`

The tensor product complex of §15.1.a is, in the based model, Chapter 4's
`prodIndex` (the degree `Ind(a,a') = Ind a + Ind a'`) together with `prodCount`
(the differential `∂ ⊗ 1 + 1 ⊗ ∂`). -/

section Tensor

variable {K : Type*} [Field K] {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]
  [DecidableEq Crit₁] [DecidableEq Crit₂]

/-- **§15.1.a, the graded module underlying `C ⊗ D`.**  The degree `k` part of
the tensor product complex has dimension `Σ_{i+j=k} dim Cᵢ · dim Dⱼ`, which is
the content of `(C ⊗ D)ₖ = ⨁_{i+j=k} Cᵢ ⊗ Dⱼ`. -/
theorem numCrit_prodIndex {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]
    (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) (k : ℕ) :
    numCrit (prodIndex ind₁ ind₂) k
      = ∑ i ∈ Finset.range (k + 1), numCrit ind₁ i * numCrit ind₂ (k - i) := by
  symm
  calc ∑ i ∈ Finset.range (k + 1), numCrit ind₁ i * numCrit ind₂ (k - i)
      = ∑ i ∈ Finset.range (k + 1), (∑ c₁ : Crit₁, if ind₁ c₁ = i then (1 : ℕ) else 0)
          * (∑ c₂ : Crit₂, if ind₂ c₂ = k - i then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun i _ => by rw [numCrit_eq_sum, numCrit_eq_sum]
    _ = ∑ i ∈ Finset.range (k + 1), ∑ c₁ : Crit₁, ∑ c₂ : Crit₂,
          (if ind₁ c₁ = i then (1 : ℕ) else 0) * (if ind₂ c₂ = k - i then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c₁ _ => Finset.mul_sum _ _ _
    _ = ∑ c₁ : Crit₁, ∑ c₂ : Crit₂, ∑ i ∈ Finset.range (k + 1),
          (if ind₁ c₁ = i then (1 : ℕ) else 0) * (if ind₂ c₂ = k - i then (1 : ℕ) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c₁ _ => Finset.sum_comm
    _ = ∑ c₁ : Crit₁, ∑ c₂ : Crit₂, if ind₁ c₁ + ind₂ c₂ = k then (1 : ℕ) else 0 :=
        Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ =>
          sum_range_ite_mul k (ind₁ c₁) (ind₂ c₂)
    _ = numCrit (prodIndex ind₁ ind₂) k := by
        have h := numCrit_eq_sum (prodIndex ind₁ ind₂) k
        rw [Fintype.sum_prod_type] at h
        exact h.symm

omit [DecidableEq Crit₁] [DecidableEq Crit₂] in
/-- **First bullet of the proof of Proposition 15.1.1**: `C ⊗ 0 = 0`. -/
theorem numCrit_prodIndex_of_isEmpty [IsEmpty Crit₂] (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ)
    (k : ℕ) : numCrit (prodIndex ind₁ ind₂) k = 0 := by
  have h : IsEmpty (CritSet (prodIndex ind₁ ind₂) k) := ⟨fun c => IsEmpty.false c.1.2⟩
  exact Fintype.card_eq_zero_iff.mpr h

omit [Fintype Crit₁] [Fintype Crit₂] in
/-- The coefficient of `∂_{C⊗D}` between two basis elements: `∂ ⊗ 1 + 1 ⊗ ∂`
counts a connection in the second factor when the first is unchanged, and one in
the first factor when the second is unchanged. -/
theorem prodCount_apply (cnt₁ : Crit₁ → Crit₁ → K) (cnt₂ : Crit₂ → Crit₂ → K)
    (a₁ b₁ : Crit₁) (a₂ b₂ : Crit₂) :
    prodCount cnt₁ cnt₂ (a₁, a₂) (b₁, b₂)
      = (if a₁ = b₁ then cnt₂ a₂ b₂ else 0) + (if a₂ = b₂ then cnt₁ a₁ b₁ else 0) := rfl

/-- **§15.1.a: the tensor product of two complexes is a complex.**

The differential `∂_{C⊗D} = ∂ ⊗ 1 + 1 ⊗ ∂` of §15.1.a squares to zero.  Expanding
`∂∂` gives four terms: `(∂ ⊗ 1)²` and `(1 ⊗ ∂)²` vanish because `∂` does, while
the two cross terms `(∂ ⊗ 1)(1 ⊗ ∂)` and `(1 ⊗ ∂)(∂ ⊗ 1)` are *equal*, so they
cancel exactly when `2 = 0` in the coefficient field.  That is why the book works
over `Z/2`; over another field one has to insert the Koszul signs.

The proof now lives in Chapter 4 as `brokenPairs_prod` — it was moved there so
that chapter no longer has to assume it — and this is an alias for it. -/
theorem tensor_brokenPairs {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (h₁ : BrokenPairs ind₁ cnt₁) (h₂ : BrokenPairs ind₂ cnt₂) (h2 : (2 : K) = 0) :
    BrokenPairs (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂) :=
  Chapter4.brokenPairs_prod h₁ h₂ h2

end Tensor

/-! ### Proposition 15.1.1 and the cases that are reachable -/

section Kunneth

variable {K : Type*} [Field K] {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]
  [DecidableEq Crit₁] [DecidableEq Crit₂]

omit [Fintype Crit₁] [Fintype Crit₂] in
/-- A complex with vanishing differential tensored with another such has
vanishing differential. -/
theorem prodCount_zero :
    prodCount (fun _ _ => (0 : K)) (fun _ _ => (0 : K))
      = fun (_ _ : Crit₁ × Crit₂) => (0 : K) := by
  funext a b
  simp [prodCount]

/-- **Proposition 15.1.1 (the Künneth formula), for complexes with zero
differential.**  When both differentials vanish the homology is the whole
complex in each degree, and the formula `βₖ(C ⊗ D) = Σ_{i+j=k} βᵢ(C) βⱼ(D)`
reduces to the dimension count `numCrit_prodIndex`.

This covers every example computed in the book, since the mod `2` differential
of the round sphere, of the torus, of `ℂPⁿ` and of `Pⁿ(ℝ)` vanishes; in
particular it gives Corollary 4.2.3 for `T² = S¹ × S¹`. -/
theorem betti_prod_of_count_zero (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) (k : ℕ) :
    betti (prodIndex ind₁ ind₂) (prodCount (fun _ _ => (0 : K)) (fun _ _ => (0 : K))) k
      = ∑ i ∈ Finset.range (k + 1),
          betti ind₁ (fun _ _ => (0 : K)) i * betti ind₂ (fun _ _ => (0 : K)) (k - i) := by
  rw [prodCount_zero, betti_of_count_zero, numCrit_prodIndex]
  exact Finset.sum_congr rfl fun i _ => by
    rw [betti_of_count_zero, betti_of_count_zero]

/-- **Proposition 15.1.1 (the Künneth formula).**  Over a field the homology of
the tensor product complex is the tensor product of the homologies,
`H⋆(C ⊗ D) = H⋆(C) ⊗ H⋆(D)`; on dimensions,
`βₖ(C ⊗ D) = Σ_{i+j=k} βᵢ(C) · βⱼ(D)`.

Not proved.  The book argues by induction on the number of nonzero terms of the
second complex, splitting `Dⱼ = Ker ∂ ⊕ D'ⱼ` and `Dⱼ₋₁ = E'ⱼ₋₁ ⊕ Im ∂` at each
stage and using that homology, the tensor product and the induction hypothesis
are all compatible with direct sums.  Two ingredients are missing here: a
basis-free notion of a complex of finite-dimensional vector spaces (the based
model of Chapter 3 is not stable under the change of basis the splitting
performs) and the additivity of homology along direct sums of complexes, which
Chapter 4 also leaves open as `betti_sumComplex`.  Mathlib has no Künneth
theorem for complexes to appeal to.

Compare `betti_prod_of_count_zero` above, which proves the formula when both
differentials vanish, `numCrit_prodIndex`, which proves it at the level of the
underlying graded vector spaces, and `exists_isCompl_ker`, which supplies the
splitting step the book's Remark 15.1.2 singles out. -/
theorem betti_tensor {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (h₁ : BrokenPairs ind₁ cnt₁) (h₂ : BrokenPairs ind₂ cnt₂) (h2 : (2 : K) = 0) (k : ℕ) :
    betti (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂) k
      = ∑ i ∈ Finset.range (k + 1), betti ind₁ cnt₁ i * betti ind₂ cnt₂ (k - i) := by
  sorry

end Kunneth

/-! ### Remark 15.1.2: where the proof uses a field

The induction of Proposition 15.1.1 splits `Dⱼ` as `Ker ∂` plus a complement, and
`Dⱼ₋₁` as `Im ∂` plus a complement.  Over a general commutative ring neither
splitting exists, which is why the formula fails for integral homology.  Over a
field both do, and the differential is injective on the complement of its
kernel. -/

section Splitting

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **Remark 15.1.2.**  Over a field the kernel of a linear map is a direct
summand: this is the step of the proof of Proposition 15.1.1 that fails over a
ring, and with it the Künneth formula for integral homology. -/
theorem exists_isCompl_ker (f : V →ₗ[K] W) : ∃ S : Submodule K V, IsCompl (LinearMap.ker f) S :=
  Submodule.exists_isCompl _

/-- The complement supplied by `exists_isCompl_ker` is mapped isomorphically onto
the image: `∂` is injective on it.  This is what turns the two-term complex
`0 → D'ⱼ → Im ∂ → 0` of the book's proof into an acyclic complex. -/
theorem injective_domRestrict_of_isCompl (f : V →ₗ[K] W) {S : Submodule K V}
    (h : IsCompl (LinearMap.ker f) S) : Function.Injective (f.domRestrict S) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, hxS⟩ hx
  have hker : x ∈ LinearMap.ker f := hx
  have hmem : x ∈ LinearMap.ker f ⊓ S := ⟨hker, hxS⟩
  rw [h.inf_eq_bot, Submodule.mem_bot] at hmem
  exact Subtype.ext hmem

end Splitting

/-! ## §15.1.b Exact sequences of complexes

A short exact sequence of complexes `0 → A → B → C → 0` induces, in each degree,
an exact sequence `Hₖ(A) → Hₖ(B) → Hₖ(C)`; the induced maps are in general
neither injective nor surjective, and the defect is measured by a long exact
sequence

`… → Hₖ(A) → Hₖ(B) → Hₖ(C) → Hₖ₋₁(A) → …`

Mathlib has all of this for a short exact sequence of complexes in an abelian
category (the connecting morphism is built from the snake lemma), so what is
recorded here is its specialisation to `ChainComplex (ModuleCat R) ℕ`, the
category in which Chapter 3's `morseComplex` lives, and — separately, since it
is the only piece the book actually proves — the elementary construction of the
connecting morphism on representatives. -/

section LongExact

variable {R : Type*} [Ring R] {S : ShortComplex (ChainComplex (ModuleCat R) ℕ)}

/-- **The connecting morphism `∂ : Hₖ₊₁(C) → Hₖ(A)`** of §15.1.b, for a short
exact sequence `0 → A → B → C → 0` of chain complexes of `R`-modules. -/
noncomputable def connecting (hS : S.ShortExact) (k : ℕ) :
    S.X₃.homology (k + 1) ⟶ S.X₁.homology k :=
  hS.δ (k + 1) k rfl

/-- **§15.1.b, the "direct verification".**  A short exact sequence of complexes
induces, in each degree, an exact sequence `Hₖ(A) → Hₖ(B) → Hₖ(C)`. -/
theorem homologySequence_exact₂ (hS : S.ShortExact) (k : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap S.f k) (HomologicalComplex.homologyMap S.g k)
      (by rw [← HomologicalComplex.homologyMap_comp, S.zero,
        HomologicalComplex.homologyMap_zero])).Exact :=
  hS.homology_exact₂ k

/-- **§15.1.b, exactness at `Hₖ(A)`**: the long exact sequence is exact at
`Hₖ₊₁(C) → Hₖ(A) → Hₖ(B)`, which measures the failure of `i⋆` to be injective. -/
theorem homologySequence_exact₁ (hS : S.ShortExact) (k : ℕ) :
    (ShortComplex.mk (connecting hS k) (HomologicalComplex.homologyMap S.f k)
      (ShortComplex.ShortExact.δ_comp hS (k + 1) k rfl)).Exact :=
  hS.homology_exact₁ (k + 1) k rfl

/-- **§15.1.b, exactness at `Hₖ₊₁(C)`**: the long exact sequence is exact at
`Hₖ₊₁(B) → Hₖ₊₁(C) → Hₖ(A)`, which measures the failure of `j⋆` to be
surjective. -/
theorem homologySequence_exact₃ (hS : S.ShortExact) (k : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap S.g (k + 1)) (connecting hS k)
      (ShortComplex.ShortExact.comp_δ hS (k + 1) k rfl)).Exact :=
  hS.homology_exact₃ (k + 1) k rfl

end LongExact

section Connecting

/-- **§15.1.b, the construction of the connecting morphism.**  This is the
diagram chase the book writes out.  Given a short exact sequence of complexes of
modules — `i` injective, `j` surjective, `Ker j = Im i` in each degree, both
commuting with the differentials — and a cycle `c` of `C` in degree `k + 2`:

* `c` lifts to some `b` of `B`, because `j` is surjective;
* `∂b` lies in `Ker j`, because `j(∂b) = ∂(j b) = ∂c = 0`, hence `∂b = i a` for
  some `a` of `A` in degree `k + 1`;
* `a` is a cycle, because `i(∂a) = ∂(i a) = ∂∂b = 0` and `i` is injective.

The class of `a` is then `∂[c]`; the remaining verifications (independence of the
choices, exactness) are the ones §15.1.b calls analogous and direct, and are
supplied by Mathlib through `connecting` above. -/
theorem exists_connecting {R : Type*} [Ring R] {A B C : ℕ → Type*}
    [∀ k, AddCommGroup (A k)] [∀ k, Module R (A k)]
    [∀ k, AddCommGroup (B k)] [∀ k, Module R (B k)]
    [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)]
    (i : ∀ k, A k →ₗ[R] B k) (j : ∀ k, B k →ₗ[R] C k)
    (dA : ∀ k, A (k + 1) →ₗ[R] A k) (dB : ∀ k, B (k + 1) →ₗ[R] B k)
    (dC : ∀ k, C (k + 1) →ₗ[R] C k)
    (hinj : ∀ k, Function.Injective (i k))
    (hsurj : ∀ k, Function.Surjective (j k))
    (hexact : ∀ k, LinearMap.ker (j k) = LinearMap.range (i k))
    (hi : ∀ (k : ℕ) (x : A (k + 1)), dB k (i (k + 1) x) = i k (dA k x))
    (hj : ∀ (k : ℕ) (x : B (k + 1)), dC k (j (k + 1) x) = j k (dB k x))
    (hBB : ∀ (k : ℕ) (x : B (k + 2)), dB k (dB (k + 1) x) = 0)
    (k : ℕ) (c : C (k + 2)) (hc : dC (k + 1) c = 0) :
    ∃ (b : B (k + 2)) (a : A (k + 1)),
      j (k + 2) b = c ∧ i (k + 1) a = dB (k + 1) b ∧ dA k a = 0 := by
  obtain ⟨b, hb⟩ := hsurj (k + 2) c
  have h1 : dB (k + 1) b ∈ LinearMap.ker (j (k + 1)) := by
    have hstep : j (k + 1) (dB (k + 1) b) = dC (k + 1) (j (k + 2) b) := (hj (k + 1) b).symm
    rw [LinearMap.mem_ker, hstep, hb, hc]
  rw [hexact (k + 1)] at h1
  obtain ⟨a, ha⟩ := h1
  refine ⟨b, a, hb, ha, ?_⟩
  have hzero : i k (dA k a) = 0 := by rw [← hi k a, ha, hBB k b]
  exact hinj k (hzero.trans (map_zero (i k)).symm)

end Connecting

/-! ## §15.2 Chern classes

The book defines the first Chern class of a complex vector bundle `E` of rank `n`
over `W` as the Euler class of its maximal exterior power, a complex line bundle:
`c₁(E) = c₁(Λⁿ E) = e(Λⁿ E) ∈ H²(W; Z)`.  It then uses `c₁(TW)` for a symplectic
manifold, `TW` being made a complex vector bundle by an almost complex structure
calibrated by the symplectic form, and observes that the choice does not matter
because the set of such structures is contractible — in particular connected —
while `H²(W; Z)` is discrete.

Neither the Euler class nor `H²(W; Z)` exists in this Mathlib, so `c₁` carries no
Lean declaration (see the gaps in the module docstring).  The two facts on which
the paragraph rests are recorded. -/

section Chern

/-- **§15.2.**  The maximal exterior power of a vector space of dimension `n` is
`1`-dimensional.  Fibrewise, this is why `Λⁿ E` is a *line* bundle, so that the
Euler class defining `c₁(E) = e(Λⁿ E)` makes sense. -/
theorem finrank_exteriorPower_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {n : ℕ} (hn : Module.finrank K V = n) :
    Module.finrank K (⋀[K]^n V) = 1 := by
  rw [exteriorPower.finrank_eq (R := K) (M := V) (n := n), hn, Nat.choose_self]

/-- **§15.2, the well-definedness argument.**  A continuous map from a
contractible — hence connected — space to a discrete space is constant.

Applied with `J` the space of almost complex structures calibrated by the
symplectic form (contractible by Proposition 5.5.6) and with the discrete group
`H²(W; Z)` as target, this is exactly the book's reason why `c₁(TW)` does not
depend on the chosen calibrated almost complex structure. -/
theorem eq_of_contractible_of_discrete {J H : Type*} [TopologicalSpace J] [TopologicalSpace H]
    [DiscreteTopology H] [ContractibleSpace J] (c : J → H) (hc : Continuous c) (J₀ J₁ : J) :
    c J₀ = c J₁ :=
  PreconnectedSpace.constant inferInstance hc

end Chern

end Chapter15
end MorseFloer
