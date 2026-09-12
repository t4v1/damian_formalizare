import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# The Borsuk–Ulam theorem

This file proves, with no `sorry`, that there is no continuous odd map from the unit
sphere `Sⁿ` of `ℝⁿ⁺¹` to the unit sphere `Sⁿ⁻¹` of `ℝⁿ` (`MorseFloer.borsuk_ulam_general`).
It supplies Theorem 4.8.3 of the book, which `Chapter4.borsuk_ulam` states.

The book derives the theorem from the mod `2` homology of projective spaces. This
Mathlib has neither that nor any degree theory, so the proof here is combinatorial: a
Tucker lemma for a fine triangulation of the cube, proved by a parity count in the
spirit of Freund and Todd, followed by an approximation argument. It uses no
algebraic topology.

**Faces of the grid.** A face of the unit cubical grid of `[-m, m]ⁿ` is coded by an
integer vector `c` with `|cᵢ| ≤ 2m`. An even `cᵢ` stands for the point `cᵢ/2` and an odd
`cᵢ` for the interval `[(cᵢ-1)/2, (cᵢ+1)/2]`. `FLE a b` says that `a` is a face of `b`.
Chains of faces are the simplices of the barycentric subdivision of the grid, a
triangulation of the cube that is antipodally symmetric and refines the decomposition
into orthants. A face has a dimension (its number of odd coordinates) and a sign vector
(`sgnSet`, the signs of its nonzero coordinates). The sign vector of a chain `σ` is the
union `sgnS σ` of those of its faces, and `σ` has at most `|sgnS σ| + 1` faces.

**Tucker's lemma** (`BorsukUlam.tucker`). Label every face by one of `±1, …, ±n`,
antipodally on the boundary. Then two comparable faces carry opposite labels. Suppose
not. Call `ρ` a *door* of `τ` when `τ` is `ρ` plus one face and the labels of `ρ` already
contain the sign vector of `τ`, and count the pairs (door, chain) modulo `2` in two ways.

* At the larger chain (`card_down`). A chain has an odd number of doors exactly when it
  is *full* (one more face than sign entries) and its labels are its sign vector plus
  one more label, with the single exception of the chain `{0}`, which has none. This is
  a statement about labelled finite sets (`card_removable`).
* At the door (`card_up`). A full chain with one extra label `ℓ` is a door of exactly one
  chain, obtained by opening coordinate `ℓ` at its top face (`card_up_full`). A *tight*
  chain (as many faces as sign entries) labelled exactly by its sign vector is a door
  of two chains, or of one when it lies in the boundary of the cube (`card_up_tight`).
  This is the pseudomanifold property of each orthant, checked coordinate by
  coordinate according to which dimension the chain misses (`card_comp_bottom`,
  `card_comp_middle`, `card_comp_top`).

Comparing the two counts, the number of tight boundary chains labelled exactly by their
sign vector is odd. But the antipodal map pairs those chains off (`card_isB_even`).

**From Tucker's lemma to the cube** (`BorsukUlam.cube_zero`). A map `F` continuous on the
cube `[-1, 1]ⁿ` (the closed unit ball of the sup norm) and odd on its boundary has a
zero. Otherwise `‖F‖ ≥ δ > 0` there. Label each face by the coordinate where `|F|` is
largest at its barycentre, with the sign of `F` there; this labelling is antipodal on
the boundary. Two comparable faces with opposite labels have barycentres within
`1/(2m)` of each other, yet `F` has a coordinate `≥ δ` at one of them and `≤ -δ` at the
other, which uniform continuity rules out once `m` is large.

**From the cube to spheres** (`borsuk_ulam_general`). The map
`y ↦ (y, 1 - ‖y‖) / ‖(y, 1 - ‖y‖)‖` sends the cube into `Sⁿ` and is odd on the boundary
of the cube, where `1 - ‖y‖` vanishes. Composed with an odd map `Sⁿ → Sⁿ⁻¹` it would give
a map on the cube, odd on its boundary and without zero.
-/

open Finset

namespace MorseFloer
namespace BorsukUlam

/-! ### Combinatorics of the grid -/

/-- The face relation on one doubled coordinate. An even integer `2k` codes the point
`k` and an odd one `2k + 1` the interval `[k, k + 1]`; `CLE x y` says that `x` is a face
of `y`, that is, `x = y` or `x` is an endpoint of the interval `y`. -/
def CLE (x y : ℤ) : Prop := x = y ∨ (y % 2 = 1 ∧ (x = y + 1 ∨ x = y - 1))

instance : DecidableRel CLE := fun _ _ => by unfold CLE; infer_instance

theorem CLE.refl (x : ℤ) : CLE x x := Or.inl rfl

theorem CLE.trans {x y z : ℤ} (h1 : CLE x y) (h2 : CLE y z) : CLE x z := by
  unfold CLE at *; omega

theorem CLE.eq_of_odd {x y : ℤ} (h : CLE x y) (hx : x % 2 = 1) : x = y := by
  unfold CLE at *; omega

theorem CLE.odd {x y : ℤ} (h : CLE x y) (hx : x % 2 = 1) : y % 2 = 1 := by
  unfold CLE at *; omega

theorem CLE.ne_iff {x y : ℤ} (h : CLE x y) : x ≠ y ↔ (y % 2 = 1 ∧ ¬ x % 2 = 1) := by
  unfold CLE at *; omega

theorem CLE.sign {x y : ℤ} (h : CLE x y) (hx : x ≠ 0) : y ≠ 0 ∧ (0 < x ↔ 0 < y) := by
  unfold CLE at *; omega

theorem CLE.eq_of_even_right {x y : ℤ} (h : CLE x y) (hy : ¬ y % 2 = 1) : x = y := by
  unfold CLE at *; omega

theorem CLE.abs_sub {x y : ℤ} (h : CLE x y) : x - y ≤ 1 ∧ y - x ≤ 1 := by
  unfold CLE at *; omega

theorem cle_neg_iff {x y : ℤ} : CLE (-x) (-y) ↔ CLE x y := by
  unfold CLE; omega

variable {n : ℕ}

/-- The face relation on the grid: `a ≤ b` when the face coded by `a` is a face of
the face coded by `b`. -/
def FLE (a b : Fin n → ℤ) : Prop := ∀ i, CLE (a i) (b i)

instance : DecidableRel (FLE (n := n)) := fun _ _ => by unfold FLE; infer_instance

theorem FLE.refl (a : Fin n → ℤ) : FLE a a := fun _ => CLE.refl _

theorem FLE.trans {a b c : Fin n → ℤ} (h1 : FLE a b) (h2 : FLE b c) : FLE a c :=
  fun i => (h1 i).trans (h2 i)

theorem fle_neg_iff {a b : Fin n → ℤ} : FLE (-a) (-b) ↔ FLE a b := by
  simp only [FLE, Pi.neg_apply, cle_neg_iff]

/-- Two faces are comparable. -/
def Comparable (a b : Fin n → ℤ) : Prop := FLE a b ∨ FLE b a

instance : DecidableRel (Comparable (n := n)) := fun _ _ => by unfold Comparable; infer_instance

/-- The coordinates in which a face is an interval. -/
def oddSet (c : Fin n → ℤ) : Finset (Fin n) := univ.filter fun i => c i % 2 = 1

/-- The dimension of a face. -/
def dim (c : Fin n → ℤ) : ℕ := #(oddSet c)

/-- The coordinates in which a face is nonzero. -/
def supp (c : Fin n → ℤ) : Finset (Fin n) := univ.filter fun i => c i ≠ 0

/-- The coordinates in which two faces differ. -/
def diffSet (a b : Fin n → ℤ) : Finset (Fin n) := univ.filter fun i => a i ≠ b i

/-- Signed labels `±1, …, ±n`, coded as a coordinate together with a sign (`true` for
`+`). -/
abbrev Label (n : ℕ) := Fin n × Bool

/-- The opposite label. -/
def opp (ℓ : Label n) : Label n := (ℓ.1, !ℓ.2)

@[simp] theorem opp_opp (ℓ : Label n) : opp (opp ℓ) = ℓ := by
  simp [opp]

/-- The sign vector of a face, as a set of signed labels. -/
def sgnSet (c : Fin n → ℤ) : Finset (Label n) := (supp c).image fun i => (i, decide (0 < c i))

theorem mem_sgnSet {c : Fin n → ℤ} {ℓ : Label n} :
    ℓ ∈ sgnSet c ↔ c ℓ.1 ≠ 0 ∧ ℓ.2 = decide (0 < c ℓ.1) := by
  obtain ⟨i, b⟩ := ℓ
  simp only [sgnSet, supp, mem_image, mem_filter, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, rfl, rfl⟩
    exact ⟨hj, rfl⟩
  · rintro ⟨hi, hb⟩
    exact ⟨i, hi, rfl, hb.symm⟩

theorem card_sgnSet (c : Fin n → ℤ) : #(sgnSet c) = #(supp c) := by
  apply card_image_of_injective
  intro i j h
  exact (Prod.mk.inj h).1

theorem oddSet_subset_supp (c : Fin n → ℤ) : oddSet c ⊆ supp c := by
  intro i hi
  simp only [oddSet, supp, mem_filter, mem_univ, true_and] at hi ⊢
  omega

theorem dim_le_card_sgnSet (c : Fin n → ℤ) : dim c ≤ #(sgnSet c) := by
  rw [card_sgnSet]; exact card_le_card (oddSet_subset_supp c)

theorem FLE.oddSet_subset {a b : Fin n → ℤ} (h : FLE a b) : oddSet a ⊆ oddSet b := by
  intro i hi
  simp only [oddSet, mem_filter, mem_univ, true_and] at hi ⊢
  exact (h i).odd hi

theorem FLE.diffSet_eq {a b : Fin n → ℤ} (h : FLE a b) : diffSet a b = oddSet b \ oddSet a := by
  ext i
  simp only [diffSet, oddSet, mem_filter, mem_univ, true_and, mem_sdiff]
  exact (h i).ne_iff

theorem FLE.card_diffSet {a b : Fin n → ℤ} (h : FLE a b) : #(diffSet a b) + dim a = dim b := by
  rw [h.diffSet_eq, card_sdiff_of_subset h.oddSet_subset]
  have := card_le_card h.oddSet_subset
  unfold dim
  omega

theorem FLE.dim_le {a b : Fin n → ℤ} (h : FLE a b) : dim a ≤ dim b := by
  have := h.card_diffSet; omega

theorem FLE.eq_of_dim_eq {a b : Fin n → ℤ} (h : FLE a b) (hd : dim a = dim b) : a = b := by
  have h1 := h.card_diffSet
  have h2 : diffSet a b = ∅ := card_eq_zero.mp (by omega)
  funext i
  by_contra hi
  have : i ∈ diffSet a b := by simp [diffSet, hi]
  rw [h2] at this
  exact absurd this (notMem_empty i)

theorem FLE.sgnSet_subset {a b : Fin n → ℤ} (h : FLE a b) : sgnSet a ⊆ sgnSet b := by
  intro ℓ hℓ
  rw [mem_sgnSet] at hℓ ⊢
  obtain ⟨h1, h2⟩ := hℓ
  obtain ⟨h3, h4⟩ := (h ℓ.1).sign h1
  refine ⟨h3, ?_⟩
  rw [h2]
  exact decide_eq_decide.mpr h4

theorem Comparable.symm {a b : Fin n → ℤ} (h : Comparable a b) : Comparable b a := Or.symm h

theorem Comparable.fle_of_dim_le {a b : Fin n → ℤ} (h : Comparable a b) (hd : dim a ≤ dim b) :
    FLE a b := by
  rcases h with h | h
  · exact h
  · have := h.dim_le
    have hd' : dim b = dim a := le_antisymm this hd
    rw [h.eq_of_dim_eq hd']
    exact FLE.refl a

theorem Comparable.eq_of_dim_eq {a b : Fin n → ℤ} (h : Comparable a b) (hd : dim a = dim b) :
    a = b := by
  rcases h with h | h
  · exact h.eq_of_dim_eq hd
  · exact (h.eq_of_dim_eq hd.symm).symm

/-- In a face `b` covering `a`, exactly one coordinate changes. -/
theorem FLE.exists_diff_one {a b : Fin n → ℤ} (h : FLE a b) (hd : dim b = dim a + 1) :
    ∃ k, diffSet a b = {k} := by
  apply card_eq_one.mp
  have := h.card_diffSet
  omega

theorem diffSet_comm (a b : Fin n → ℤ) : diffSet a b = diffSet b a := by
  ext i
  simp only [diffSet, mem_filter, mem_univ, true_and, ne_comm]

theorem eq_update_of_diffSet {a b : Fin n → ℤ} {k : Fin n} (h : diffSet a b = {k}) :
    b = Function.update a k (b k) := by
  funext i
  by_cases hik : i = k
  · subst hik; simp
  · rw [Function.update_of_ne hik]
    by_contra hne
    have : i ∈ diffSet a b := by simp [diffSet, Ne.symm hne]
    rw [h, mem_singleton] at this
    exact hik this


/-! ### Chains of faces -/

section Chains

variable (m : ℕ)

/-- A face lies in the grid `[-m, m]ⁿ` (in doubled coordinates, `[-2m, 2m]`). -/
def InGrid (c : Fin n → ℤ) : Prop := ∀ i, -(2 * (m : ℤ)) ≤ c i ∧ c i ≤ 2 * m

/-- A face lies in the boundary of the cube. -/
def IsBdry (c : Fin n → ℤ) : Prop := ∃ i, c i = 2 * (m : ℤ) ∨ c i = -(2 * (m : ℤ))

/-- The finite set of faces of the grid. -/
noncomputable def grid : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Icc (-(2 * (m : ℤ))) (2 * m)

variable {m}

theorem mem_grid {c : Fin n → ℤ} : c ∈ grid m ↔ InGrid m c := by
  simp only [grid, Fintype.mem_piFinset, mem_Icc, InGrid]

/-- A set of faces that are pairwise comparable. -/
def IsChainF (σ : Finset (Fin n → ℤ)) : Prop := ∀ a ∈ σ, ∀ b ∈ σ, Comparable a b

variable (m) in
/-- The nodes of the parity argument: nonempty chains of faces of the grid. -/
def IsNode (σ : Finset (Fin n → ℤ)) : Prop :=
  σ.Nonempty ∧ (∀ c ∈ σ, InGrid m c) ∧ IsChainF σ

instance (σ : Finset (Fin n → ℤ)) : Decidable (IsNode m σ) := by
  unfold IsNode IsChainF InGrid; infer_instance

variable (m) in
/-- The finite set of nodes. -/
noncomputable def nodes : Finset (Finset (Fin n → ℤ)) :=
  (grid (n := n) m).powerset.filter (IsNode m)

theorem mem_nodes {σ : Finset (Fin n → ℤ)} : σ ∈ nodes m ↔ IsNode m σ := by
  simp only [nodes, mem_filter, mem_powerset, and_iff_right_iff_imp]
  intro h c hc
  exact mem_grid.mpr (h.2.1 c hc)

/-- The sign vector of a chain: the union of the sign vectors of its faces. -/
def sgnS (σ : Finset (Fin n → ℤ)) : Finset (Label n) := σ.biUnion sgnSet

theorem sgnSet_subset_sgnS {σ : Finset (Fin n → ℤ)} {c : Fin n → ℤ} (hc : c ∈ σ) :
    sgnSet c ⊆ sgnS σ := subset_biUnion_of_mem sgnSet hc

theorem sgnS_mono {ρ τ : Finset (Fin n → ℤ)} (h : ρ ⊆ τ) : sgnS ρ ⊆ sgnS τ :=
  biUnion_subset_biUnion_of_subset_left _ h

theorem sgnS_insert (G : Fin n → ℤ) (ρ : Finset (Fin n → ℤ)) :
    sgnS (insert G ρ) = sgnSet G ∪ sgnS ρ := biUnion_insert

theorem sgnS_eq_of_top {σ : Finset (Fin n → ℤ)} {T : Fin n → ℤ} (hT : T ∈ σ)
    (htop : ∀ c ∈ σ, FLE c T) : sgnS σ = sgnSet T := by
  apply Subset.antisymm _ (sgnSet_subset_sgnS hT)
  intro ℓ hℓ
  obtain ⟨c, hc, hℓc⟩ := mem_biUnion.mp hℓ
  exact (htop c hc).sgnSet_subset hℓc

theorem IsChainF.subset {σ τ : Finset (Fin n → ℤ)} (h : IsChainF σ) (hτ : τ ⊆ σ) : IsChainF τ :=
  fun a ha b hb => h a (hτ ha) b (hτ hb)

theorem IsChainF.fle_of_dim_le {σ : Finset (Fin n → ℤ)} (h : IsChainF σ) {a b : Fin n → ℤ}
    (ha : a ∈ σ) (hb : b ∈ σ) (hd : dim a ≤ dim b) : FLE a b :=
  (h a ha b hb).fle_of_dim_le hd

theorem IsChainF.injOn_dim {σ : Finset (Fin n → ℤ)} (h : IsChainF σ) :
    Set.InjOn dim (σ : Set (Fin n → ℤ)) :=
  fun a ha b hb hd => (h a ha b hb).eq_of_dim_eq hd

theorem dim_le_card_sgnS {σ : Finset (Fin n → ℤ)} {c : Fin n → ℤ} (hc : c ∈ σ) :
    dim c ≤ #(sgnS σ) :=
  (dim_le_card_sgnSet c).trans (card_le_card (sgnSet_subset_sgnS hc))

theorem IsChainF.card_image_dim {σ : Finset (Fin n → ℤ)} (h : IsChainF σ) :
    #(σ.image dim) = #σ := card_image_iff.mpr h.injOn_dim

theorem image_dim_subset (σ : Finset (Fin n → ℤ)) :
    σ.image dim ⊆ range (#(sgnS σ) + 1) := by
  intro k hk
  obtain ⟨c, hc, rfl⟩ := mem_image.mp hk
  exact mem_range.mpr (Nat.lt_succ_of_le (dim_le_card_sgnS hc))

/-- A chain has at most one more face than its sign vector has entries. -/
theorem IsChainF.card_le {σ : Finset (Fin n → ℤ)} (h : IsChainF σ) : #σ ≤ #(sgnS σ) + 1 := by
  rw [← h.card_image_dim]
  simpa using card_le_card (image_dim_subset σ)

/-- If a face has as many interval coordinates as nonzero ones, the two sets coincide. -/
theorem supp_eq_oddSet {T : Fin n → ℤ} (h : #(sgnSet T) ≤ dim T) : supp T = oddSet T := by
  rw [card_sgnSet] at h
  exact (eq_of_subset_of_card_le (oddSet_subset_supp T) h).symm

/-- A *full* chain (one more face than sign entries) contains a face of each dimension
`0, …, r`, and its top face has all its nonzero coordinates odd. -/
theorem IsChainF.full {σ : Finset (Fin n → ℤ)} (h : IsChainF σ) (hf : #σ = #(sgnS σ) + 1) :
    σ.image dim = range (#(sgnS σ) + 1) ∧ ∃ T ∈ σ, dim T = #(sgnS σ) ∧
      (∀ c ∈ σ, FLE c T) ∧ sgnS σ = sgnSet T ∧ supp T = oddSet T := by
  have himg : σ.image dim = range (#(sgnS σ) + 1) :=
    eq_of_subset_of_card_le (image_dim_subset σ) (by rw [card_range, h.card_image_dim, hf])
  refine ⟨himg, ?_⟩
  have hr : #(sgnS σ) ∈ σ.image dim := by rw [himg]; exact self_mem_range_succ _
  obtain ⟨T, hT, hdT⟩ := mem_image.mp hr
  have htop : ∀ c ∈ σ, FLE c T := fun c hc =>
    h.fle_of_dim_le hc hT (hdT ▸ dim_le_card_sgnS hc)
  have hS := sgnS_eq_of_top hT htop
  exact ⟨T, hT, hdT, htop, hS, supp_eq_oddSet (by rw [← hS, hdT])⟩

/-- A *tight* chain (as many faces as sign entries) misses exactly one dimension `d`. -/
theorem IsChainF.tight {σ : Finset (Fin n → ℤ)} (h : IsChainF σ) (ht : #σ = #(sgnS σ)) :
    ∃ d ≤ #(sgnS σ), σ.image dim = (range (#(sgnS σ) + 1)).erase d := by
  have hsub := image_dim_subset σ
  have hc : #(range (#(sgnS σ) + 1) \ σ.image dim) = 1 := by
    rw [card_sdiff_of_subset hsub, card_range, h.card_image_dim, ht]; omega
  obtain ⟨d, hd⟩ := card_eq_one.mp hc
  have hdm : d ∈ range (#(sgnS σ) + 1) \ σ.image dim := by rw [hd]; exact mem_singleton_self d
  rw [mem_sdiff, mem_range] at hdm
  refine ⟨d, Nat.lt_succ_iff.mp hdm.1, ?_⟩
  ext k
  rw [mem_erase]
  constructor
  · intro hk
    exact ⟨fun hkd => hdm.2 (hkd ▸ hk), hsub hk⟩
  · rintro ⟨hkd, hk⟩
    by_contra hk'
    have : k ∈ range (#(sgnS σ) + 1) \ σ.image dim := mem_sdiff.mpr ⟨hk, hk'⟩
    rw [hd, mem_singleton] at this
    exact hkd this

theorem exists_mem_dim {σ : Finset (Fin n → ℤ)} {k : ℕ} (hk : k ∈ σ.image dim) :
    ∃ A ∈ σ, dim A = k := by
  simpa using hk

end Chains

/-! ### Removable vertices of a labelled simplex -/

section Removable

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Let `f` label the `r + 1` points of `A` so that the labels cover a set `S` of size
`r`. The points whose removal still leaves `S` covered are exactly one if a label
outside `S` occurs, and exactly two (the two points sharing a label) otherwise. -/
theorem card_removable (A : Finset α) (f : α → β) (S : Finset β)
    (hcard : #A = #S + 1) (hS : S ⊆ A.image f) :
    #(A.filter fun v => S ⊆ (A.erase v).image f) = if A.image f = S then 2 else 1 := by
  split_ifs with himg
  · have hlt : #(A.image f) < #A := by rw [himg, hcard]; omega
    obtain ⟨v, hv, w, hw, hvw, hf⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (fun x hx => mem_coe.mpr (mem_image_of_mem f (mem_coe.mp hx)))
    -- removing one of two points with the same label keeps the image
    have hinj : ∀ v w, v ∈ A → w ∈ A → v ≠ w → f v = f w → Set.InjOn f (A.erase v : Set α) := by
      intro v w hv hw hvw hf
      have himg' : (A.erase v).image f = A.image f := by
        apply Subset.antisymm (image_subset_image (erase_subset v A))
        intro y hy
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
        by_cases hxv : x = v
        · subst hxv
          rw [hf]
          exact mem_image_of_mem f (mem_erase.mpr ⟨Ne.symm hvw, hw⟩)
        · exact mem_image_of_mem f (mem_erase.mpr ⟨hxv, hx⟩)
      apply card_image_iff.mp
      rw [himg', himg, card_erase_of_mem hv, hcard]
      omega
    have hkey : ∀ u ∈ A, (S ⊆ (A.erase u).image f ↔ ∃ u' ∈ A, u' ≠ u ∧ f u' = f u) := by
      intro u hu
      constructor
      · intro h
        have : f u ∈ S := himg ▸ mem_image_of_mem f hu
        obtain ⟨u', hu', hfu⟩ := mem_image.mp (h this)
        exact ⟨u', (mem_erase.mp hu').2, (mem_erase.mp hu').1, hfu⟩
      · rintro ⟨u', hu', hne, hfu⟩ s hs
        rw [← himg] at hs
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
        by_cases hxu : x = u
        · subst hxu
          rw [← hfu]
          exact mem_image_of_mem f (mem_erase.mpr ⟨hne, hu'⟩)
        · exact mem_image_of_mem f (mem_erase.mpr ⟨hxu, hx⟩)
    have heq : A.filter (fun v => S ⊆ (A.erase v).image f) = {v, w} := by
      ext u
      rw [mem_filter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hu, h⟩
        obtain ⟨u', hu', hne, hfu⟩ := (hkey u hu).mp h
        by_contra hc
        push Not at hc
        obtain ⟨huv, huw⟩ := hc
        by_cases hu'v : u' = v
        · subst hu'v
          have := hinj u' w hv hw hvw hf (mem_erase.mpr ⟨huv, hu⟩)
            (mem_erase.mpr ⟨Ne.symm hvw, hw⟩) (by rw [← hfu, hf])
          exact huw this
        · exact hne (hinj v w hv hw hvw hf (mem_erase.mpr ⟨hu'v, hu'⟩)
            (mem_erase.mpr ⟨huv, hu⟩) hfu)
      · rintro (rfl | rfl)
        · exact ⟨hv, (hkey _ hv).mpr ⟨w, hw, Ne.symm hvw, hf.symm⟩⟩
        · exact ⟨hw, (hkey _ hw).mpr ⟨v, hv, hvw, hf⟩⟩
    rw [heq, card_pair hvw]
  · have hss : S ⊂ A.image f := ssubset_of_subset_of_ne hS (Ne.symm himg)
    have h1 := card_lt_card hss
    have h2 : #(A.image f) ≤ #A := card_image_le
    have hinj : Set.InjOn f (A : Set α) := card_image_iff.mp (by omega)
    have h3 : #(A.image f \ S) = 1 := by rw [card_sdiff_of_subset hS]; omega
    obtain ⟨ℓ, hℓ⟩ := card_eq_one.mp h3
    have hℓmem : ℓ ∈ A.image f \ S := by rw [hℓ]; exact mem_singleton_self ℓ
    obtain ⟨v₀, hv₀, hfv₀⟩ := mem_image.mp (mem_sdiff.mp hℓmem).1
    have hkey : ∀ u ∈ A, (S ⊆ (A.erase u).image f ↔ f u ∉ S) := by
      intro u hu
      constructor
      · intro h hfu
        obtain ⟨x, hx, hfx⟩ := mem_image.mp (h hfu)
        exact (mem_erase.mp hx).1 (hinj (mem_erase.mp hx).2 hu hfx)
      · intro hfu s hs
        obtain ⟨x, hx, rfl⟩ := mem_image.mp (hS hs)
        have hxu : x ≠ u := fun hxu => hfu (hxu ▸ hs)
        exact mem_image_of_mem f (mem_erase.mpr ⟨hxu, hx⟩)
    have heq : A.filter (fun v => S ⊆ (A.erase v).image f) = {v₀} := by
      ext u
      rw [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hu, h⟩
        have hfu := (hkey u hu).mp h
        have : f u ∈ A.image f \ S := mem_sdiff.mpr ⟨mem_image_of_mem f hu, hfu⟩
        rw [hℓ, mem_singleton, ← hfv₀] at this
        exact hinj hu hv₀ this
      · rintro rfl
        exact ⟨hv₀, (hkey _ hv₀).mpr (hfv₀ ▸ (mem_sdiff.mp hℓmem).2)⟩
    rw [heq, card_singleton]

/-- No point is removable when the labels do not cover `S`, or when there are too few
points. -/
theorem removable_eq_empty (A : Finset α) (f : α → β) (S : Finset β)
    (h : ¬ (#A = #S + 1 ∧ S ⊆ A.image f)) (hle : #A ≤ #S + 1) :
    A.filter (fun v => S ⊆ (A.erase v).image f) = ∅ := by
  rw [filter_eq_empty_iff]
  intro v hv hsub
  apply h
  have h1 := card_le_card hsub
  have h2 : #((A.erase v).image f) ≤ #(A.erase v) := card_image_le
  rw [card_erase_of_mem hv] at h2
  have hA : 0 < #A := card_pos.mpr ⟨v, hv⟩
  exact ⟨by omega, hsub.trans (image_subset_image (erase_subset v A))⟩

end Removable

/-! ### The door relation and the downward count -/

section Doors

variable {m : ℕ} (lab : (Fin n → ℤ) → Label n)

/-- `ρ` is a door of `τ`: `τ` is `ρ` with one more face, and the labels of `ρ` already
contain the whole sign vector of `τ`. -/
def Door (ρ τ : Finset (Fin n → ℤ)) : Prop := ρ ⊆ τ ∧ #τ = #ρ + 1 ∧ sgnS τ ⊆ ρ.image lab

instance : DecidableRel (Door lab) := fun _ _ => by unfold Door; infer_instance

/-- A full chain whose labels contain its sign vector and one label more. -/
def IsA (σ : Finset (Fin n → ℤ)) : Prop :=
  #σ = #(sgnS σ) + 1 ∧ sgnS σ ⊆ σ.image lab ∧ σ.image lab ≠ sgnS σ

instance (σ : Finset (Fin n → ℤ)) : Decidable (IsA lab σ) := by unfold IsA; infer_instance

variable (m) in
/-- A chain all of whose faces lie in the boundary of the cube. -/
def Bdry (σ : Finset (Fin n → ℤ)) : Prop := ∀ c ∈ σ, IsBdry m c

instance (σ : Finset (Fin n → ℤ)) : Decidable (Bdry m σ) := by
  unfold Bdry IsBdry; infer_instance

variable (m) in
/-- A tight boundary chain labelled exactly by its sign vector. -/
def IsB (σ : Finset (Fin n → ℤ)) : Prop := #σ = #(sgnS σ) ∧ σ.image lab = sgnS σ ∧ Bdry m σ

instance (σ : Finset (Fin n → ℤ)) : Decidable (IsB m lab σ) := by unfold IsB; infer_instance

theorem sgnSet_eq_empty_iff {c : Fin n → ℤ} : sgnSet c = ∅ ↔ c = 0 := by
  rw [sgnSet, image_eq_empty, supp, filter_eq_empty_iff]
  simp only [mem_univ, ne_eq, not_not, true_implies]
  exact ⟨fun h => funext h, fun h i => by simp [h]⟩

/-- The number of doors of `τ` from below, modulo `2`. -/
theorem card_down {τ : Finset (Fin n → ℤ)} (hτ : IsNode m τ) :
    (#((nodes m).filter fun ρ => Door lab ρ τ) : ZMod 2) =
      (if IsA lab τ then 1 else 0) + (if τ = {0} then 1 else 0) := by
  classical
  have hbij : #((nodes m).filter fun ρ => Door lab ρ τ) =
      #(τ.filter fun v => (τ.erase v).Nonempty ∧ sgnS τ ⊆ (τ.erase v).image lab) := by
    symm
    apply card_bij (fun v _ => τ.erase v)
    · intro v hv
      rw [mem_filter] at hv ⊢
      obtain ⟨hvτ, hne, hsub⟩ := hv
      refine ⟨mem_nodes.mpr ⟨hne, fun c hc => hτ.2.1 c (mem_of_mem_erase hc),
        hτ.2.2.subset (erase_subset v τ)⟩, erase_subset v τ, ?_, hsub⟩
      rw [card_erase_of_mem hvτ]
      have := card_pos.mpr ⟨v, hvτ⟩
      omega
    · intro v hv w hw hvw
      by_contra hne
      have : w ∈ τ.erase v := mem_erase.mpr ⟨Ne.symm hne, (mem_filter.mp hw).1⟩
      rw [hvw] at this
      exact (mem_erase.mp this).1 rfl
    · intro ρ hρ
      rw [mem_filter, mem_nodes] at hρ
      obtain ⟨hρn, hsub, hcard, hS⟩ := hρ
      obtain ⟨a, ha, rfl⟩ := exists_eq_insert_iff.mpr ⟨hsub, hcard.symm⟩
      refine ⟨a, mem_filter.mpr ⟨mem_insert_self a ρ, ?_⟩, erase_insert ha⟩
      rw [erase_insert ha]
      exact ⟨hρn.1, hS⟩
  rw [hbij]
  by_cases h1 : #τ = 1
  · obtain ⟨v, rfl⟩ := card_eq_one.mp h1
    have hempty : ({v} : Finset (Fin n → ℤ)).filter
        (fun w => (({v} : Finset _).erase w).Nonempty ∧
          sgnS {v} ⊆ (({v} : Finset _).erase w).image lab) = ∅ := by
      rw [filter_eq_empty_iff]
      intro w hw h
      rw [mem_singleton] at hw
      subst hw
      simp at h
    rw [hempty, card_empty, Nat.cast_zero]
    by_cases hv : v = 0
    · subst hv
      have hA : IsA lab ({0} : Finset (Fin n → ℤ)) := by
        have hs : sgnS ({0} : Finset (Fin n → ℤ)) = ∅ := by
          rw [sgnS, singleton_biUnion, sgnSet_eq_empty_iff]
        refine ⟨by rw [hs]; rfl, by rw [hs]; exact empty_subset _, ?_⟩
        rw [hs, image_singleton]
        exact singleton_ne_empty _
      rw [if_pos hA, if_pos rfl]
      decide
    · have hA : ¬ IsA lab ({v} : Finset (Fin n → ℤ)) := by
        rintro ⟨hc, -, -⟩
        rw [card_singleton, sgnS, singleton_biUnion] at hc
        have : sgnSet v = ∅ := card_eq_zero.mp (by omega)
        exact hv (sgnSet_eq_empty_iff.mp this)
      rw [if_neg hA, if_neg (fun h => hv (singleton_injective h))]
      simp
  · have h2 : 2 ≤ #τ := by
      have := card_pos.mpr hτ.1
      omega
    have hne : τ ≠ {0} := fun h => by rw [h, card_singleton] at h2; omega
    rw [if_neg hne, add_zero]
    have hfilt : τ.filter (fun v => (τ.erase v).Nonempty ∧ sgnS τ ⊆ (τ.erase v).image lab) =
        τ.filter (fun v => sgnS τ ⊆ (τ.erase v).image lab) := by
      apply filter_congr
      intro v hv
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      rw [← card_pos, card_erase_of_mem hv]
      omega
    rw [hfilt]
    by_cases hfull : #τ = #(sgnS τ) + 1 ∧ sgnS τ ⊆ τ.image lab
    · rw [card_removable τ lab (sgnS τ) hfull.1 hfull.2]
      by_cases himg : τ.image lab = sgnS τ
      · have hA : ¬ IsA lab τ := fun h => h.2.2 himg
        rw [if_pos himg, if_neg hA]
        decide
      · have hA : IsA lab τ := ⟨hfull.1, hfull.2, himg⟩
        rw [if_neg himg, if_pos hA]
        simp
    · rw [removable_eq_empty τ lab (sgnS τ) hfull hτ.2.2.card_le]
      have hA : ¬ IsA lab τ := fun h => hfull ⟨h.1, h.2.1⟩
      rw [if_neg hA]
      simp

/-- What a door says about the larger chain. -/
theorem door_facts {ρ τ : Finset (Fin n → ℤ)} (hτ : IsNode m τ) (hd : Door lab ρ τ) :
    ∃ a ∉ ρ, τ = insert a ρ ∧ #ρ ≤ #(sgnS τ) ∧ sgnS ρ ⊆ sgnS τ ∧ sgnS τ ⊆ ρ.image lab := by
  obtain ⟨hsub, hcard, hS⟩ := hd
  obtain ⟨a, ha, rfl⟩ := exists_eq_insert_iff.mpr ⟨hsub, hcard.symm⟩
  have := hτ.2.2.card_le
  exact ⟨a, ha, rfl, by omega, sgnS_mono hsub, hS⟩

end Doors

/-! ### The upward count at a full chain -/

section Full

variable {m : ℕ} (lab : (Fin n → ℤ) → Label n)

/-- Two faces of a chain never carry opposite labels, if no comparable pair does. -/
theorem no_flip_in_chain
    (hno : ∀ a b, InGrid m a → InGrid m b → FLE a b → lab a ≠ opp (lab b))
    {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ) {x y : Fin n → ℤ} (hx : x ∈ ρ) (hy : y ∈ ρ) :
    lab x ≠ opp (lab y) := by
  rcases hρ.2.2 x hx y hy with h | h
  · exact hno x y (hρ.2.1 x hx) (hρ.2.1 y hy) h
  · intro hxy
    apply hno y x (hρ.2.1 y hy) (hρ.2.1 x hx) h
    rw [hxy, opp_opp]

/-- **The upward count at a full chain.** A full chain with an extra label `ℓ` has exactly
one door upward: the face of its top obtained by opening coordinate `ℓ.1` in the
direction `ℓ.2`. Otherwise it has none. -/
theorem card_up_full (hm : 1 ≤ m)
    (hno : ∀ a b, InGrid m a → InGrid m b → FLE a b → lab a ≠ opp (lab b))
    {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ) (hf : #ρ = #(sgnS ρ) + 1) :
    #((nodes m).filter fun τ => Door lab ρ τ) = if IsA lab ρ then 1 else 0 := by
  split_ifs with hA
  · obtain ⟨-, hS, himg⟩ := hA
    obtain ⟨-, T, hT, hdT, htop, hST, hsupp⟩ := hρ.2.2.full hf
    -- the extra label
    have hcardimg : #(ρ.image lab) ≤ #ρ := card_image_le
    have hlt := card_lt_card (ssubset_of_subset_of_ne hS (Ne.symm himg))
    have h3 : #(ρ.image lab \ sgnS ρ) = 1 := by rw [card_sdiff_of_subset hS]; omega
    obtain ⟨ℓ, hℓ⟩ := card_eq_one.mp h3
    have hℓmem : ℓ ∈ ρ.image lab \ sgnS ρ := by rw [hℓ]; exact mem_singleton_self ℓ
    obtain ⟨j, b⟩ := ℓ
    have hTj : T j = 0 := by
      by_contra hTj
      have hmem : (j, decide (0 < T j)) ∈ sgnS ρ := by
        rw [hST, mem_sgnSet]; exact ⟨hTj, rfl⟩
      have hb : decide (0 < T j) ≠ b := by
        intro hb
        rw [hb] at hmem
        exact (mem_sdiff.mp hℓmem).2 hmem
      have hflip : (j, decide (0 < T j)) = opp (j, b) := by
        simp only [opp, Prod.mk.injEq, true_and]
        cases hd : decide (0 < T j) <;> cases b <;> simp_all
      obtain ⟨x, hx, hlx⟩ := mem_image.mp (hS hmem)
      obtain ⟨y, hy, hly⟩ := mem_image.mp (mem_sdiff.mp hℓmem).1
      exact no_flip_in_chain lab hno hρ hx hy (by rw [hlx, hly, hflip])
    have hcj : ∀ c ∈ ρ, c j = 0 := fun c hc =>
      ((htop c hc) j).eq_of_even_right (by rw [hTj]; decide) |>.trans hTj
    set G := Function.update T j (if b then 1 else -1) with hG
    have hGj : G j = if b then 1 else -1 := by simp [hG]
    have hGi : ∀ i, i ≠ j → G i = T i := fun i hi => by simp [hG, hi]
    have hTG : FLE T G := by
      intro i
      by_cases hij : i = j
      · subst hij; rw [hGj, hTj]; unfold CLE; cases b <;> simp
      · rw [hGi i hij]; exact CLE.refl _
    have hGρ : G ∉ ρ := fun hG' => by
      have := hcj G hG'
      rw [hGj] at this
      cases b <;> simp at this
    apply card_eq_one.mpr
    refine ⟨insert G ρ, ?_⟩
    apply eq_singleton_iff_unique_mem.mpr
    constructor
    · rw [mem_filter, mem_nodes]
      refine ⟨⟨insert_nonempty G ρ, ?_, ?_⟩, subset_insert G ρ, card_insert_of_notMem hGρ, ?_⟩
      · intro c hc
        rcases mem_insert.mp hc with rfl | hc
        · intro i
          by_cases hij : i = j
          · subst hij; rw [hGj]; cases b <;> simp <;> omega
          · rw [hGi i hij]; exact hρ.2.1 T hT i
        · exact hρ.2.1 c hc
      · intro x hx y hy
        rcases mem_insert.mp hx with rfl | hx' <;> rcases mem_insert.mp hy with rfl | hy'
        · exact Or.inl (FLE.refl _)
        · exact Or.inr ((htop y hy').trans hTG)
        · exact Or.inl ((htop x hx').trans hTG)
        · exact hρ.2.2 x hx' y hy'
      · rw [sgnS_insert]
        refine union_subset ?_ hS
        intro ℓ' hℓ'
        obtain ⟨i, bb⟩ := ℓ'
        rw [mem_sgnSet] at hℓ'
        obtain ⟨hne, hbb⟩ := hℓ'
        dsimp only at hne hbb
        by_cases hij : i = j
        · subst hij
          have : (i, bb) = (i, b) := by
            simp only [Prod.mk.injEq, true_and]
            rw [hbb, hGj]; cases b <;> simp
          rw [this]
          exact (mem_sdiff.mp hℓmem).1
        · apply hS
          rw [hST, mem_sgnSet]
          rw [hGi i hij] at hne hbb
          exact ⟨hne, hbb⟩
    · intro τ hτ
      rw [mem_filter, mem_nodes] at hτ
      obtain ⟨a, ha, rfl, hle, -, hSτ⟩ := door_facts lab hτ.1 hτ.2
      have hch := hτ.1.2.2
      -- the new face lies above the top face
      have hda : dim T < dim a := by
        by_contra hda
        push Not at hda
        have hmem : dim a ∈ ρ.image dim := by
          rw [(hρ.2.2.full hf).1, mem_range]; omega
        obtain ⟨c, hc, hdc⟩ := exists_mem_dim hmem
        have := (hch c (mem_insert_of_mem hc) a (mem_insert_self a ρ)).eq_of_dim_eq hdc
        exact ha (this ▸ hc)
      have hTa : FLE T a :=
        (hch T (mem_insert_of_mem hT) a (mem_insert_self a ρ)).fle_of_dim_le hda.le
      have hnew : ∀ i, a i ≠ 0 → T i = 0 → (i, decide (0 < a i)) = (j, b) := by
        intro i hai hTi
        have hmem : (i, decide (0 < a i)) ∈ ρ.image lab :=
          hSτ (sgnSet_subset_sgnS (mem_insert_self a ρ) (mem_sgnSet.mpr ⟨hai, rfl⟩))
        have hnot : (i, decide (0 < a i)) ∉ sgnS ρ := by
          rw [hST, mem_sgnSet]; exact fun h => h.1 hTi
        have : (i, decide (0 < a i)) ∈ ρ.image lab \ sgnS ρ := mem_sdiff.mpr ⟨hmem, hnot⟩
        rw [hℓ] at this
        exact mem_singleton.mp this
      have hT0 : ∀ i, T i % 2 ≠ 1 → T i = 0 := by
        intro i hi
        by_contra h
        have : i ∈ supp T := by simp [supp, h]
        rw [hsupp] at this
        simp [oddSet] at this
        exact hi this
      have hcoord : ∀ i, i ≠ j → a i = T i := by
        intro i hij
        by_cases hodd : T i % 2 = 1
        · exact ((hTa i).eq_of_odd hodd).symm
        · have hTi := hT0 i hodd
          by_contra hai
          have := hnew i (by rw [hTi] at hai; exact hai) hTi
          exact hij (Prod.mk.inj this).1
      have haj : a j ≠ 0 := by
        intro haj
        apply ha
        have : a = T := funext fun i => by
          by_cases hij : i = j
          · subst hij; rw [haj, hTj]
          · exact hcoord i hij
        rw [this]; exact hT
      have hbj := (Prod.mk.inj (hnew j haj hTj)).2
      have hcj' := hTa j
      rw [hTj] at hcj'
      have haj' : a j = if b then 1 else -1 := by
        unfold CLE at hcj'
        cases b <;> simp at hbj ⊢ <;> omega
      congr 1
      funext i
      by_cases hij : i = j
      · subst hij; rw [hGj, haj']
      · rw [hGi i hij, hcoord i hij]
  · apply card_eq_zero.mpr
    rw [filter_eq_empty_iff]
    intro τ hτ hd
    apply hA
    obtain ⟨a, ha, rfl, hle, hSS, hSτ⟩ := door_facts lab (mem_nodes.mp hτ) hd
    have hcardimg : #(ρ.image lab) ≤ #ρ := card_image_le
    have heq : sgnS (insert a ρ) = ρ.image lab := eq_of_subset_of_card_le hSτ (by omega)
    refine ⟨hf, heq ▸ hSS, fun h => ?_⟩
    have := card_le_card hSτ
    rw [h] at this
    omega

end Full

/-! ### The upward count at a tight chain -/

section Tight

variable {m : ℕ}

variable (m) in
/-- The faces completing a chain inside its own orthant face. -/
noncomputable def comp (ρ : Finset (Fin n → ℤ)) : Finset (Fin n → ℤ) :=
  (grid m).filter fun G => G ∉ ρ ∧ (∀ c ∈ ρ, Comparable c G) ∧ sgnSet G ⊆ sgnS ρ

theorem mem_comp {ρ : Finset (Fin n → ℤ)} {G : Fin n → ℤ} :
    G ∈ comp m ρ ↔ InGrid m G ∧ G ∉ ρ ∧ (∀ c ∈ ρ, Comparable c G) ∧ sgnSet G ⊆ sgnS ρ := by
  rw [comp, mem_filter, mem_grid]

/-- Chains one face larger with the same sign vector correspond to completing faces. -/
theorem card_up_eq_card_comp {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ) :
    #((nodes m).filter fun τ => ρ ⊆ τ ∧ #τ = #ρ + 1 ∧ sgnS τ ⊆ sgnS ρ) = #(comp m ρ) := by
  symm
  apply card_bij (fun G _ => insert G ρ)
  · intro G hG
    obtain ⟨hGg, hGρ, hcomp, hGS⟩ := mem_comp.mp hG
    rw [mem_filter, mem_nodes]
    refine ⟨⟨insert_nonempty G ρ, ?_, ?_⟩, subset_insert G ρ, card_insert_of_notMem hGρ, ?_⟩
    · intro c hc
      rcases mem_insert.mp hc with rfl | hc
      · exact hGg
      · exact hρ.2.1 c hc
    · intro x hx y hy
      rcases mem_insert.mp hx with rfl | hx' <;> rcases mem_insert.mp hy with rfl | hy'
      · exact Or.inl (FLE.refl _)
      · exact (hcomp y hy').symm
      · exact hcomp x hx'
      · exact hρ.2.2 x hx' y hy'
    · rw [sgnS_insert]; exact union_subset hGS (Subset.refl _)
  · intro G hG G' _ h
    obtain ⟨-, hGρ, -⟩ := mem_comp.mp hG
    have : G ∈ insert G' ρ := h ▸ mem_insert_self G ρ
    rcases mem_insert.mp this with h' | h'
    · exact h'
    · exact absurd h' hGρ
  · intro τ hτ
    rw [mem_filter, mem_nodes] at hτ
    obtain ⟨hτn, hsub, hcard, hS⟩ := hτ
    obtain ⟨a, ha, rfl⟩ := exists_eq_insert_iff.mpr ⟨hsub, hcard.symm⟩
    exact ⟨a, mem_comp.mpr ⟨hτn.2.1 a (mem_insert_self a ρ), ha,
      fun c hc => hτn.2.2 c (mem_insert_of_mem hc) a (mem_insert_self a ρ),
      (sgnSet_subset_sgnS (mem_insert_self a ρ)).trans hS⟩, rfl⟩

/-- A completing face has the missing dimension. -/
theorem dim_of_mem_comp {ρ : Finset (Fin n → ℤ)} {d : ℕ}
    (hd : ρ.image dim = (range (#(sgnS ρ) + 1)).erase d) {G : Fin n → ℤ}
    (hG : G ∈ comp m ρ) : dim G = d := by
  obtain ⟨-, hGρ, hcomp, hGS⟩ := mem_comp.mp hG
  by_contra hne
  have hle : dim G ≤ #(sgnS ρ) := (dim_le_card_sgnSet G).trans (card_le_card hGS)
  have hmem : dim G ∈ ρ.image dim := by rw [hd, mem_erase, mem_range]; omega
  obtain ⟨c, hc, hdc⟩ := exists_mem_dim hmem
  exact hGρ ((hcomp c hc).eq_of_dim_eq hdc ▸ hc)

/-- A face of a chain of full dimension in its orthant face is not a boundary face. -/
theorem not_isBdry_of_top (hm : 1 ≤ m) {ρ : Finset (Fin n → ℤ)} {T : Fin n → ℤ} (hT : T ∈ ρ)
    (hdT : dim T = #(sgnS ρ)) : ¬ IsBdry m T := by
  have hsupp : supp T = oddSet T := supp_eq_oddSet (hdT ▸ card_le_card (sgnSet_subset_sgnS hT))
  rintro ⟨i, hi⟩
  have : i ∈ supp T := by simp only [supp, mem_filter, mem_univ, true_and]; omega
  rw [hsupp] at this
  simp only [oddSet, mem_filter, mem_univ, true_and] at this
  omega

theorem mem_image_dim_of_ne {ρ : Finset (Fin n → ℤ)} {d k : ℕ}
    (hd : ρ.image dim = (range (#(sgnS ρ) + 1)).erase d) (hk : k ≤ #(sgnS ρ)) (hkd : k ≠ d) :
    ∃ A ∈ ρ, dim A = k :=
  exists_mem_dim (by rw [hd, mem_erase, mem_range]; omega)

theorem dim_ne_of_mem {ρ : Finset (Fin n → ℤ)} {d : ℕ}
    (hd : ρ.image dim = (range (#(sgnS ρ) + 1)).erase d) {c : Fin n → ℤ} (hc : c ∈ ρ) :
    dim c ≠ d ∧ dim c ≤ #(sgnS ρ) := by
  have : dim c ∈ ρ.image dim := mem_image_of_mem dim hc
  rw [hd, mem_erase, mem_range] at this
  omega

/-- **Missing top face.** When the missing dimension is the top one, the completions
open the unique nonzero even coordinate `j` of the top face one step in either
direction, and only one step fits exactly when that coordinate is `±2m`, that is,
when the chain lies in the boundary. -/
theorem card_comp_top (hm : 1 ≤ m) {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ)
    (hr : 1 ≤ #(sgnS ρ))
    (hd : ρ.image dim = (range (#(sgnS ρ) + 1)).erase (#(sgnS ρ))) :
    (#(comp m ρ) : ZMod 2) = if Bdry m ρ then 1 else 0 := by
  obtain ⟨T, hT, hdT⟩ := mem_image_dim_of_ne hd (k := #(sgnS ρ) - 1) (by omega) (by omega)
  have htop : ∀ c ∈ ρ, FLE c T := fun c hc =>
    hρ.2.2.fle_of_dim_le hc hT (by have := dim_ne_of_mem hd hc; omega)
  have hST : sgnS ρ = sgnSet T := sgnS_eq_of_top hT htop
  have hcs : #(supp T \ oddSet T) = 1 := by
    rw [card_sdiff_of_subset (oddSet_subset_supp T), ← card_sgnSet, ← hST]
    unfold dim at hdT; omega
  obtain ⟨j, hj⟩ := card_eq_one.mp hcs
  have hjmem : j ∈ supp T \ oddSet T := by rw [hj]; exact mem_singleton_self j
  have hTj0 : T j ≠ 0 := by simpa [supp] using (mem_sdiff.mp hjmem).1
  have hTjev : ¬ T j % 2 = 1 := by simpa [oddSet] using (mem_sdiff.mp hjmem).2
  have huniq : ∀ i, T i ≠ 0 → ¬ T i % 2 = 1 → i = j := by
    intro i h1 h2
    have : i ∈ supp T \ oddSet T := by simp [supp, oddSet, h1, h2]
    rw [hj] at this; exact mem_singleton.mp this
  set Y := ({T j + 1, T j - 1} : Finset ℤ).filter
    (fun y => -(2 * (m : ℤ)) ≤ y ∧ y ≤ 2 * m) with hY
  have hcomp : comp m ρ = Y.image (Function.update T j) := by
    ext G
    rw [mem_comp, mem_image]
    constructor
    · rintro ⟨hGg, hGρ, hcmp, hGS⟩
      have hdG : dim G = #(sgnS ρ) :=
        dim_of_mem_comp hd (mem_comp.mpr ⟨hGg, hGρ, hcmp, hGS⟩)
      have hTG : FLE T G := (hcmp T hT).fle_of_dim_le (by omega)
      obtain ⟨k, hk⟩ := hTG.exists_diff_one (by omega)
      have hkmem : k ∈ diffSet T G := by rw [hk]; exact mem_singleton_self k
      have hTk : T k ≠ G k := by simpa [diffSet] using hkmem
      have hne := (hTG k).ne_iff.mp hTk
      have hkj : k = j := by
        refine huniq k ?_ hne.2
        intro hTk0
        have hGk0 : G k ≠ 0 := by omega
        have : (k, decide (0 < G k)) ∈ sgnSet T := by
          rw [← hST]; exact hGS (mem_sgnSet.mpr ⟨hGk0, rfl⟩)
        exact (mem_sgnSet.mp this).1 hTk0
      subst hkj
      refine ⟨G k, ?_, (eq_update_of_diffSet hk).symm⟩
      rw [hY, mem_filter, mem_insert, mem_singleton]
      have := hTG k
      unfold CLE at this
      have hb := hGg k
      omega
    · rintro ⟨y, hy, rfl⟩
      rw [hY, mem_filter, mem_insert, mem_singleton] at hy
      have hTG : FLE T (Function.update T j y) := by
        intro i
        by_cases hij : i = j
        · subst hij; simp only [Function.update_self]; unfold CLE; omega
        · rw [Function.update_of_ne hij]; exact CLE.refl _
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hij : i = j
        · subst hij; simp only [Function.update_self]; omega
        · rw [Function.update_of_ne hij]; exact hρ.2.1 T hT i
      · intro hG
        have := (htop _ hG j).eq_of_even_right hTjev
        simp only [Function.update_self] at this
        omega
      · intro c hc; exact Or.inl ((htop c hc).trans hTG)
      · rw [hST]
        intro ℓ hℓ
        obtain ⟨i, b⟩ := ℓ
        rw [mem_sgnSet] at hℓ ⊢
        dsimp only at hℓ ⊢
        by_cases hij : i = j
        · subst hij
          simp only [Function.update_self] at hℓ
          refine ⟨hTj0, ?_⟩
          rw [hℓ.2]
          apply decide_eq_decide.mpr
          omega
        · rw [Function.update_of_ne hij] at hℓ; exact hℓ
  rw [hcomp, card_image_of_injective _ (Function.update_injective T j)]
  have hbdry : Bdry m ρ ↔ (T j = 2 * m ∨ T j = -(2 * m)) := by
    constructor
    · intro h
      obtain ⟨i, hi⟩ := h T hT
      have hij : i = j := huniq i (by omega) (by omega)
      subst hij; exact hi
    · intro h c hc
      refine ⟨j, ?_⟩
      rw [(htop c hc j).eq_of_even_right hTjev]
      exact h
  have hTjb := hρ.2.1 T hT j
  rw [hY, card_filter, sum_pair (by omega)]
  by_cases hb : T j = 2 * m ∨ T j = -(2 * m)
  · rw [if_pos (hbdry.mpr hb)]
    rcases hb with hb | hb
    · rw [if_neg (by omega), if_pos (by omega)]; simp
    · rw [if_pos (by omega), if_neg (by omega)]; simp
  · rw [if_neg (fun h => hb (hbdry.mp h)), if_pos (by omega), if_pos (by omega)]
    decide

/-- **Missing vertex.** When the missing dimension is `0`, the two completions are the
two endpoints of the edge at the bottom of the chain. -/
theorem card_comp_bottom (hm : 1 ≤ m) {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ)
    (hr : 1 ≤ #(sgnS ρ)) (hd : ρ.image dim = (range (#(sgnS ρ) + 1)).erase 0) :
    #(comp m ρ) = 2 ∧ ¬ Bdry m ρ := by
  obtain ⟨A, hA, hdA⟩ := mem_image_dim_of_ne hd (k := 1) hr (by omega)
  obtain ⟨T, hT, hdT⟩ := mem_image_dim_of_ne hd (k := #(sgnS ρ)) le_rfl (by omega)
  refine ⟨?_, fun h => not_isBdry_of_top hm hT hdT (h T hT)⟩
  have hAc : ∀ c ∈ ρ, FLE A c := fun c hc =>
    hρ.2.2.fle_of_dim_le hA hc (by have := dim_ne_of_mem hd hc; omega)
  obtain ⟨i₀, hi₀⟩ := card_eq_one.mp (show #(oddSet A) = 1 from hdA)
  have hAodd : A i₀ % 2 = 1 := by
    have : i₀ ∈ oddSet A := by rw [hi₀]; exact mem_singleton_self _
    simpa [oddSet] using this
  have hAev : ∀ i, i ≠ i₀ → ¬ A i % 2 = 1 := by
    intro i hi h
    have : i ∈ oddSet A := by simp [oddSet, h]
    rw [hi₀, mem_singleton] at this; exact hi this
  have hcomp : comp m ρ = ({A i₀ + 1, A i₀ - 1} : Finset ℤ).image (Function.update A i₀) := by
    ext G
    rw [mem_comp, mem_image]
    constructor
    · rintro ⟨hGg, hGρ, hcmp, hGS⟩
      have hdG : dim G = 0 := dim_of_mem_comp hd (mem_comp.mpr ⟨hGg, hGρ, hcmp, hGS⟩)
      have hGA : FLE G A := (hcmp A hA).symm.fle_of_dim_le (by omega)
      obtain ⟨k, hk⟩ := hGA.exists_diff_one (by omega)
      have hkmem : k ∈ diffSet G A := by rw [hk]; exact mem_singleton_self k
      have hGk : G k ≠ A k := by simpa [diffSet] using hkmem
      have hne := (hGA k).ne_iff.mp hGk
      have hki : k = i₀ := by by_contra h; exact hAev k h hne.1
      subst hki
      refine ⟨G k, ?_, ?_⟩
      · rw [mem_insert, mem_singleton]; have := hGA k; unfold CLE at this; omega
      · rw [diffSet_comm] at hk
        exact (eq_update_of_diffSet hk).symm
    · rintro ⟨y, hy, rfl⟩
      rw [mem_insert, mem_singleton] at hy
      have hGA : FLE (Function.update A i₀ y) A := by
        intro i
        by_cases hij : i = i₀
        · subst hij; simp only [Function.update_self]; unfold CLE; omega
        · rw [Function.update_of_ne hij]; exact CLE.refl _
      have hdiff : diffSet (Function.update A i₀ y) A = {i₀} := by
        ext i
        by_cases hij : i = i₀
        · subst hij; simp only [diffSet, mem_filter, mem_univ, true_and, Function.update_self,
            mem_singleton, iff_true]; omega
        · simp [diffSet, hij]
      have hdG : dim (Function.update A i₀ y) = 0 := by
        have := hGA.card_diffSet; rw [hdiff, card_singleton, hdA] at this; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        by_cases hij : i = i₀
        · subst hij; simp only [Function.update_self]; have := hρ.2.1 A hA i; omega
        · rw [Function.update_of_ne hij]; exact hρ.2.1 A hA i
      · intro hG
        exact (dim_ne_of_mem hd hG).1 hdG
      · intro c hc; exact Or.inr (hGA.trans (hAc c hc))
      · exact hGA.sgnSet_subset.trans (sgnSet_subset_sgnS hA)
  rw [hcomp, card_image_of_injective _ (Function.update_injective A i₀), card_pair (by omega)]

/-- **Missing middle face.** When the missing dimension `d` lies strictly between `0` and
the top, the completions are the two faces between the faces of dimensions `d - 1`
and `d + 1` (the diamond property). -/
theorem card_comp_middle (hm : 1 ≤ m) {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ) {d : ℕ}
    (hd0 : 0 < d) (hdr : d < #(sgnS ρ))
    (hd : ρ.image dim = (range (#(sgnS ρ) + 1)).erase d) :
    #(comp m ρ) = 2 ∧ ¬ Bdry m ρ := by
  obtain ⟨A, hA, hdA⟩ := mem_image_dim_of_ne hd (k := d - 1) (by omega) (by omega)
  obtain ⟨B, hB, hdB⟩ := mem_image_dim_of_ne hd (k := d + 1) (by omega) (by omega)
  obtain ⟨T, hT, hdT⟩ := mem_image_dim_of_ne hd (k := #(sgnS ρ)) le_rfl (by omega)
  refine ⟨?_, fun h => not_isBdry_of_top hm hT hdT (h T hT)⟩
  have hAB : FLE A B := hρ.2.2.fle_of_dim_le hA hB (by omega)
  obtain ⟨i, j, hij, hIJ⟩ := card_eq_two.mp
    (show #(diffSet A B) = 2 by have := hAB.card_diffSet; omega)
  have hAi : A i ≠ B i := by
    have : i ∈ diffSet A B := by rw [hIJ]; simp
    simpa [diffSet] using this
  have hAj : A j ≠ B j := by
    have : j ∈ diffSet A B := by rw [hIJ]; simp
    simpa [diffSet] using this
  have hAk : ∀ k, k ≠ i → k ≠ j → A k = B k := by
    intro k hki hkj
    by_contra h
    have : k ∈ diffSet A B := by simp [diffSet, h]
    rw [hIJ] at this
    simp [hki, hkj] at this
  have hvalid : ∀ k, A k ≠ B k → Function.update A k (B k) ∈ comp m ρ := by
    intro k hk
    have hAG : FLE A (Function.update A k (B k)) := by
      intro l
      by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact hAB l
      · rw [Function.update_of_ne hl]; exact CLE.refl _
    have hGB : FLE (Function.update A k (B k)) B := by
      intro l
      by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact CLE.refl _
      · rw [Function.update_of_ne hl]; exact hAB l
    have hdiff : diffSet A (Function.update A k (B k)) = {k} := by
      ext l
      by_cases hl : l = k
      · subst hl; simp [diffSet, hk]
      · simp [diffSet, hl]
    have hdG : dim (Function.update A k (B k)) = d := by
      have := hAG.card_diffSet; rw [hdiff, card_singleton] at this; omega
    refine mem_comp.mpr ⟨?_, ?_, ?_, ?_⟩
    · intro l
      by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact hρ.2.1 B hB l
      · rw [Function.update_of_ne hl]; exact hρ.2.1 A hA l
    · intro hG; exact (dim_ne_of_mem hd hG).1 hdG
    · intro c hc
      have hcd := (dim_ne_of_mem hd hc).1
      by_cases hc' : dim c < d
      · exact Or.inl ((hρ.2.2.fle_of_dim_le hc hA (by omega)).trans hAG)
      · exact Or.inr (hGB.trans (hρ.2.2.fle_of_dim_le hB hc (by omega)))
    · exact hGB.sgnSet_subset.trans (sgnSet_subset_sgnS hB)
  have hcomp : comp m ρ = {Function.update A i (B i), Function.update A j (B j)} := by
    ext G
    rw [mem_insert, mem_singleton]
    constructor
    · intro hG
      obtain ⟨-, -, hcmp, -⟩ := mem_comp.mp hG
      have hdG := dim_of_mem_comp hd hG
      have hAG : FLE A G := (hcmp A hA).fle_of_dim_le (by omega)
      have hGB : FLE G B := (hcmp B hB).symm.fle_of_dim_le (by omega)
      obtain ⟨k, hk⟩ := hAG.exists_diff_one (by omega)
      have hkmem : k ∈ diffSet A G := by rw [hk]; exact mem_singleton_self k
      have hAGk : A k ≠ G k := by simpa [diffSet] using hkmem
      have hGk : G k = B k := (hGB k).eq_of_odd ((hAG k).ne_iff.mp hAGk).1
      have hABk : A k ≠ B k := hGk ▸ hAGk
      have hG : G = Function.update A k (B k) := by
        rw [← hGk]; exact eq_update_of_diffSet hk
      have : k = i ∨ k = j := by
        by_contra h
        push Not at h
        exact hABk (hAk k h.1 h.2)
      rcases this with rfl | rfl
      · exact Or.inl hG
      · exact Or.inr hG
    · rintro (rfl | rfl)
      · exact hvalid i hAi
      · exact hvalid j hAj
  rw [hcomp, card_pair]
  intro h
  have := congrFun h i
  rw [Function.update_self, Function.update_of_ne hij] at this
  exact hAi this.symm

/-- **The upward count at a tight chain**, modulo `2`: it is odd exactly for boundary
chains. -/
theorem card_up_tight (hm : 1 ≤ m) {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ)
    (ht : #ρ = #(sgnS ρ)) :
    (#((nodes m).filter fun τ => ρ ⊆ τ ∧ #τ = #ρ + 1 ∧ sgnS τ ⊆ sgnS ρ) : ZMod 2) =
      if Bdry m ρ then 1 else 0 := by
  rw [card_up_eq_card_comp hρ]
  have hr : 1 ≤ #(sgnS ρ) := by have := card_pos.mpr hρ.1; omega
  obtain ⟨d, hdr, hd⟩ := hρ.2.2.tight ht
  rcases Nat.lt_or_ge d #(sgnS ρ) with hlt | hge
  · have h2 : #(comp m ρ) = 2 ∧ ¬ Bdry m ρ := by
      rcases Nat.eq_zero_or_pos d with rfl | hpos
      · exact card_comp_bottom hm hρ hr hd
      · exact card_comp_middle hm hρ hpos hlt hd
    rw [h2.1, if_neg h2.2]
    decide
  · have : d = #(sgnS ρ) := le_antisymm hdr hge
    rw [this] at hd
    exact card_comp_top hm hρ hr hd

end Tight

/-! ### Tucker's lemma -/

section Tucker

variable {m : ℕ} (lab : (Fin n → ℤ) → Label n)

/-- The upward count at any chain, modulo `2`. -/
theorem card_up (hm : 1 ≤ m)
    (hno : ∀ a b, InGrid m a → InGrid m b → FLE a b → lab a ≠ opp (lab b))
    {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ) :
    (#((nodes m).filter fun τ => Door lab ρ τ) : ZMod 2) =
      (if IsA lab ρ then 1 else 0) + (if IsB m lab ρ then 1 else 0) := by
  have hle := hρ.2.2.card_le
  have himgle : #(ρ.image lab) ≤ #ρ := card_image_le
  rcases Nat.lt_or_ge #ρ #(sgnS ρ) with hlt | hge
  · have hA : ¬ IsA lab ρ := fun h => by have := h.1; omega
    have hB : ¬ IsB m lab ρ := fun h => by have := h.1; omega
    rw [if_neg hA, if_neg hB, card_eq_zero.mpr, Nat.cast_zero, add_zero]
    rw [filter_eq_empty_iff]
    intro τ hτ hd
    obtain ⟨a, -, rfl, -, hSS, hSτ⟩ := door_facts lab (mem_nodes.mp hτ) hd
    have h1 := card_le_card (hSS.trans hSτ)
    omega
  · rcases Nat.lt_or_ge #(sgnS ρ) #ρ with hlt | hge'
    · have hf : #ρ = #(sgnS ρ) + 1 := by omega
      have hB : ¬ IsB m lab ρ := fun h => by have := h.1; omega
      rw [card_up_full lab hm hno hρ hf, if_neg hB, add_zero]
      split_ifs <;> simp
    · have ht : #ρ = #(sgnS ρ) := by omega
      have hA : ¬ IsA lab ρ := fun h => by have := h.1; omega
      rw [if_neg hA, zero_add]
      by_cases himg : ρ.image lab = sgnS ρ
      · have hfilt : (nodes m).filter (fun τ => Door lab ρ τ) =
            (nodes m).filter (fun τ => ρ ⊆ τ ∧ #τ = #ρ + 1 ∧ sgnS τ ⊆ sgnS ρ) := by
          apply filter_congr
          intro τ _
          simp only [Door, himg]
        rw [hfilt, card_up_tight hm hρ ht]
        by_cases hb : Bdry m ρ
        · rw [if_pos hb, if_pos ⟨ht, himg, hb⟩]
        · rw [if_neg hb, if_neg (fun h => hb h.2.2)]
      · have hB : ¬ IsB m lab ρ := fun h => himg h.2.1
        rw [if_neg hB, card_eq_zero.mpr, Nat.cast_zero]
        rw [filter_eq_empty_iff]
        intro τ hτ hd
        obtain ⟨a, -, rfl, -, hSS, hSτ⟩ := door_facts lab (mem_nodes.mp hτ) hd
        exact himg (eq_of_subset_of_card_le (hSS.trans hSτ) (by omega)).symm

theorem sgnSet_neg (c : Fin n → ℤ) : sgnSet (-c) = (sgnSet c).image opp := by
  ext ⟨i, b⟩
  rw [mem_image]
  constructor
  · intro h
    rw [mem_sgnSet] at h
    obtain ⟨h1, h2⟩ := h
    dsimp only at h1 h2
    refine ⟨(i, !b), mem_sgnSet.mpr ⟨by simpa using h1, ?_⟩, by simp [opp]⟩
    dsimp only
    rw [h2]
    simp only [Pi.neg_apply, Left.neg_pos_iff] at h1 ⊢
    cases hc : decide (c i < 0) <;> cases hc' : decide (0 < c i) <;> simp_all <;> omega
  · rintro ⟨⟨j, b'⟩, h, he⟩
    simp only [opp, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [mem_sgnSet] at h ⊢
    obtain ⟨h1, h2⟩ := h
    dsimp only at h1 h2 ⊢
    refine ⟨by simpa using h1, ?_⟩
    rw [h2]
    simp only [Pi.neg_apply, Left.neg_pos_iff]
    cases hc : decide (c j < 0) <;> cases hc' : decide (0 < c j) <;> simp_all <;> omega

theorem sgnS_neg (ρ : Finset (Fin n → ℤ)) :
    sgnS (ρ.image fun c => -c) = (sgnS ρ).image opp := by
  rw [sgnS, sgnS, image_biUnion, biUnion_image]
  simp only [sgnSet_neg]

theorem opp_injective : Function.Injective (opp : Label n → Label n) := fun a b h => by
  rw [← opp_opp a, h, opp_opp]

/-- The antipodal map on chains maps tight boundary chains labelled by their sign vector
to chains of the same kind, and moves each of them. -/
theorem isB_neg (hm : 1 ≤ m)
    (hanti : ∀ c, InGrid m c → IsBdry m c → lab (-c) = opp (lab c))
    {ρ : Finset (Fin n → ℤ)} (hρ : IsNode m ρ) (hB : IsB m lab ρ) :
    IsNode m (ρ.image fun c => -c) ∧ IsB m lab (ρ.image fun c => -c) ∧
      (ρ.image fun c => -c) ≠ ρ := by
  obtain ⟨ht, himg, hbd⟩ := hB
  have hinj : Function.Injective (fun c : Fin n → ℤ => -c) := neg_injective
  refine ⟨⟨hρ.1.image _, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := mem_image.mp hc
    intro i
    have := hρ.2.1 c' hc' i
    simp only [Pi.neg_apply]
    omega
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := mem_image.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_image.mp hy
    rcases hρ.2.2 x' hx' y' hy' with h | h
    · exact Or.inl (fle_neg_iff.mpr h)
    · exact Or.inr (fle_neg_iff.mpr h)
  · rw [card_image_of_injective _ hinj, sgnS_neg, card_image_of_injective _ opp_injective, ht]
  · rw [sgnS_neg, ← himg, image_image, image_image]
    apply image_congr
    intro c hc
    exact hanti c (hρ.2.1 c hc) (hbd c hc)
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := mem_image.mp hc
    obtain ⟨i, hi⟩ := hbd c' hc'
    exact ⟨i, by simp only [Pi.neg_apply]; omega⟩
  · intro h
    obtain ⟨c, hc⟩ := hρ.1
    have hnc : -c ∈ ρ := h ▸ mem_image_of_mem _ hc
    obtain ⟨i, hi⟩ := hbd c hc
    rcases hρ.2.2 c hc (-c) hnc with h' | h'
    · have := h' i; simp only [Pi.neg_apply] at this; unfold CLE at this; omega
    · have := h' i; simp only [Pi.neg_apply] at this; unfold CLE at this; omega

/-- There is an even number of tight boundary chains labelled by their sign vector: the
antipodal map pairs them off. -/
theorem card_isB_even (hm : 1 ≤ m)
    (hanti : ∀ c, InGrid m c → IsBdry m c → lab (-c) = opp (lab c)) :
    (#((nodes m).filter (IsB m lab)) : ZMod 2) = 0 := by
  rw [card_eq_sum_ones, Nat.cast_sum]
  refine sum_involution (fun ρ _ => ρ.image fun c => -c) (fun _ _ => by decide) ?_ ?_ ?_
  · intro ρ hρ _
    rw [mem_filter, mem_nodes] at hρ
    exact (isB_neg lab hm hanti hρ.1 hρ.2).2.2
  · intro ρ hρ
    rw [mem_filter, mem_nodes] at hρ ⊢
    obtain ⟨h1, h2, -⟩ := isB_neg lab hm hanti hρ.1 hρ.2
    exact ⟨h1, h2⟩
  · intro ρ _
    simp only [image_image]
    have : ((fun c : Fin n → ℤ => -c) ∘ fun c => -c) = id := funext fun c => neg_neg c
    rw [this, image_id]

/-- **Tucker's lemma on the barycentric subdivision of the cubical grid.** Let `lab`
assign a signed label `±1, …, ±n` to every face of the grid `[-m, m]ⁿ`, antipodally on
the boundary. Then two comparable faces (two vertices of one simplex of the
barycentric subdivision) carry opposite labels. -/
theorem tucker (hm : 1 ≤ m)
    (hanti : ∀ c, InGrid m c → IsBdry m c → lab (-c) = opp (lab c)) :
    ∃ a b, InGrid m a ∧ InGrid m b ∧ FLE a b ∧ lab a = opp (lab b) := by
  by_contra hcon
  have hno : ∀ a b, InGrid m a → InGrid m b → FLE a b → lab a ≠ opp (lab b) :=
    fun a b ha hb hab h => hcon ⟨a, b, ha, hb, hab, h⟩
  have hdc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (Door lab)
    (s := nodes (n := n) m) (t := nodes m)
  have h1 := congrArg (Nat.cast : ℕ → ZMod 2) hdc
  push_cast at h1
  simp only [bipartiteAbove, bipartiteBelow] at h1
  have hB : ∑ ρ ∈ nodes m, (if IsB m lab ρ then (1 : ZMod 2) else 0) = 0 := by
    rw [sum_boole]; exact card_isB_even lab hm hanti
  have h0node : ({0} : Finset (Fin n → ℤ)) ∈ nodes m := by
    refine mem_nodes.mpr ⟨singleton_nonempty 0, ?_, ?_⟩
    · intro c hc i
      rw [mem_singleton] at hc
      subst hc
      simp only [Pi.zero_apply]
      omega
    · intro a ha b hb
      rw [mem_singleton] at ha hb
      subst ha hb
      exact Or.inl (FLE.refl 0)
  rw [sum_congr rfl fun ρ hρ => card_up lab hm hno (mem_nodes.mp hρ),
    sum_congr rfl fun τ hτ => card_down lab (mem_nodes.mp hτ), sum_add_distrib,
    sum_add_distrib, hB, sum_ite_eq', if_pos h0node] at h1
  exact absurd (add_left_cancel h1) (by decide)

end Tucker

/-! ### From Tucker's lemma to zeros of maps on the cube -/

section Cube

/-- For the sup norm, a coordinate of largest absolute value realises the norm. -/
theorem norm_eq_abs_of_max {n : ℕ} {v : Fin n → ℝ} {i : Fin n} (h : ∀ j, |v j| ≤ |v i|) :
    ‖v‖ = |v i| := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j => by
      rw [Real.norm_eq_abs]; exact h j
  · rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i

/-- A coordinate where `a` is largest. It depends on `a` only, which makes the labelling
built from it antipodal. -/
noncomputable def maxIdx {k : ℕ} (a : Fin (k + 1) → ℝ) : Fin (k + 1) :=
  Classical.choose (Finite.exists_max a)

theorem le_maxIdx {k : ℕ} (a : Fin (k + 1) → ℝ) (j : Fin (k + 1)) : a j ≤ a (maxIdx a) :=
  Classical.choose_spec (Finite.exists_max a) j

/-- Two reals of absolute value at least `δ` whose distance is less than `δ` have the same
sign. -/
theorem pos_iff_of_close {δ u w : ℝ} (hu : δ ≤ |u|) (hw : δ ≤ |w|) (huw : |u - w| < δ) :
    (0 < u ↔ 0 < w) := by
  rw [abs_lt] at huw
  rcases le_or_gt 0 u with hu0 | hu0 <;> rcases le_or_gt 0 w with hw0 | hw0
  · rw [abs_of_nonneg hu0] at hu; rw [abs_of_nonneg hw0] at hw
    constructor <;> intro <;> linarith
  · rw [abs_of_nonneg hu0] at hu; rw [abs_of_neg hw0] at hw
    constructor <;> intro <;> linarith
  · rw [abs_of_neg hu0] at hu; rw [abs_of_nonneg hw0] at hw
    constructor <;> intro <;> linarith
  · constructor <;> intro <;> linarith

/-- **The cube form of Borsuk–Ulam.** A map continuous on the cube `[-1, 1]ⁿ` (the closed
unit ball of the sup norm) and odd on its boundary vanishes somewhere in the cube.

If it did not, `‖F‖ ≥ δ > 0` on the cube. Label each face `c` of a fine grid by the
coordinate where `|F|` is largest at the barycentre of `c`, with the sign of `F` there;
oddness makes the labelling antipodal on the boundary. Tucker's lemma gives two
comparable faces with opposite labels. Their barycentres are close, but `F` has
coordinates `≥ δ` and `≤ -δ` there, which uniform continuity forbids. -/
theorem cube_zero {n : ℕ} (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContinuousOn F (Metric.closedBall 0 1))
    (hodd : ∀ x ∈ Metric.sphere (0 : Fin n → ℝ) 1, F (-x) = -F x) :
    ∃ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, F x = 0 := by
  by_contra hcon
  push Not at hcon
  obtain _ | k := n
  · exact hcon 0 (Metric.mem_closedBall_self zero_le_one) (Subsingleton.elim _ _)
  have hK : IsCompact (Metric.closedBall (0 : Fin (k + 1) → ℝ) 1) := isCompact_closedBall 0 1
  obtain ⟨x₀, hx₀, hmin⟩ :=
    hK.exists_isMinOn (Metric.nonempty_closedBall.mpr zero_le_one) hF.norm
  have hδ : 0 < ‖F x₀‖ := norm_pos_iff.mpr (hcon x₀ hx₀)
  have hδle : ∀ x ∈ Metric.closedBall (0 : Fin (k + 1) → ℝ) 1, ‖F x₀‖ ≤ ‖F x‖ :=
    fun x hx => hmin hx
  obtain ⟨η, hη, hunif⟩ :=
    Metric.uniformContinuousOn_iff.mp (hK.uniformContinuousOn_of_continuous hF) _ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hm : 1 ≤ N + 1 := by omega
  have hmpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hmη : 1 / (2 * ((N + 1 : ℕ) : ℝ)) < η := by
    have h1 : 1 / η < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    rw [div_lt_iff₀ hη] at h1
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  set M : ℝ := 2 * ((N + 1 : ℕ) : ℝ) with hM
  have hMpos : 0 < M := by positivity
  -- barycentres of the faces
  let pt : (Fin (k + 1) → ℤ) → (Fin (k + 1) → ℝ) := fun c i => (c i : ℝ) / M
  have hpt_abs : ∀ c i, |pt c i| = |(c i : ℝ)| / M := fun c i => by
    simp only [pt, abs_div, abs_of_pos hMpos]
  have hpt_grid : ∀ c, InGrid (N + 1) c → pt c ∈ Metric.closedBall 0 1 := by
    intro c hc
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs, hpt_abs, div_le_one hMpos, hM]
    have h2 : |c i| ≤ 2 * ((N + 1 : ℕ) : ℤ) := abs_le.mpr (hc i)
    exact_mod_cast h2
  have hpt_bdry : ∀ c, InGrid (N + 1) c → IsBdry (N + 1) c → pt c ∈ Metric.sphere 0 1 := by
    intro c hc hb
    rw [mem_sphere_zero_iff_norm]
    apply le_antisymm (mem_closedBall_zero_iff.mp (hpt_grid c hc))
    obtain ⟨i, hi⟩ := hb
    have hci : |(c i : ℝ)| = M := by
      rcases hi with hi | hi
      · rw [hi, hM]; push_cast; exact abs_of_pos (by positivity)
      · rw [hi, hM]; push_cast; rw [abs_neg]; exact abs_of_pos (by positivity)
    have : |pt c i| = 1 := by rw [hpt_abs, hci, div_self hMpos.ne']
    rw [← this, ← Real.norm_eq_abs]
    exact norm_le_pi_norm _ i
  have hpt_neg : ∀ c, pt (-c) = -pt c := fun c => by
    funext i; simp only [pt, Pi.neg_apply, Int.cast_neg, neg_div]
  have hpt_dist : ∀ a b, FLE a b → dist (pt a) (pt b) < η := by
    intro a b hab
    refine lt_of_le_of_lt ((dist_pi_le_iff (by positivity)).mpr fun i => ?_) hmη
    rw [Real.dist_eq]
    have h1 : pt a i - pt b i = ((a i - b i : ℤ) : ℝ) / M := by
      simp only [pt]; push_cast; ring
    rw [h1, abs_div, abs_of_pos hMpos, div_le_div_iff_of_pos_right hMpos]
    have := (hab i).abs_sub
    have h2 : |a i - b i| ≤ 1 := abs_le.mpr ⟨by omega, by omega⟩
    exact_mod_cast h2
  -- the labelling
  let idx : (Fin (k + 1) → ℤ) → Fin (k + 1) := fun c => maxIdx fun i => |F (pt c) i|
  have hidx : ∀ c j, |F (pt c) j| ≤ |F (pt c) (idx c)| := fun c =>
    le_maxIdx fun i => |F (pt c) i|
  have hnorm : ∀ c, InGrid (N + 1) c → ‖F x₀‖ ≤ |F (pt c) (idx c)| := fun c hc =>
    norm_eq_abs_of_max (hidx c) ▸ hδle _ (hpt_grid c hc)
  let lab : (Fin (k + 1) → ℤ) → Label (k + 1) := fun c => (idx c, decide (0 < F (pt c) (idx c)))
  have hanti : ∀ c, InGrid (N + 1) c → IsBdry (N + 1) c → lab (-c) = opp (lab c) := by
    intro c hc hb
    have hF' : F (pt (-c)) = -F (pt c) := by rw [hpt_neg]; exact hodd _ (hpt_bdry c hc hb)
    have hi : idx (-c) = idx c := by
      show maxIdx _ = maxIdx _
      congr 1
      funext i
      rw [hF', Pi.neg_apply, abs_neg]
    have hv : F (pt c) (idx c) ≠ 0 := fun h => by
      have := hnorm c hc; rw [h, abs_zero] at this; linarith
    simp only [lab, opp, hi, hF', Pi.neg_apply, Prod.mk.injEq, true_and, Left.neg_pos_iff]
    rcases lt_or_gt_of_ne hv with h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h, not_lt.mpr h.le]
  obtain ⟨a, b, ha, hb, hab, hlab⟩ := tucker lab hm hanti
  have hi : idx a = idx b := congrArg Prod.fst hlab
  have hs : decide (0 < F (pt a) (idx a)) = !decide (0 < F (pt b) (idx b)) :=
    congrArg Prod.snd hlab
  have hd : dist (F (pt a)) (F (pt b)) < ‖F x₀‖ :=
    hunif _ (hpt_grid a ha) _ (hpt_grid b hb) (hpt_dist a b hab)
  have hcoord : |F (pt a) (idx b) - F (pt b) (idx b)| < ‖F x₀‖ := by
    rw [← Real.dist_eq]; exact lt_of_le_of_lt (dist_le_pi_dist _ _ _) hd
  have hsame := pos_iff_of_close (by rw [← hi]; exact hnorm a ha) (hnorm b hb) hcoord
  rw [hi] at hs
  by_cases h : 0 < F (pt b) (idx b)
  · simp [h, hsame.mpr h] at hs
  · simp [h, (not_congr hsame).mpr h] at hs

end Cube

/-! ### From the cube to spheres -/

section Sphere

variable {n : ℕ}

/-- The point `(y, 1 - ‖y‖)` of `ℝⁿ⁺¹`, for `y` in `ℝⁿ` with the sup norm. On the
boundary of the cube its last coordinate vanishes. -/
noncomputable def lift (y : Fin n → ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i : Fin (n + 1) => if h : (i : ℕ) < n then y ⟨i, h⟩ else 1 - ‖y‖)

theorem continuous_lift : Continuous (lift (n := n)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  by_cases h : (i : ℕ) < n
  · simp only [h, dif_pos]; exact continuous_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact continuous_const.sub continuous_norm

theorem lift_ne_zero (y : Fin n → ℝ) : lift y ≠ 0 := by
  intro h
  have hy : y = 0 := by
    funext i
    have := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v (Fin.castSucc i)) h
    simpa [lift] using this
  have := congrArg (fun v : EuclideanSpace ℝ (Fin (n + 1)) => v (Fin.last n)) h
  simp [lift, hy] at this

theorem lift_neg {y : Fin n → ℝ} (hy : ‖y‖ = 1) : lift (-y) = -lift y := by
  apply PiLp.ext
  intro i
  by_cases h : (i : ℕ) < n
  · simp [lift, h]
  · simp [lift, h, hy]

end Sphere

end BorsukUlam

open BorsukUlam in
/-- **The Borsuk–Ulam theorem.** There is no continuous map `Sⁿ → Sⁿ⁻¹` that is odd.

Precomposing such a map with `y ↦ (y, 1 - ‖y‖) / ‖(y, 1 - ‖y‖)‖`, which sends the cube
`[-1, 1]ⁿ` into `Sⁿ` and is odd on the boundary of the cube, would give a map on the cube,
odd on its boundary, with values on the unit sphere, hence without zero. This
contradicts `cube_zero`. -/
theorem borsuk_ulam_general (n : ℕ) :
    ¬ ∃ φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n),
        ContinuousOn φ (Metric.sphere 0 1) ∧
        Set.MapsTo φ (Metric.sphere 0 1) (Metric.sphere 0 1) ∧
        ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, φ (-x) = -φ x := by
  rintro ⟨φ, hcont, hmaps, hodd⟩
  have hne : ∀ y : Fin n → ℝ, ‖lift y‖ ≠ 0 := fun y => norm_ne_zero_iff.mpr (lift_ne_zero y)
  let s : (Fin n → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) := fun y => ‖lift y‖⁻¹ • lift y
  have hs_cont : Continuous s := (continuous_lift.norm.inv₀ hne).smul continuous_lift
  have hs_sphere : ∀ y, s y ∈ Metric.sphere 0 1 := fun y => by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hne y)]
  have hs_neg : ∀ y ∈ Metric.sphere (0 : Fin n → ℝ) 1, s (-y) = -s y := by
    intro y hy
    simp only [s, lift_neg (mem_sphere_zero_iff_norm.mp hy), norm_neg, smul_neg]
  let F : (Fin n → ℝ) → (Fin n → ℝ) := fun y => WithLp.ofLp (φ (s y))
  have hF : ContinuousOn F (Metric.closedBall 0 1) :=
    (PiLp.continuous_ofLp 2 _).comp_continuousOn
      (hcont.comp hs_cont.continuousOn fun y _ => hs_sphere y)
  have hFodd : ∀ y ∈ Metric.sphere (0 : Fin n → ℝ) 1, F (-y) = -F y := by
    intro y hy
    simp only [F, hs_neg y hy, hodd _ (hs_sphere y), WithLp.ofLp_neg]
  obtain ⟨y, -, hy⟩ := cube_zero F hF hFodd
  have h1 : φ (s y) = 0 := by simpa [F] using hy
  have h2 := hmaps (hs_sphere y)
  rw [h1, mem_sphere_zero_iff_norm, norm_zero] at h2
  exact zero_ne_one h2


end MorseFloer
