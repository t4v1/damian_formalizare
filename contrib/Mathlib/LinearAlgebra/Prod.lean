/-
Copyright (c) 2026 Octavian Halmaghi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Octavian Halmaghi
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Products of submodules, as modules

Two isomorphisms that `Mathlib.LinearAlgebra.Prod` does not have. They belong in
that file's `Submodule` section, beside `Submodule.prod`; the second needs
`Mathlib.LinearAlgebra.Isomorphisms`, so it may prefer to live there instead.

* `Submodule.prodEquiv` : `↥(p.prod q) ≃ₗ ↥p × ↥q`
* `Submodule.quotientProdEquiv` : `(M × N) ⧸ p.prod q ≃ₗ (M ⧸ p) × (N ⧸ q)`

The first says the submodule `p × q` of `M × N` *is* the product module; the
second says the cokernel of a direct sum is the direct sum of the cokernels.
Together they let a rank computation on `f.prodMap g` be split into one on `f`
and one on `g`.
-/

namespace Submodule

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The submodule `p × q` of `M × N`, viewed as a module, is the product of `p`
and `q`. -/
def prodEquiv (p : Submodule R M) (q : Submodule R N) : p.prod q ≃ₗ[R] p × q where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun w := ⟨(w.1.1, w.2.1), ⟨w.1.2, w.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem prodEquiv_apply (p : Submodule R M) (q : Submodule R N) (z : p.prod q) :
    prodEquiv p q z = (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩) := rfl

/-- The quotient of `M × N` by `p × q` is the product of the two quotients. -/
noncomputable def quotientProdEquiv (p : Submodule R M) (q : Submodule R N) :
    ((M × N) ⧸ p.prod q) ≃ₗ[R] (M ⧸ p) × (N ⧸ q) := by
  have hsurj : Function.Surjective (p.mkQ.prodMap q.mkQ) := by
    rintro ⟨a, b⟩
    obtain ⟨a', rfl⟩ := p.mkQ_surjective a
    obtain ⟨b', rfl⟩ := q.mkQ_surjective b
    exact ⟨(a', b'), rfl⟩
  refine (quotEquivOfEq _ (LinearMap.ker (p.mkQ.prodMap q.mkQ)) ?_).trans
    (LinearMap.quotKerEquivOfSurjective _ hsurj)
  rw [LinearMap.ker_prodMap, ker_mkQ, ker_mkQ]

end Submodule
