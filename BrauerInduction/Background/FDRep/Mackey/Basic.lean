import BrauerInduction.Background.FDRep.ConjMap
import BrauerInduction.Background.FDRep.Basic
import BrauerInduction.Background.Group.DoubleCoset

/-!
# Mackey summands for induced representations

This file defines the representation-theoretic summands that occur in the Mackey
decomposition for `Res Ind`.

For a subgroup `I ≤ G`, a representation `σ` of `I`, and an element `g : G`, the
relevant subgroup is

`I ∩ gIg⁻¹`.

There are two representations of this subgroup: the restriction of `σ`, and the
restriction of the conjugate representation. The Hom space between these two
representations is the Mackey Hom term associated to `g`.

The character computations for these terms are developed in
`FDRep.Mackey.Character`.
-/

open CategoryTheory

universe u v

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/-
These two helpers are good general `FDRep` API. If they already exist in your
basic file, delete the local versions below and use the global names.
-/

/--
The conjugate subgroup `gIg⁻¹`.
-/
abbrev mackeyConjSubgroup (I : Subgroup G) (g : G) : Subgroup G :=
  I.map (MulAut.conj g).toMonoidHom

/--
The Mackey intersection `I ∩ gIg⁻¹`.
-/
abbrev mackeyIntersection (I : Subgroup G) (g : G) : Subgroup G :=
  I ⊓ mackeyConjSubgroup I g

/--
The restriction of `σ` to the Mackey intersection `I ∩ gIg⁻¹` through the left
inclusion into `I`.
-/
noncomputable abbrev mackeyLeftRes
    (I : Subgroup G) (σ : FDRep k I) (g : G) :
    FDRep k (mackeyIntersection I g) :=
  FDRep.of (σ.ρ.comp (Subgroup.inclusion inf_le_left))

/--
The restriction of the conjugate representation `σᵍ` to the Mackey intersection
`I ∩ gIg⁻¹`.
-/
noncomputable abbrev mackeyConjRes
    (I : Subgroup G) (σ : FDRep k I) (g : G) :
    FDRep k (mackeyIntersection I g) :=
  let σg := FDRep.conjMap (k := k) I g σ
  FDRep.of (σg.ρ.comp (Subgroup.inclusion inf_le_right))

/--
The Mackey Hom term attached to `g`, namely the Hom space from the left
restriction of `σ` to the conjugate restriction of `σ`.
-/
abbrev mackeyHomTerm
    (I : Subgroup G) (σ : FDRep k I) (g : G) : Type _ :=
  mackeyLeftRes (k := k) I σ g ⟶
    mackeyConjRes (k := k) I σ g

/--
If `g ∈ I`, then the Mackey intersection `I ∩ gIg⁻¹` is identified with `I`.
-/
noncomputable def mackeyIntersectionEquivOfMem
    (I : Subgroup G) (g : G) (hg : g ∈ I) :
    mackeyIntersection I g ≃* I where
  toFun x :=
    ⟨(x : G), x.2.1⟩
  invFun x :=
    ⟨(x : G), by
      constructor
      · exact x.2
      · refine ⟨(MulAut.conj g).symm (x : G), ?_, ?_⟩
        · have hmem : g⁻¹ * (x : G) * g ∈ I :=
            I.mul_mem (I.mul_mem (I.inv_mem hg) x.2) hg
          simpa [MulAut.conj_symm_apply] using hmem
        · simpa using (MulAut.conj g).apply_symm_apply (x : G)⟩
  left_inv x := by
    ext
    rfl
  right_inv x := by
    ext
    rfl
  map_mul' x y := by
    ext
    rfl

/--
If `g ∈ I`, then the two representations in the Mackey term over `I ∩ I^g` are
isomorphic.

The isomorphism is induced by the action of `g⁻¹` on `σ`.
-/
noncomputable def mackeyConjResIsoLeftResOfMem
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G)
    (hg : g ∈ I) :
    mackeyLeftRes (k := k) I σ g ≅
      mackeyConjRes (k := k) I σ g := by
  let H : Subgroup G := mackeyIntersection I g
  let L : FDRep k H := mackeyLeftRes (k := k) I σ g
  let C : FDRep k H := mackeyConjRes (k := k) I σ g
  let gI : I := ⟨g, hg⟩
  let gInvI : I := ⟨g⁻¹, I.inv_mem hg⟩

  let e : L.V.obj ≃ₗ[k] C.V.obj := by
    change σ.V.obj ≃ₗ[k] σ.V.obj
    exact rhoLinearEquiv σ gInvI

  refine FDRep.isoOfLinearEquiv e ?_
  intro h
  apply LinearMap.ext
  intro v
  -- `isoOfLinearEquiv` wants `C.ρ h (e v) = e (L.ρ h v)`.
  -- The following is the old intertwining calculation, with `.rep` removed.
  symm
  change
    σ.ρ gInvI (σ.ρ ⟨(h : G), h.2.1⟩ v)
      =
    σ.ρ (((MulAut.conj g).subgroupMap I).symm
        ⟨(h : G), h.2.2⟩)
      (σ.ρ gInvI v)
  calc
    σ.ρ gInvI (σ.ρ ⟨(h : G), h.2.1⟩ v)
        = σ.ρ (gInvI * ⟨(h : G), h.2.1⟩) v := by
            rw [map_mul]
            rfl
    _ =
      σ.ρ
        ((((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩) * gInvI) v := by
            have hmul :
                gInvI * ⟨(h : G), h.2.1⟩
                  =
                (((MulAut.conj g).subgroupMap I).symm
                  ⟨(h : G), h.2.2⟩) * gInvI := by
              apply Subtype.ext
              simp [gInvI]
            exact congrArg (fun x : I => σ.ρ x v) hmul
    _ =
      σ.ρ (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
        (σ.ρ gInvI v) := by
            rw [map_mul]
            rfl

/--
An endomorphism of the left Mackey restriction gives an endomorphism of `σ` when
`g ∈ I`, using the identification `I ∩ gIg⁻¹ ≃ I`.
-/
noncomputable def mackeyLeftResEndToEndOfMem
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G)
    (hg : g ∈ I) :
    (mackeyLeftRes (k := k) I σ g ⟶
      mackeyLeftRes (k := k) I σ g)
      →ₗ[k]
    (σ ⟶ σ) := by
  let H : Subgroup G := mackeyIntersection I g
  let L : FDRep k H := mackeyLeftRes (k := k) I σ g
  let eH : H ≃* I := mackeyIntersectionEquivOfMem I g hg
  refine
  { toFun := ?toFun
    map_add' := ?map_add
    map_smul' := ?map_smul }
  · intro f
    let fLin : σ →ₗ[k] σ := by
      change L →ₗ[k] L
      exact FDRep.homToLinearMap f
    refine homOfLinearMap (X := σ) (Y := σ) fLin ?_
    intro i
    apply LinearMap.ext
    intro v
    let h : H := eH.symm i
    have hcomm :
        homToLinearMap f (L.ρ h v) = L.ρ h (homToLinearMap f v) :=
      homToLinearMap_rho_apply f h v
    have hi : Subgroup.inclusion inf_le_left h = i := by
      change eH h = i
      simp [h]
    exact LinearMap.mem_eqLocus.mp hcomm
  · intro f₁ f₂
    ext v
    rfl
  · intro c f
    ext v
    rfl

/--
Restricting an endomorphism of `σ` gives an endomorphism of the left Mackey
restriction.
-/
noncomputable def mackeyLeftResEndFromEndOfMem
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) :
    (σ ⟶ σ) →ₗ[k]
      (mackeyLeftRes (k := k) I σ g ⟶
        mackeyLeftRes (k := k) I σ g) := by
  let H : Subgroup G := mackeyIntersection I g
  let L : FDRep k H := mackeyLeftRes (k := k) I σ g
  refine
  { toFun := ?toFun
    map_add' := ?map_add
    map_smul' := ?map_smul }
  · intro c
    let cLin : L →ₗ[k] L := by
      change σ →ₗ[k] σ
      exact homToLinearMap c
    refine homOfLinearMap (X := L) (Y := L) cLin ?_
    intro h
    apply LinearMap.ext
    intro v
    have hcomm :
        homToLinearMap c
          (σ.ρ (Subgroup.inclusion inf_le_left h) v)
          =
        σ.ρ (Subgroup.inclusion inf_le_left h)
          (homToLinearMap c v) :=
      homToLinearMap_rho_apply c (Subgroup.inclusion inf_le_left h) v
    simpa [cLin, L] using hcomm
  · intro c₁ c₂
    ext v
    rfl
  · intro a c
    ext v
    rfl

/--
When `g ∈ I`, endomorphisms of the left Mackey restriction are linearly
equivalent to endomorphisms of `σ`.
-/
noncomputable def mackeyLeftResEndEquivEndOfMem
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G)
    (hg : g ∈ I) :
    (mackeyLeftRes (k := k) I σ g ⟶
      mackeyLeftRes (k := k) I σ g)
      ≃ₗ[k]
    (σ ⟶ σ) := by
  let F := mackeyLeftResEndToEndOfMem (k := k) I σ g hg
  let R := mackeyLeftResEndFromEndOfMem (k := k) I σ g
  refine
  { toFun := F
    invFun := R
    left_inv := ?left_inv
    right_inv := ?right_inv
    map_add' := ?map_add
    map_smul' := ?map_smul }
  · intro f y
    ext v
    rfl
  · intro c x
    ext v
    rfl
  · intro f₂
    ext v
    rfl
  · intro a
    ext v
    rfl

/--
If `g ∈ I`, then the Mackey Hom term over `g` has the same dimension as
`End(σ)`.
-/
lemma finrank_mackeyHomTerm_eq_end_of_mem
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G)
    (hg : g ∈ I) :
    Module.finrank k
      (mackeyHomTerm (k := k) I σ g)
      =
    Module.finrank k (σ ⟶ σ) := by
  let L : FDRep k (mackeyIntersection I g) :=
    mackeyLeftRes (k := k) I σ g
  let C : FDRep k (mackeyIntersection I g) :=
    mackeyConjRes (k := k) I σ g
  let eLC : L ≅ C :=
    mackeyConjResIsoLeftResOfMem (k := k) I σ g hg
  calc
    Module.finrank k (mackeyHomTerm (k := k) I σ g)
        =
      Module.finrank k (L ⟶ L) := by
        exact
          (LinearEquiv.finrank_eq
            (FDRep.postcompIsoLinearEquiv
              (X := L) (Y := L) (Z := C) eLC)).symm
    _ =
      Module.finrank k (σ ⟶ σ) := by
        exact LinearEquiv.finrank_eq
          (mackeyLeftResEndEquivEndOfMem
            (k := k) I σ g hg)

/--
The Mackey Hom term for a representative of the identity double coset has the
same dimension as `End(σ)`.
-/
lemma finrank_mackeyHomTerm_oneDC_eq_end
    (I : Subgroup G)
    (σ : FDRep k I) :
    Module.finrank k
      (mackeyHomTerm
        (k := k) I σ
        (Quotient.out (DoubleCoset.oneDC (G := G) I)))
      =
    Module.finrank k (σ ⟶ σ) := by
  exact finrank_mackeyHomTerm_eq_end_of_mem
    (k := k) I σ
    (Quotient.out (DoubleCoset.oneDC (G := G) I))
    (DoubleCoset.out_oneDC_mem (G := G) I)

end FDRep
