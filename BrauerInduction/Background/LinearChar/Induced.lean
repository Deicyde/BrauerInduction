import BrauerInduction.Background.LinearChar.Basic
import BrauerInduction.Background.FDRep.InducedFinrank

/-!
# Induced representations attached to linear characters

This file defines induction and coinduction of the one-dimensional
representation associated to a linear character.

Character formulas are kept in `LinearChar.InducedCharacter`.
-/

universe u v

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace FDRep

open Module

/--
Induced Linear Representation: `Ind_H^G(ψ)`.
This is the atomic basis for Brauer's theorem.
-/
noncomputable def indLin (H : Subgroup G)
    (ψ : H →* kˣ) : FDRep k G :=
  FDRep.ind H (FDRep.ofLinearChar ψ)

/-- `Coind_H^G(ψ)` as an `FDRep`. -/
noncomputable def coindLin (H : Subgroup G)
    (ψ : H →* kˣ) : FDRep k G :=
  FDRep.coind H (FDRep.ofLinearChar ψ)

@[simp]
lemma coindLin_ρ_apply (H : Subgroup G) (ψ : H →* kˣ)
    (g : G) (v : (FDRep.coindLin H ψ)) (x : G) :
    ((FDRep.coindLin H ψ).ρ g v).1 x = v.1 (x * g) := rfl

/--
For linear characters, induction and coinduction agree through the general
finite-group induction/coinduction isomorphism.
-/
noncomputable def indLinCoindLinIso
    (H : Subgroup G) (ψ : H →* kˣ) :
    FDRep.indLin H ψ ≅ FDRep.coindLin H ψ := by
  unfold FDRep.indLin FDRep.coindLin
  exact FDRep.indIsoCoind H (FDRep.ofLinearChar ψ)


open Classical in
/--
An isomorphism to `indLin` is equivalent to an isomorphism to `coindLin`.
-/
lemma nonempty_iso_indLin_iff_coindLin
    (ρ : FDRep k G) (H : Subgroup G) (ψ : H →* kˣ) :
    Nonempty (ρ ≅ FDRep.indLin (k := k) (G := G) H ψ) ↔
    Nonempty (ρ ≅ FDRep.coindLin (k := k) (G := G) H ψ) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i ≪≫ FDRep.indLinCoindLinIso (k := k) (G := G) H ψ⟩
  · rintro ⟨i⟩
    exact ⟨i ≪≫ (FDRep.indLinCoindLinIso (k := k) (G := G) H ψ).symm⟩

/--
Transporting a stable linear-character representation along a group equivalence
gives the stable linear-character representation obtained by precomposing with
the inverse equivalence.

This same-universe version is the one needed for subgroup transport, such as
`H ≃* H.map I.subtype`.
-/
noncomputable def ofLinearChar_transportEquiv_iso
    {Γ Δ : Type v} [Group Γ] [Group Δ]
    (e : Γ ≃* Δ)
    (θ : Γ →* kˣ) :
    ((FDRep.transportEquiv (k := k) e).functor.obj
        (FDRep.ofLinearChar θ))
      ≅
    FDRep.ofLinearChar (θ.comp e.symm.toMonoidHom) := by
  rfl

/--
Transitivity of induction for representations induced from linear
characters. If `H ≤ I ≤ G` and `θ` is a linear character of `H`, then inducing
`indLin H θ` from `I` to `G` agrees with inducing the transported character
from the image of `H` as a subgroup of `G`.
-/
noncomputable def indLin_trans
    (I : Subgroup G)
    (H : Subgroup I)
    (θ : H →* kˣ) :
    let HG : Subgroup G := H.map I.subtype
    let e : H ≃* HG :=
      H.equivMapOfInjective I.subtype Subtype.coe_injective
    let θG : HG →* kˣ :=
      θ.comp e.symm.toMonoidHom
    FDRep.ind I (FDRep.indLin H θ) ≅ FDRep.indLin HG θG := by
  dsimp
  let HG : Subgroup G := H.map I.subtype
  let e : H ≃* HG :=
    H.equivMapOfInjective I.subtype Subtype.coe_injective
  let θG : HG →* kˣ :=
    θ.comp e.symm.toMonoidHom
  let σlin : FDRep k H :=
    FDRep.ofLinearChar θ
  change
    FDRep.ind I (FDRep.ind H σlin) ≅
      FDRep.ind HG (FDRep.ofLinearChar θG)
  let hstage :
      FDRep.ind I (FDRep.ind H σlin) ≅
        FDRep.ind HG
          (FDRep.transport
            (H.equivMapOfInjective I.subtype Subtype.coe_injective) σlin) :=
    FDRep.indTrans (k := k) (G := G) (I := I) (H := H) σlin
  let hsrc :
      ((FDRep.transportEquiv (k := k) e).functor.obj σlin) ≅
        FDRep.ofLinearChar θG :=
    FDRep.ofLinearChar_transportEquiv_iso e θ
  exact
    hstage ≪≫
      ((FDRep.indHomFunctor (G := HG) (H := G) HG.subtype).mapIso hsrc)

/--
The dimension of a representation induced from a linear character, expressed
using the right-coset quotient.
-/
@[simp]
theorem finrank_indLin_rightRel
    {k : Type u} [Field k]
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (ψ : H →* kˣ) :
    (FDRep.indLin H ψ).finrank =
      Nat.card (Quotient (QuotientGroup.rightRel H)) := by
  classical
  dsimp [FDRep.indLin]
  rw [FDRep.finrank_ind_rightRel]
  simp only [finrank_ofLinearChar, mul_one]

end FDRep
