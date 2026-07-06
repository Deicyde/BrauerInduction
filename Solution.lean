import Mathlib
import BrauerInduction.Main

open scoped BigOperators

universe u

namespace BrauerChallenge

/--
An element is `p`-regular if its order is coprime to `p`.
-/
def IsPRegular {G : Type u} [Group G] (p : ℕ) (g : G) : Prop :=
  Nat.Coprime (orderOf g) p

/--
A group `G` is `p`-elementary if it is the product of a cyclic `p`-regular
subgroup `C` and a `p`-group `P`, with `C` centralizing `P`.

The structure is data-bearing: it records chosen subgroups `C` and `P`.
The corresponding proposition is usually expressed as
`Nonempty (PElementary p G)`, or equivalently `IsPElementary p G`.
-/
structure PElementary (p : ℕ) (G : Type u) [Group G] where
  protected C : Subgroup G
  protected P : Subgroup G
  protected C_isCyclic : IsCyclic C
  protected P_isPGroup : IsPGroup p P
  protected C_isPRegular : ∀ {c : G}, c ∈ C → IsPRegular p c
  protected comm : ∀ {c q : G}, c ∈ C → q ∈ P → Commute c q
  protected decompose : ∀ h : G, ∃ c ∈ C, ∃ q ∈ P, c * q = h

/--
A group is Brauer elementary if it is `p`-elementary for some prime `p`.
-/
def IsBrauerElementary (G : Type u) [Group G] : Prop :=
  ∃ p : ℕ, p.Prime ∧ Nonempty (PElementary p G)

section Induction

namespace FDRep

variable {k : Type u} [CommRing k]
variable {G H : Type u} [Group G] [Group H]

noncomputable abbrev asRep
    {k : Type u} [CommRing k]
    {G : Type v} [Monoid G]
    (V : FDRep k G) : Rep k G :=
  (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).obj V

/--
Induction of a finite-dimensional representation along a group homomorphism.
-/
noncomputable def indHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    FDRep k H := by
  let A : Rep k G := asRep σ
  let τind : Rep k H := Rep.ind φ A
  have h_fin_τ : Module.Finite k τind.V := by
    letI : Fintype H := Fintype.ofFinite H
    haveI : Module.Finite k A.V := by
      change Module.Finite k σ
      infer_instance
    exact Module.Finite.of_surjective
      (Representation.Coinvariants.mk _) (Submodule.mkQ_surjective _)
  haveI : Module.Finite k τind.V := h_fin_τ
  exact FDRep.of τind.ρ

/-- Induction from a subgroup defined a special case of `indHom`. -/
noncomputable abbrev ind [Finite G] (H : Subgroup G) (σ : FDRep k H) : FDRep k G :=
  indHom H.subtype σ

end Induction.FDRep

section LinearChar

namespace FDRep

variable {k : Type u} [CommRing k]

/--
The one-dimensional representation associated to a linear character
`ψ : G →* kˣ`.
-/
noncomputable def ofLinearChar
    {G : Type u} [Monoid G]
    (ψ : G →* kˣ) : FDRep k G :=
  let ρ : Representation k G k :=
  { toFun := fun g => (ψ g : k) • LinearMap.id
    map_one' := by
      ext
      simp
    map_mul' := by
      intro x y
      ext
      simp [mul_comm] }
  FDRep.of ρ

/--
The representation induced from the one-dimensional representation attached to
a linear character of a subgroup.
-/
noncomputable def indLin {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (ψ : H →* kˣ) : FDRep k G :=
    FDRep.ind H (ofLinearChar ψ)

end FDRep

end LinearChar

/--
Brauer's induction theorem, stated using only Mathlib vocabulary plus the
definitions in this file.

Every character of a finite-dimensional representation of a finite group over an
algebraically closed field of characteristic zero is an integer linear
combination of characters induced from linear characters of Brauer elementary
subgroups.
-/
theorem character_eq_sum_induced_linear
    {G : Type u} [Group G] [Finite G]
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    (V : FDRep k G) :
    ∃ (ι : Type) (_ : Fintype ι)
      (ns : ι → ℤ)
      (Hs : ι → Subgroup G)
      (ψs : ∀ i, Hs i →* kˣ),
      (∀ i, IsBrauerElementary (Hs i)) ∧
      V.character =
          ∑ i, ns i •
            (FDRep.indLin (k := k) (G := G) (Hs i) (ψs i)).character := by
  rcases BrauerInduction.character_eq_sum_induced_linear (k := k) (G := G) V with
    ⟨ι, hι, ns, Hs, ψs, hElem, hsum⟩
  refine ⟨ι, hι, ns, Hs, ψs, ?_, ?_⟩
  · intro i
    rcases hElem i with ⟨p, hp, hpe⟩
    dsimp [BrauerInduction.IsPElementary] at hpe
    rcases hpe with ⟨E⟩
    refine ⟨p, hp, ⟨?_⟩⟩
    exact
    { C := E.C
      P := E.P
      C_isCyclic := E.C_isCyclic
      C_isPRegular := by
        intro c hc
        simpa [BrauerChallenge.IsPRegular, _root_.IsPRegular] using E.C_isPRegular hc
      P_isPGroup := E.P_isPGroup
      comm := E.comm
      decompose := E.decompose }
  · trans
      ∑ i, ns i •
        (_root_.FDRep.indLin (k := k) (G := G) (Hs i) (ψs i)).character
    · exact hsum
    · apply Finset.sum_congr rfl
      intro i hi
      rw [_root_.FDRep.indLin_eq_of_rep_ind]
      rfl

/-- Every Brauer-elementary group is solvable (elementary ⇒ nilpotent ⇒ solvable),
    bridging the challenge predicate through the project's `IsBrauerElementary.isNilpotent`. -/
theorem IsBrauerElementary.isSolvable
    {G : Type u} [Group G] [Finite G]
    (h : IsBrauerElementary G) : IsSolvable G := by
  obtain ⟨p, hp, ⟨E⟩⟩ := h
  have hBI : BrauerInduction.IsBrauerElementary G := by
    refine ⟨p, hp, ⟨?_⟩⟩
    exact
    { C := E.C
      P := E.P
      C_isCyclic := E.C_isCyclic
      C_isPRegular := by
        intro c hc
        simpa [BrauerChallenge.IsPRegular, _root_.IsPRegular] using E.C_isPRegular hc
      P_isPGroup := E.P_isPGroup
      comm := E.comm
      decompose := E.decompose }
  haveI : Group.IsNilpotent G := hBI.isNilpotent
  infer_instance

/-- Trivial-character bridge: the character of the challenge's trivial linear representation
    equals that of Mathlib's trivial representation `(1 : Representation k G k)`. -/
theorem lhs_bridge {G : Type u} [Group G] [Finite G] {k : Type u} [Field k] :
    (FDRep.ofLinearChar (1 : G →* kˣ)).character
      = (1 : Representation k G k).character := by
  have hρ : (FDRep.ofLinearChar (1 : G →* kˣ)).ρ = (1 : Representation k G k) := by
    apply MonoidHom.ext; intro g; apply LinearMap.ext; intro x
    change (_root_.FDRep.ofLinearChar (1 : G →* kˣ)).ρ g x = (1 : G →* Module.End k k) g x
    simp [Module.End.one_apply]
  exact congrArg Representation.character hρ

/--
The user corollary, stated in pure Mathlib vocabulary and proved from the previous
(elementary) challenge theorem `character_eq_sum_induced_linear`.

The character of the trivial one-dimensional representation is an integer linear
combination of characters of representations induced from linear characters of
*solvable* subgroups.
-/
theorem trivialChar_eq_sum_induced_linear_solvable
    {G : Type u} [Group G] [Finite G]
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] :
    ∃ (ι : Type) (_ : Fintype ι)
      (ns : ι → ℤ)
      (Hs : ι → Subgroup G)
      (ψs : ∀ i, Hs i →* kˣ),
      (∀ i, IsSolvable (Hs i)) ∧
        (1 : Representation k G k).character =
          ∑ i, ns i •
            (Representation.ind (Hs i).subtype
              ((algebraMap k (Module.End k k)).toMonoidHom.comp
                ((Units.coeHom k).comp (ψs i)))).character := by
  obtain ⟨ι, hι, ns, Hs, ψs, hElem, hsum⟩ :=
    character_eq_sum_induced_linear (FDRep.ofLinearChar (1 : G →* kˣ))
  refine ⟨ι, hι, ns, Hs, ψs, fun i => (hElem i).isSolvable, ?_⟩
  rw [← lhs_bridge, hsum]
  exact Finset.sum_congr rfl (fun i _ => rfl)

end BrauerChallenge
