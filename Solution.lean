import Mathlib
import BrauerInduction.Main

/-!
Solution to `Challenge.lean`.

The pure-Mathlib, trivial-representation / solvable-subgroup corollary of Brauer induction,
proved directly from the project's elementary theorem
`BrauerInduction.character_eq_sum_induced_linear` (the elementary form of the challenge is
kept, for reference, in `OldChallenge.lean`).

The proof:
* specializes the elementary theorem to the trivial one-dimensional representation
  `FDRep.ofLinearChar 1`;
* weakens each subgroup's `IsBrauerElementary` to `IsSolvable`
  (Brauer-elementary ⇒ nilpotent ⇒ solvable);
* rewrites both sides of the equation into Mathlib's unbundled `Representation` vocabulary.
-/

open scoped BigOperators

universe u

namespace BrauerChallenge

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
    BrauerInduction.character_eq_sum_induced_linear (FDRep.ofLinearChar (1 : G →* kˣ))
  refine ⟨ι, hι, ns, Hs, ψs, ?_, ?_⟩
  · -- each `Hs i` is solvable: Brauer-elementary ⇒ nilpotent ⇒ solvable
    intro i
    haveI := (hElem i).isNilpotent
    infer_instance
  · -- rewrite both sides into Mathlib's `Representation` vocabulary
    have lhs :
        (FDRep.ofLinearChar (1 : G →* kˣ)).character
          = (1 : Representation k G k).character := by
      have hρ : (FDRep.ofLinearChar (1 : G →* kˣ)).ρ = (1 : Representation k G k) := by
        apply MonoidHom.ext; intro g; apply LinearMap.ext; intro x
        change (FDRep.ofLinearChar (1 : G →* kˣ)).ρ g x = (1 : G →* Module.End k k) g x
        simp [Module.End.one_apply]
      exact congrArg Representation.character hρ
    rw [← lhs, hsum]
    exact Finset.sum_congr rfl (fun i _ => rfl)

end BrauerChallenge
