-- Here is a first `import Mathlib.Tactic` to get things started.
-- Based on the definitions you need, you can add more imports right below.
import Mathlib.Tactic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Semisimple.Lemmas
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.DirectSum
-- Theoretically, you could just write `import Mathlib`, but this will be somewhat slower.

/- Remember we can open namespaces to shorten names and enable notation.

For example (feel free to change it): -/
-- open Function Set
open LieAlgebra LieModule
#check LieAlgebra
#check LieAlgebra.IsSemisimple
#check LieIdeal
#check IsLieAbelian
#check LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal
#check IsAtom
#check IsNilpotent

-- simple: irreducible, non-abelian
#check LieAlgebra.IsSimple
#print LieAlgebra.IsSimple
-- Exercise: Show that simple Lie-Algebras are semisimple

-- example {R : Type*} [CommRing R] {L : Type*} [k : LieRing L] [g : LieAlgebra R L] (h : g.IsSimple) : g.IsSemisimple := by
/-    obtain⟨a,b⟩ := h
    have simple_not_trivial : (⊤ : LieIdeal R L) ≠ ⊥ := by sorry
    constructor
    · have h1 : ∀ (I : LieIdeal R L), (I = ⊤) → (IsAtom I) := by
        intro h2 h3
        rw [h3]
        constructor
        · exact simple_not_trivial
        · intro h4 h5
          obtain⟨c,d⟩ := a h4
          rfl
          rename_i f
          rw [f] at h5
          exfalso
          exact lt_irrefl _ h5
      exact sup_eq_top_of_top_mem (h1 ⊤ rfl)
    · sorry
    · intro h1 h2 h3
      obtain⟨c,d⟩ := a h1
      rcases h2
      rename_i right
      rename_i left
      exact false_of_ne left
      rename_i top
      rw [top] at h3
      apply b
      rwa [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at h3
-/



/- Remember if many new definitions require a `noncomputable` either in the `section` or definition.

For example (feel free to change it): -/

-- Nilradical ist maximum nilpotent ideal? Something is missing
variable (R : Type u) (L : Type v)
variable [CommRing R]
variable [LieRing L] [g : LieAlgebra R L]

def LieAlgebra.nilradical  :=
  maxNilpotentIdeal R L

-- für Quotient g/nil(g) ist reduktiv (direkte Summe aus halbeinfacher und abelscher LieAlgebra)

-- g halbeinfach ist das Nilradikal {0}

-- g + h direkte summe dann ist nil(g+h) = nil(g) + nil(h)

-- wenn Nil(g) = 0 => Zentrum = rad(g)

lemma nilradical_eq_bot_of_isSemisimple  (h1 : g.IsSemisimple) : nilradical R L = ⊥ := by
  have h2 : (radical R L = ⊥) := by simp
  have h3 : (nilradical R L ≤ radical R L) := by
    · unfold LieAlgebra.nilradical
      apply maxNilpotentIdeal_le_radical
  rw [h2] at h3
  rw [le_bot_iff] at h3
  exact h3

--open DirectSum

variable {L1} [LieRing L1] [g1 : LieAlgebra R L1]
variable {L2} [LieRing L2] [g2 : LieAlgebra R L2]
variable [LieRing (L1 × L2)] [g12: LieAlgebra R (L1 × L2)]

-- variable (L : ι → Type w)
-- variable [∀ i, LieRing (L i)] [∀ i, LieAlgebra R (L i)]

#check LieAlgebra R L1

--def nilradical_of_direct_sum :=
 -- nilradical R (⨁ i, L i)


-- zeige nil(g) + nil(h) = nil(g+h)

#check nilradical R L1

#check LieSubmodule.Quotient.lieQuotientLieAlgebra
#check LieAlgebra R (L ⧸ (nilradical R L))
#check radical

--lemma a : nilradical R (⨁ i, L i) = (⨁ i, nilradical R (L i)) := by
--  sorry

lemma b : (nilradical R (L1 × L2)) = ((nilradical R L1) × (nilradical R L2 )) := by
  sorry

-- all nilpotent ideals in g/nil(g) are 0
lemma nil_ideals_eq_zero_quotient_nilradical (I : LieIdeal R (L ⧸ (nilradical R L))) (h : IsNilpotent (L ⧸ (nilradical R L)) I) : I = ⊥ := by
  sorry

-- für g/Nil(g) gilt Rad(g) = Z(g)

theorem quotient_nilradical_radical_eq_center : radical R (L ⧸ (nilradical R L)) = center R (L ⧸ (nilradical R L)) := by
  have h1 : (center R (L ⧸ (nilradical R L)) ≤ radical R (L ⧸ (nilradical R L))) := by
    apply center_le_radical
  have h2 : (radical R (L ⧸ (nilradical R L)) ≤ center R (L ⧸ (nilradical R L))) := by
    sorry
  exact le_antisymm h2 h1

#check LieAlgebra.abelian_of_le_center
#check LieAlgebra.nilpotent_ad_of_nilpotent_algebra
noncomputable section

/- You can now start writing definitions and theorems. -/
