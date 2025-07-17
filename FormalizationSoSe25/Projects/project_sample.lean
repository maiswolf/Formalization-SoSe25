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
#check LieIdeal

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

theorem quotient_nilradical_radical_eq_center2 : radical R (L ⧸ (nilradical R L)) = center R (L ⧸ (nilradical R L)) := by
  have center_eq_zero : (center R (L ⧸ (nilradical R L))) = ⊥ := by
    have center_nilpotent : (IsNilpotent (L ⧸ (nilradical R L)) (center R (L ⧸ (nilradical R L)))) := by
      apply trivialIsNilpotent
    apply nil_ideals_eq_zero_quotient_nilradical at center_nilpotent
    exact center_nilpotent
  have rad_eq_zero : (radical R (L ⧸ (nilradical R L))) = ⊥ := by
    unfold radical
    rw [sSup_eq_bot]
    simp
    intro h h'
    obtain⟨a⟩ := h'
    -- für g auflösbares Ideal, es existiert k sodass [g^(k), g^(k)] = 0, damit ist g^(k) nilpotent, also
    -- g^(k) = 0 (nach nil_ideals_eq_zero_quotient_nilradical). Damit ist [g^(k-1),g^(k-1)]=0
    -- per Induktion immer so weiter, dann folgt g = 0
    sorry
  rw [← center_eq_zero] at rad_eq_zero
  exact rad_eq_zero

variable (L : Type v)
variable [CommRing ℤ]
variable [LieRing L] [g : LieAlgebra ℤ L]

lemma ideal_bot_nilpotent (I : LieIdeal ℤ L) (h : ⊥=⁅I,I⁆) : IsNilpotent L I := by
  sorry


theorem radical_eq_center_if_nil_ideals_eq_zero (nil_ideals_eq_zero : ∀(I : LieIdeal ℤ L), IsNilpotent L I → I = ⊥) : radical ℤ L = center ℤ L := by
  have center_eq_zero : center ℤ L = ⊥ := by
    have center_nilpotent : (IsNilpotent L (center ℤ L)) := by
      apply trivialIsNilpotent
    apply nil_ideals_eq_zero at center_nilpotent
    exact center_nilpotent
  have rad_eq_zero : radical ℤ L = ⊥ := by
    unfold radical
    simp
    intro h h'
    obtain ⟨a⟩ := h'
    unfold LieAlgebra.derivedSeries at a
    unfold derivedSeriesOfIdeal at a
    obtain ⟨b,c⟩ := a
    have derivedSeries_step (k : ℕ) (hk : derivedSeries ℤ h (k+1) = ⊥) : derivedSeries ℤ h k = ⊥ := by
      unfold LieAlgebra.derivedSeries at hk
      unfold LieAlgebra.derivedSeries
      have succ : derivedSeriesOfIdeal ℤ h (k+1) ⊤ = ⁅derivedSeriesOfIdeal ℤ h k ⊤, derivedSeriesOfIdeal ℤ h k ⊤⁆ := by
        apply LieAlgebra.derivedSeriesOfIdeal_succ
      rw [hk] at succ
      apply ideal_bot_nilpotent at succ
      --apply nil_ideals_eq_zero at succ
      sorry
    have derivedSeries_zero : derivedSeries ℤ h 0 = ⊥ := by
      sorry
    have derived_series_seriesOfIdeal_bot : derivedSeries ℤ h 0 = ⊥ ↔ derivedSeriesOfIdeal ℤ L 0 h = ⊥ := by
      apply LieIdeal.derivedSeries_eq_bot_iff
    have zero_series_eq_bot : derivedSeriesOfIdeal ℤ L 0 h = ⊥ := by
      obtain⟨a,b⟩ := derived_series_seriesOfIdeal_bot
      apply a
      exact derivedSeries_zero
    have zero_series_eq_h : derivedSeriesOfIdeal ℤ L 0 h = h := by
      rfl
    rw [zero_series_eq_h] at zero_series_eq_bot
    exact zero_series_eq_bot

  rw [← center_eq_zero] at rad_eq_zero
  exact rad_eq_zero

variable (I : LieIdeal ℤ L)
variable (k : ℕ)
variable (w : derivedSeriesOfIdeal ℤ I k ⊤)


#moogle "For LieIdeal I, if ⁅I,I⁆ = ⊥ then I nilpotent."
#check LieSubmodule.lie_abelian_iff_lie_self_eq_bot
#check derivedSeries_le_lowerCentralSeries
#check LieAlgebra.derivedSeriesOfIdeal_succ
#check Nat.caseStrongRecOn
#check LieIdeal.derivedSeries_eq_bot_iff
#check derivedSeries_zero
#check LieIdeal.derivedSeries_eq_bot_iff
#check LieAlgebra.derivedSeries
#check LieAlgebra.abelian_of_le_center
#check LieAlgebra.nilpotent_ad_of_nilpotent_algebra
noncomputable section

/- You can now start writing definitions and theorems. -/
