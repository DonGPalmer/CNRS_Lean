import CNRSArithmetic.MSDMinusOneDiskGrowth
import CNRSArithmetic.MSDMinusOneCertificate
import Mathlib.Tactic

/-!
# CNRS P4: no finite MSD remainder invariant for divisor -1, delay zero

Combines the independently compiled radius-eight ranked-deletion certificate
and the exact external-disk strict-growth inequality. No finite invariant
set of Gaussian remainders containing the origin is possible for the
canonical five-digit input/output recurrence at divisor -1.

This is an exact *global finite-invariant-set* obstruction at delay zero.
Converting arbitrary correct online algorithms to finite invariant remainder
sets, handling positive delay, and the general non-power-divisor conjecture
are outside this module.
-/

namespace CNRSArithmetic

/-- Any finite nonempty set of Gaussian remainders that is closed under
some output digit for each incoming digit must lie inside radius eight:
otherwise a maximal squared-norm state outside the disk has an even larger
successor, a contradiction. -/
theorem minusOne_finite_invariant_inside_disk
    (S : Finset GaussianRemainder)
    (hinv : ∀ r ∈ S, ∀ a : Fin 5,
      ∃ d : Fin 5, msdDivisionStep (-1, 0) r a d ∈ S) :
    ∀ r ∈ S, msdNormSq r ≤ 64 := by
  by_contra hh
  push_neg at hh
  obtain ⟨r0, hr0, houtside⟩ := hh
  let values : Finset ℤ := S.image msdNormSq
  have hvalues : values.Nonempty := by
    refine ⟨msdNormSq r0, ?_⟩
    exact Finset.mem_image.mpr ⟨r0, hr0, rfl⟩
  have hmaxmem : values.max' hvalues ∈ values :=
    Finset.max'_mem values hvalues
  obtain ⟨rmax, hrmax, hident⟩ := Finset.mem_image.mp hmaxmem
  have hmax (r : GaussianRemainder) (hr : r ∈ S) :
      msdNormSq r ≤ values.max' hvalues :=
    Finset.le_max' values _ (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  have hmaxoutside : (64 : ℤ) < msdNormSq rmax := by
    have hb := hmax r0 hr0
    omega
  obtain ⟨d, hchild⟩ := hinv rmax hrmax (0 : Fin 5)
  have hgrowth :=
    minusOne_outside_disk_strict_growth rmax (0 : Fin 5) d hmaxoutside
  have hbounded := hmax (msdDivisionStep (-1, 0) rmax (0 : Fin 5) d) hchild
  omega

/-- The concrete disk certificate plus outward growth yields a genuine global
finite-state obstruction: no finite set of remainder states containing 0
has a total transition choice for every incoming digit. -/
theorem minusOne_no_finite_invariant
    (S : Finset GaussianRemainder)
    (hzero : (0, 0) ∈ S)
    (hinv : ∀ r ∈ S, ∀ a : Fin 5,
      ∃ d : Fin 5, msdDivisionStep (-1, 0) r a d ∈ S) :
    False := by
  have hbound := minusOne_finite_invariant_inside_disk S hinv
  let allowed : GaussianRemainder → Prop := fun r => r ∈ S
  let eliminated : GaussianRemainder → Prop :=
    fun r => minusOneDeleted r ∧ r ∈ S
  have hz : eliminated (0, 0) := ⟨minusOne_origin_deleted, hzero⟩
  have hsub : ∀ r, eliminated r → allowed r := by
    intro r hr
    exact hr.2
  have hdesc : ∀ r, eliminated r →
        ∀ d : Fin 5,
          allowed (msdDivisionStep (-1, 0) r (minusOneAdversary r) d) →
            eliminated (msdDivisionStep (-1, 0) r (minusOneAdversary r) d) ∧
              minusOneRank (msdDivisionStep (-1, 0) r (minusOneAdversary r) d) <
                minusOneRank r := by
    intro r hr d hd
    have hinside :
        minusOneInside (msdDivisionStep (-1, 0) r (minusOneAdversary r) d) := by
      exact hbound _ hd
    obtain ⟨hdelete, hrank⟩ :=
      minusOne_all_deleted_transitions r hr.1 d hinside
    exact ⟨⟨hdelete, hd⟩, hrank⟩
  have hpolicy :
      HasOnlineRemainderPolicy allowed (msdDivisionStep (-1, 0)) := by
    intro r hr a
    exact hinv r hr a
  exact (msdDeletionCertificate_noPolicy (-1, 0) allowed eliminated
    minusOneRank minusOneAdversary hz hsub hdesc) hpolicy

end CNRSArithmetic
