import A083833
import A083837
import Spec_A083837

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083837 - fermeture du Spec

`proven_A083837` scelle les 21 zéros affichés : pour chaque `k` du
zéro-ensemble, `A083837_<k>_zero` certifie l'inexistence universelle
d'un palindrome `p` avec `k·p+1` palindrome.
-/

open A083833
open A083837

/-- Fermeture : les 21 zéros affichés de A083837 sont des inexistences
universelles, certifiées par obstruction de bord (profondeurs 1, 2, 3). -/
theorem proven_A083837 : SpecA083837 := by
  intro k hk
  fin_cases hk
  · exact A083837_12_zero
  · exact A083837_17_zero
  · exact A083837_23_zero
  · exact A083837_31_zero
  · exact A083837_37_zero
  · exact A083837_41_zero
  · exact A083837_42_zero
  · exact A083837_48_zero
  · exact A083837_51_zero
  · exact A083837_53_zero
  · exact A083837_61_zero
  · exact A083837_64_zero
  · exact A083837_71_zero
  · exact A083837_74_zero
  · exact A083837_79_zero
  · exact A083837_81_zero
  · exact A083837_86_zero
  · exact A083837_91_zero
  · exact A083837_96_zero
  · exact A083837_101_zero
  · exact A083837_103_zero

#print axioms proven_A083837
