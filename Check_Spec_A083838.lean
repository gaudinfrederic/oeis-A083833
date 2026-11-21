import A083833
import A083838
import Spec_A083838

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083838 - fermeture du Spec image

`proven_A083838` scelle les 21 zéros de la suite image : pour chaque
`k` du zéro-ensemble, `A083838_<k>_zero` certifie l'inexistence
universelle d'un couple `(p, q)` palindromique avec `q = k·p+1`.
-/

open A083833
open A083838

/-- Fermeture : les zéros affichés de A083838 sont des inexistences
universelles (héritées de l'obstruction de bord de A083837). -/
theorem proven_A083838 : SpecA083838 := by
  intro k hk
  fin_cases hk
  · exact A083838_12_zero
  · exact A083838_17_zero
  · exact A083838_23_zero
  · exact A083838_31_zero
  · exact A083838_37_zero
  · exact A083838_41_zero
  · exact A083838_42_zero
  · exact A083838_48_zero
  · exact A083838_51_zero
  · exact A083838_53_zero
  · exact A083838_61_zero
  · exact A083838_64_zero
  · exact A083838_71_zero
  · exact A083838_74_zero
  · exact A083838_79_zero
  · exact A083838_81_zero
  · exact A083838_86_zero
  · exact A083838_91_zero
  · exact A083838_96_zero
  · exact A083838_101_zero
  · exact A083838_103_zero

#print axioms proven_A083838
