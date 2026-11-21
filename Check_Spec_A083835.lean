import Spec_A083835
import A083835

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083835 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A083835.lean`) ne contient aucune preuve ; ce
fichier vérifie que le théorème compilé `A083835.A083835`
satisfait EXACTEMENT l'énoncé record de la spec (classification
bidirectionnelle complète).
-/

/-- La preuve compilée satisfait l'énoncé record. -/
theorem proven_A083835 : SpecA083835 := A083835.A083835

#print axioms proven_A083835
