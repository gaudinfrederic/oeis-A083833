import Spec_A083832
import A083832

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083832 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A083832.lean`) ne contient aucune preuve ; ce
fichier vérifie que le théorème compilé `A083832_alphabet`
satisfait EXACTEMENT l'énoncé de la spec. Le théorème vit à la
racine du module `A083832` (le fichier ne déclare aucun
`namespace` propre ; `IsPal`/`dgt` viennent de `A083831`).
-/

/-- La preuve compilée satisfait l'énoncé record. -/
theorem proven_A083832 : SpecA083832 := A083832_alphabet

#print axioms proven_A083832
