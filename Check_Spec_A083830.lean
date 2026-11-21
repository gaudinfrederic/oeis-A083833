import Spec_A083830
import A083829

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A083830 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A083830.lean`) ne contient aucune preuve ; ce
fichier vérifie que le théorème compilé satisfait EXACTEMENT
l'énoncé de la spec. Le théorème vit dans le namespace
`A083829` du module homonyme (théorème compagnon
`A083830_digits`).
-/

/-- La preuve compilée satisfait l'énoncé record. -/
theorem proven_A083830 : SpecA083830 := A083829.A083830_digits

#print axioms proven_A083830
