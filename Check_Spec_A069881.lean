import Spec_A069881
import A069881

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Check_Spec_A069881 : fermeture Spec↔preuve (Option B)

Le Spec (`Spec_A069881.lean`) ne contient aucune preuve ; ce
fichier vérifie que les théorèmes compilés satisfont EXACTEMENT
les trois énoncés de la spec, dans l'ordre de la conjonction
((i) Tangente, (ii) dichotomie, (iii) bonus). Les théorèmes
vivent dans le namespace `A069881` du module homonyme.
-/

/-- Les preuves compilées satisfont les énoncés record. -/
theorem proven_A069881 : SpecA069881 :=
  ⟨A069881.A069881_even, A069881.A069881_overflow,
    A069881.A069881_image_odd⟩

#print axioms proven_A069881
