# Audit d'anteriorite 8 registres - A083831

Date : 2026-11-08. Mission E8-BATCH-3 (sous-agent le projet).
Enonce audite (verbatim OEIS, fetch live `search?q=id:A083831&fmt=text`
2026-11-08 ; miroir `(workdir interne)` absent sur cette machine) :

```
%I A083831 #21 Apr 04 2018
%N A083831 Palindromes n such that 4n + 1 is also a palindrome.
%C A083831 Among infinite subsequences are the repdigits
   8...8 = 8*(10^k-1)/9. It appears that the only terms with an even
   number of digits are these for even k. - _Robert Israel_,
   Apr 04 2018
%K A083831 base,nonn   %O A083831 1,2
%A A083831 _Amarnath Murthy_ and Meenakshi Srikanth, May 09 2003
```

Enonces prouves localement (`lean/A083831.lean`, metadata.json) :
`A083831_even` : si p est un palindrome a m chiffres (m pair) tel que
`q = 4p+1` est palindrome, alors tout chiffre de p vaut 8 - direction
unicite de la conjecture « It appears » d'Israel (les seuls termes de
longueur paire sont les repdigits `8^d`, d pair), prouvee pour toute
longueur. Bonus `A083831_digits` : chaque chiffre de p est `<= 4` ou
`= 8`, coherent avec les termes publies. Methode : chaine de
retenues `c_j = (4·(p mod 10^j)+1)/10^j` (`c_0 = 1`, `c_j <= 3`) ;
cas m'=m (chaine symetrique 2-periodique) vs m'=m+1 (chaine
constante 3 forcant p = 88..8). Proprietes universelles ; NON une
enumeration : appartenance, completude, existence de membres
repdigits, infinitude non revendiquees. Le module prouve aussi
`A083832_digits` (soeur, package A083832).

## Verdicts par registre

| # | Registre | Methode | Fraicheur | Verdict |
|---|---|---|---|---|
| 1 | Fiche OEIS A083831 | fetch live `?fmt=text` (rev. #21, 04/04/2018) | live 08/11/2026 | conjecture d'Israel affichee « It appears » - aucune preuve referencee ; b-file Israel n=1..1000 ; Maple Israel + Mathematica Dale + PARI Marcus = generation/filtrage |
| 2 | google-deepmind/formal-conjectures | grep 83831 | HEAD 2055e5a | ABSENT |
| 3 | epoch-research/LeanOpenProblems-results | `git ls-tree` | HEAD cbb7cb65 | ABSENT |
| 4 | provables/sequencelib | find + grep | HEAD dfb06c18 | ABSENT |
| 5 | Repos « OEIS resolues » | oeis-papers (63), OEIS-Settled (5920), Eppie/dvgyl/VictorLiwentao/dpreil, jonmaiga | live 08/11/2026 | ABSENT ; jonmaiga : stub `Prog/A083/A0838.lean`, `Proof/A083/` sans A083831 |
| 6 | Recherche globale `"A083831"` | GitHub code-search (498 hits), arXiv API, web | 08/11/2026 | joeis `A083831.java` + `A083832.java` (calcul), gfis/OEIS-prog `prog/gp/a083/A083831.gp` (PARI, calcul), OEIS-Spider, notre hote de build externe ; reste = collisions ; arXiv : 0 ; forums : 0 |
| 7 | Litterature | « palindrome 4n+1 repdigit » | web 08/11/2026 | aucune preuve publiee de la conjecture d'Israel localisee ; famille 2003 = commentaires observatoires sans preuves |
| 8 | trureturing `dev` | ls-tree + grep | local 2dab9b09 | ABSENT |

## Conclusion

**OUVERT avant ce travail** : aucune preuve anterieure de la
conjecture d'Israel (direction unicite : membre de longueur paire =>
repdigit `88..8`) localisee dans les 8 registres ; la fiche l'affiche
toujours « It appears ». Claim honnete maximal : « preuve verifiee
machine de la direction unicite pour toute longueur + alphabet
`{0,1,2,3,4,8}` des membres » - jamais « premiere preuve » comme
revendication de priorite ; la reciproque (existence des repdigits
membres) et la completude restent non revendiquees. Aucune divergence
de claim dans le package (metadata : « uniqueness direction ...
proved for all digit lengths ... not an enumeration »).
