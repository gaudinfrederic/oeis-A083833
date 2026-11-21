# Audit d'anteriorite 8 registres - A083830

Date : 2026-11-08. Mission E8-BATCH-3 (sous-agent le projet).
Enonce audite (verbatim OEIS, fetch live `search?q=id:A083830&fmt=text`
2026-11-08 ; miroir `(workdir interne)` absent sur cette machine) :

```
%I A083830 #9 Jul 20 2020
%N A083830 Palindromes of the form 3n + 1 where n is also a
   palindrome: palindromes arising in A083829.
%K A083830 base,nonn   %O A083830 1,1
%A A083830 _Amarnath Murthy_ and Meenakshi Srikanth, May 09 2003
```

Enonce prouve localement (`lean/A083830.lean` re-export du theoreme
`A083830_digits` du module `A083829.lean`, metadata.json) :
`A083830_alphabet` : pour tout palindrome p a `m >= 1` chiffres tel
que `q = 3p+1` est aussi palindrome (m' chiffres), aucun chiffre de q
n'est 0, 6 ou 9 - c.-a-d. chaque chiffre de q est dans
`{1,2,3,4,5,7,8}`. Propriete universelle des membres, prouvee pour
toute longueur par la chaine de retenues du module compagnon
(cas m'=m : chaine symetrique 2-periodique ; cas m'=m+1 : etat unique
forcant p = 77..7, q = 23..32). NON une enumeration : appartenance,
completude, optimalite de l'alphabet non revendiquees.

Note de fiche : l'enonce « digits of q avoid {0,6,9} » n'est PAS un
commentaire de la fiche A083830 (qui ne porte aucune conjecture) -
c'est un theoreme deduit portant sur les images `q = 3p+1` ; son
pendant source (« aucun terme ne contient 3,8,9 ») est l'assertion
P3 d'Israel sur A083829, traitee dans l'audit soeur.

## Verdicts par registre

| # | Registre | Methode | Fraicheur | Verdict |
|---|---|---|---|---|
| 1 | Fiche OEIS A083830 | fetch live `?fmt=text` (rev. #9, 20/07/2020) | live 08/11/2026 | aucune conjecture ni reference ; Mathematica Dale = calcul ; table publiee 36 termes |
| 2 | google-deepmind/formal-conjectures | grep 83830 | HEAD 2055e5a | ABSENT |
| 3 | epoch-research/LeanOpenProblems-results | `git ls-tree` | HEAD cbb7cb65 | ABSENT |
| 4 | provables/sequencelib | find + grep | HEAD dfb06c18 | ABSENT |
| 5 | Repos « OEIS resolues » | oeis-papers (63), OEIS-Settled (5920), Eppie/dvgyl/VictorLiwentao/dpreil, jonmaiga | live 08/11/2026 | ABSENT ; jonmaiga : stub `Prog/A083/A0838.lean`, `Proof/A083/` sans A083830 |
| 6 | Recherche globale `"A083830"` | GitHub code-search (474 hits), arXiv API, web | 08/11/2026 | joeis `A083830.java` (calcul), OEIS-Spider (soeurs), miroirs joeis-lite, notre hote de build externe ; reste = collisions (npm cache, OCR books, .lock) ; arXiv : 0 ; forums : 0 |
| 7 | Litterature | famille Murthy/Srikanth, alphabet des images 3p+1 | web 08/11/2026 | aucune preuve publiee localisee ; l'enonce lui-meme (alphabet des q) n'apparait pas dans la litterature consultee - theoreme deduit du projet |
| 8 | trureturing `dev` | ls-tree + grep | local 2dab9b09 | ABSENT |

## Conclusion

**OUVERT avant ce travail** : aucune preuve anterieure de
l'alphabet `{1,2,3,4,5,7,8}` pour les palindromes `q = 3p+1` n'a ete
localisee (enonce deduit, absent meme des commentaires OEIS de la
cible). Claim honnete maximal : « preuve verifiee machine de la
propriete universelle d'alphabet des membres pour toute longueur » -
jamais « premiere preuve » comme revendication de priorite. Aucune
divergence de claim dans le package (metadata : « universal digit-
alphabet property ... enumeration of the sequence not claimed »).
