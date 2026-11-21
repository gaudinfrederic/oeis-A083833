# Audit d'anteriorite E8 - A069881

Date : 2026-11-07. Mission E8 (audit 8 registres, AGENTS.md
CONFIANCE/PUBLIABLE). Re-audit complet au stade (etape interne) ;
l'audit P25 (`AUDITS.d/Prospection.md`, meme verdict) est
re-verifie ici a neuf sur miroirs locaux + sources live.

Enonce audite (verbatim OEIS, fiche live fetch 2026-11-07) :
« Numbers n such that n and 2n+1 are both palindromes. »
(offset 1,2 ; nonn,base ; Murthy 2002, ext. McCann 2002).

Resultats prouves concernes (lean/A069881.lean) :
- `A069881_even` : membre a m chiffres, m pair => p = 55...5
  (= la conjecture Tangente N 222 / « palindromes alpha+ »).
- `A069881_overflow` : dichotomie complete des membres
  (repdigit de 5 avec retenue sortante, OU longueur impaire
  a classes alternees {1..4}/>=5).
- `A069881_image_odd` : chiffres pairs de 2p+1 tous impairs.

## Verdict par registre

| # | Registre | Verdict | Preuve |
|---|----------|---------|--------|
| 1 | Fiche OEIS (commentaires/%I) | AUCUNE preuve | Live `oeis.org/A069881?fmt=text` : COMMENTS = McCann 2002 seul (« all digits = 5 (A002279) is part of this sequence ») ; LINKS = b-file Neretin 1..15636 seul ; %I = stamp revision Jan 22 2018, zero citation litterature ; CROSSREFS = subsequence of A002113 |
| 2 | google-deepmind/formal-conjectures | 0 hit | Miroir `(workdir interne)` : grep `69881`/`A069881` = 0 ; pas de `FormalConjectures/OEIS/69881.lean` (349 fichiers OEIS listes) ; live GitHub code search repo = total 0 |
| 3 | epoch-research/LeanOpenProblems-results | 0 hit | Miroir `(workdir interne)` : `git grep A069881 origin/main` = 0 ; les hits `69881` = sous-chaines de litteraux Nat (TestNat10M, Erdos952 WallData), faux positifs |
| 4 | sequencelib | 0 hit | Miroir local : 25905 .lean ; ni `Sequencelib/A069881.lean` ni `Sequencelib/AISynth/A069881.lean` ; grep contenu = 0 |
| 5 | Repos « OEIS resolues » (live, enumeration complete des arbres via git/trees API) | 0 hit partout | twentyseventhllc-lgtm/OEIS-Settled (12162 fichiers : aucun path 69881 ; LEDGER.md/STATE.md/results.json sans A069881) ; dvgyl/oeis-proofs (27 entrees A-numbered listees, aucune A069881, aucun theme palindrome) ; VictorLiwentao/lean-oeis-proofs (434 fichiers) ; pandolfonicolo/oeis-proofs (132, projets A354766/A278085 seuls) ; otoi-lab/oeis-lean-proofs (19) ; Eppie/oeis-proofs (118) ; jewoo-suh/oeis-lean (38) ; wanglu2016/oeis-notes (13) ; dpreil-ydlp/open-problems (244 + miroir local `(workdir interne)` : seuls hits = sous-chaines numeriques du b-file A185897, faux positifs) |
| 6 | Recherche globale « A069881 » | generateurs de termes seuls, 0 preuve | GitHub code search : `joeis` A069881.java (filtre palindrome(k) && palindrome(2k+1), generation de termes) ; `gfis/OEIS-prog` A069881.gp (isok PARI) ; `africamonkey/OEIS-Spider` (donnee scrapee) ; `(external CI mirror)` = NOTRE depot ; le reste = faux positifs hex/SHA/UUID (verifies un a un : CFSG litteral hex, hard-disk sha256, factoreminv/bdc hex, Sitecore commit a069881). Web : oeis.org + miroir number.house + codes produit (Elesa-Ganter, Skylon). arXiv full-text search « A069881 » : No Results. MSE + MO via API Stack Exchange officielle : 0 items chacun. Zulip/NMBRTHRY/SeqFan : aucun hit indexe |
| 7 | Litterature (proposant + « proved ») | conjecture ENONCEE, jamais prouvee | Tangente N 222 (2025) p.28, « Les palindromes alpha et leurs cousins » (Criton & Descombes, probleme.tangente-mag.com, fetch live) : les alpha+ = A069881 ; texte verbatim « On peut conjecturer que les seuls palindromes alpha+ ayant un nombre pair de chiffres sont les nombres 55, 5555, 555555... » - CONJECTURE explicite, aucune preuve publiee. 2e conjecture : pas de chaine alpha+ de long >=3. Murthy (proposant) : aucune publication liee localisee. Scholar/MSE : rien sur cette classification |
| 8 | the-omega-institute/trureturing (branche dev, Library/) | 0 hit | Miroir local sur branche `dev` : `grep A069881|A0698 Library/` = 0 fichier/contenu ; hits `69881` = fragments de SHA-256 dans .git et papiers sans rapport (Weil, GraphInvariants), faux positifs |

## Fait notable adjacent (pas un hit, honnetete)

- A069882 (n et 2n-1 palindromes, « alpha- ») : la fiche OEIS
  porte une PREUVE de Chai Wah Wu (Jul 20 2020) : tous les
  termes > 5 sont des repdigits de 6, `a(n) = 2*(10^(n-5)-1)/3`
  pour n > 5. Enonce DIFFERENT (2n-1, chaine d'emprunt) - ne
  couvre ni n'implique la classification A069881 (2n+1, chaine
  de retenue). Cite ici comme art anterieur le plus proche ;
  la page Tangente affirme aussi « On peut demontrer » pour
  alpha- sans la publier (coherent avec Wu 2020).
- b-file Neretin (15636 termes <= 10^12) + joeis/OEIS-prog :
  verification computationnelle, pas une preuve.
- Solutions Tangente derriere login (plateforme Q&A) : la
  conjecture est dans le texte d'exposition (pas dans les
  questions Q1-Q5), presentee comme ouverte.

## Conclusion claim

- Verdict global : AUCUNE preuve anterieure de la
  classification des membres de longueur paire (ni de la
  dichotomie complete, ni de image_odd) localisee dans les
  8 registres. La seule source qui l'enonce (Tangente 222)
  la pose comme conjecture ouverte.
- AUTORISE (factuel, AGENTS « on ne revendique rien ») :
  decrire le resultat - enonce, methode, certification
  kernel-pur ; mentionner la conjecture Tangente 222/8154
  comme source de l'enonce ; citer A069882-Wu comme analogue.
- INTERDIT : tout claim de priorite (« first », « premiere »,
  « jamais prouve », « open problem resolved ») dans les
  textes publies - la regle projet l'interdit quoi qu'il
  arrive ; l'evidence ci-dessus vit ici uniquement.
